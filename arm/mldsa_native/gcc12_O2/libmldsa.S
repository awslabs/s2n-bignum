// Copyright (c) The mldsa-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// The code and read-only data of mldsa-native's libmldsa.so (gcc 12, -O2)
//
// This is a transcription of the binary
// binaries/multilevel/gcc12/O2/libmldsa.so from the binary branch of
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

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mldsa_native_libmldsa_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mldsa_native_libmldsa_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mldsa_native_libmldsa_gcc12_O2):

// ELF header and dynamic linking information (0x0 to 0xe30)

        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x0000000100b70003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x0000000000030670
        .quad   0x0038004000000000
        .quad   0x0019001a00400005
        .quad   0x0000000500000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000000000d5a4
        .quad   0x000000000000d5a4
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
        .quad   0x0000001000000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000100000002b
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000100000005b
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000013
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000024
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x00080012000001ae
        .quad   0x0000000000006aa0
        .quad   0x00000000000002a0
        .quad   0x00080012000001f2
        .quad   0x00000000000072e0
        .quad   0x00000000000000a8
        .quad   0x00080012000000f0
        .quad   0x0000000000004dc0
        .quad   0x000000000000010c
        .quad   0x0008001200000082
        .quad   0x00000000000046f0
        .quad   0x00000000000000a8
        .quad   0x00080012000003f1
        .quad   0x000000000000a8d0
        .quad   0x00000000000000d0
        .quad   0x0008001200000067
        .quad   0x00000000000041f0
        .quad   0x0000000000000500
        .quad   0x000800120000037a
        .quad   0x000000000000a0b0
        .quad   0x000000000000048c
        .quad   0x0008001200000439
        .quad   0x000000000000aa60
        .quad   0x00000000000000bc
        .quad   0x0008001200000347
        .quad   0x0000000000009af0
        .quad   0x0000000000000508
        .quad   0x000800120000020a
        .quad   0x0000000000007390
        .quad   0x00000000000004b4
        .quad   0x00080012000002a5
        .quad   0x0000000000007ca0
        .quad   0x00000000000000bc
        .quad   0x000800120000031e
        .quad   0x0000000000009740
        .quad   0x000000000000031c
        .quad   0x00080012000002ea
        .quad   0x0000000000007e20
        .quad   0x00000000000000ac
        .quad   0x0008001200000272
        .quad   0x0000000000007b10
        .quad   0x00000000000000bc
        .quad   0x000800120000004b
        .quad   0x0000000000004160
        .quad   0x0000000000000088
        .quad   0x0008001200000111
        .quad   0x0000000000004f90
        .quad   0x00000000000000d0
        .quad   0x0008001200000415
        .quad   0x000000000000a9a0
        .quad   0x00000000000000bc
        .quad   0x0008001200000392
        .quad   0x000000000000a540
        .quad   0x0000000000000018
        .quad   0x00080012000000b2
        .quad   0x0000000000004c00
        .quad   0x0000000000000018
        .quad   0x0008001200000102
        .quad   0x0000000000004ed0
        .quad   0x00000000000000bc
        .quad   0x00080012000001d7
        .quad   0x0000000000006dd0
        .quad   0x0000000000000510
        .quad   0x0008001200000159
        .quad   0x0000000000005120
        .quad   0x00000000000000bc
        .quad   0x00080012000003e2
        .quad   0x000000000000a810
        .quad   0x00000000000000bc
        .quad   0x00080012000003d0
        .quad   0x000000000000a700
        .quad   0x000000000000010c
        .quad   0x000800120000047b
        .quad   0x000000000000abd0
        .quad   0x0000000000000320
        .quad   0x000800120000019b
        .quad   0x0000000000005290
        .quad   0x0000000000000320
        .quad   0x00080012000000c7
        .quad   0x0000000000004c20
        .quad   0x000000000000019c
        .quad   0x0008001200000260
        .quad   0x0000000000007a00
        .quad   0x000000000000010c
        .quad   0x0008001200000237
        .quad   0x0000000000007860
        .quad   0x000000000000019c
        .quad   0x0008001200000032
        .quad   0x0000000000003f10
        .quad   0x0000000000000248
        .quad   0x00080012000003a7
        .quad   0x000000000000a560
        .quad   0x000000000000019c
        .quad   0x0008001200000135
        .quad   0x0000000000005060
        .quad   0x00000000000000bc
        .quad   0x0008001200000337
        .quad   0x0000000000009a60
        .quad   0x0000000000000088
        .quad   0x000800120000045a
        .quad   0x000000000000ab20
        .quad   0x00000000000000ac
        .quad   0x0008001200000222
        .quad   0x0000000000007844
        .quad   0x0000000000000018
        .quad   0x00080012000002c9
        .quad   0x0000000000007d60
        .quad   0x00000000000000bc
        .quad   0x00080012000001c7
        .quad   0x0000000000006d40
        .quad   0x0000000000000088
        .quad   0x0008001200000281
        .quad   0x0000000000007bd0
        .quad   0x00000000000000d0
        .quad   0x000800120000030b
        .quad   0x0000000000007ed0
        .quad   0x0000000000000328
        .quad   0x0008001200000362
        .quad   0x000000000000a000
        .quad   0x00000000000000a8
        .quad   0x000800120000009a
        .quad   0x00000000000047a0
        .quad   0x0000000000000458
        .quad   0x000800120000017a
        .quad   0x00000000000051e0
        .quad   0x00000000000000ac
        .quad   0x6b636174735f5f00
        .quad   0x6175675f6b68635f
        .quad   0x6174735f5f006472
        .quad   0x665f6b68635f6b63
        .quad   0x736d656d006c6961
        .quad   0x70636d656d007465
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

// The procedure linkage table and the code (0xe30 to 0xaef0)
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

// mldsa_shake128_init (0x28 bytes)
L0e90:
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
L0ec0:
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
        b.hi    L0f20
L0ef0:
        mov     x1, x20
        mov     x0, x22
        bl      L1710
        sub     x19, x19, x21
        mov     x0, x22
        add     x20, x20, x21
        bl      L1850
        mov     x21, #0xa8
        mov     w2, #0x0
        mov     w3, #0xa8
        cmp     x19, #0xa7
        b.hi    L0ef0
L0f20:
        mov     x1, x20
        mov     w3, w19
        mov     x0, x22
        str     w2, [sp, #60]
        bl      L1710
        ldr     w2, [sp, #60]
        ldr     x30, [sp, #32]
        add     w2, w2, w19
        str     w2, [x22, #200]
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        ret

// mldsa_shake128_finalize (0x80 bytes)
L0f50:
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
        bl      L1710
        mov     x0, x19
        add     x1, sp, #0x16
        mov     w2, #0xa7
        mov     w3, #0x1
        bl      L1710
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     w1, #0xa8
        str     w1, [x19, #200]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L0fcc
        ldp     x19, x30, [sp], #32
        ret
L0fcc:
        bl      L0e70

// mldsa_shake128_squeeze (0xb0 bytes)
L0fd0:
        stp     x19, x20, [sp, #-64]!
        stp     x21, x22, [sp, #16]
        ldr     w21, [x2, #200]
        stp     x23, x24, [sp, #32]
        mov     x23, x2
        str     x30, [sp, #56]
        cbz     x1, L1068
        mov     x19, x1
        mov     x22, #0x0
        mov     w24, #0xa8
        str     x25, [sp, #48]
        mov     x25, x0
        b       L1044
L1004:
        sub     w3, w24, w21
        sub     w20, w24, w21
        mov     w4, w21
L1010:
        add     x1, x25, x22
        mov     w2, w4
        mov     x0, x23
        mov     w21, #0xa8
        cmp     x20, x19
        b.ls    L1034
        add     w21, w4, w19
        mov     w3, w19
        mov     x20, x19
L1034:
        bl      L16e0
        add     x22, x22, x20
        subs    x19, x19, x20
        b.eq    L1064
L1044:
        cmp     w21, #0xa8
        b.ne    L1004
        mov     x0, x23
        bl      L1850
        mov     w3, w21
        mov     x20, #0xa8
        mov     w4, #0x0
        b       L1010
L1064:
        ldr     x25, [sp, #48]
L1068:
        ldr     x30, [sp, #56]
        str     w21, [x23, #200]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x19, x20, [sp], #64
        ret

// mldsa_shake128_release (0x24 bytes)
L1080:
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
L10a4:
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
L10d0:
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
        b.hi    L1130
L1100:
        mov     x1, x20
        mov     x0, x22
        bl      L1710
        sub     x19, x19, x21
        mov     x0, x22
        add     x20, x20, x21
        bl      L1850
        mov     x21, #0x88
        mov     w2, #0x0
        mov     w3, #0x88
        cmp     x19, #0x87
        b.hi    L1100
L1130:
        mov     x1, x20
        mov     w3, w19
        mov     x0, x22
        str     w2, [sp, #60]
        bl      L1710
        ldr     w2, [sp, #60]
        ldr     x30, [sp, #32]
        add     w2, w2, w19
        str     w2, [x22, #200]
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        ret

// mldsa_shake256_finalize (0x80 bytes)
L1160:
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
        bl      L1710
        mov     x0, x19
        add     x1, sp, #0x16
        mov     w2, #0x87
        mov     w3, #0x1
        bl      L1710
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     w1, #0x88
        str     w1, [x19, #200]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L11dc
        ldp     x19, x30, [sp], #32
        ret
L11dc:
        bl      L0e70

// mldsa_shake256_squeeze (0xb0 bytes)
L11e0:
        stp     x19, x20, [sp, #-64]!
        stp     x21, x22, [sp, #16]
        ldr     w21, [x2, #200]
        stp     x23, x24, [sp, #32]
        mov     x23, x2
        str     x30, [sp, #56]
        cbz     x1, L1278
        mov     x19, x1
        mov     x22, #0x0
        mov     w24, #0x88
        str     x25, [sp, #48]
        mov     x25, x0
        b       L1254
L1214:
        sub     w3, w24, w21
        sub     w20, w24, w21
        mov     w4, w21
L1220:
        add     x1, x25, x22
        mov     w2, w4
        mov     x0, x23
        mov     w21, #0x88
        cmp     x20, x19
        b.ls    L1244
        add     w21, w4, w19
        mov     w3, w19
        mov     x20, x19
L1244:
        bl      L16e0
        add     x22, x22, x20
        subs    x19, x19, x20
        b.eq    L1274
L1254:
        cmp     w21, #0x88
        b.ne    L1214
        mov     x0, x23
        bl      L1850
        mov     w3, w21
        mov     x20, #0x88
        mov     w4, #0x0
        b       L1220
L1274:
        ldr     x25, [sp, #48]
L1278:
        ldr     x30, [sp, #56]
        str     w21, [x23, #200]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x19, x20, [sp], #64
        ret

// mldsa_shake256_release (0x24 bytes)
L1290:
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
L12b4:
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
        bl      L10a4
        mov     x2, x23
        mov     x1, x22
        mov     x0, x19
        bl      L10d0
        mov     x0, x19
        bl      L1160
        mov     x2, x19
        mov     x1, x21
        mov     x0, x20
        bl      L11e0
        mov     x0, x19
        bl      L1290
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #264]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L134c
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #272
        ret
L134c:
        bl      L0e70

// mld_keccak_absorb_once_x4.constprop.0 (0x16c bytes)
L1350:
        stp     x19, x20, [sp, #-96]!
        mov     w19, w1
        mov     x20, x6
        .inst   0xd00000e7  // adrp x7, 0x1f000
        ldr     x7, [x7, #4088]
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        stp     x23, x24, [sp, #32]
        mov     x22, x3
        mov     x24, x0
        stp     x25, x26, [sp, #48]
        mov     x23, x4
        mov     x25, x19
        stp     x27, x30, [sp, #64]
        mov     x26, x5
        ldr     x1, [x7]
        str     x1, [sp, #88]
        mov     x1, #0x0
        mov     w1, #0x1f
        strb    w1, [sp, #87]
        cmp     x19, x6
        b.hi    L13ec
L13a8:
        mov     x4, x26
        mov     x3, x23
        mov     x2, x22
        mov     x1, x21
        mov     w6, w25
        mov     w5, #0x0
        mov     x0, x24
        bl      L17d0
        mov     x0, x24
        sub     x20, x20, x19
        bl      L1e20
        add     x26, x26, x19
        add     x23, x23, x19
        add     x22, x22, x19
        add     x21, x21, x19
        cmp     x20, x19
        b.cs    L13a8
L13ec:
        sub     w25, w25, #0x1
        mov     w27, w20
        cbnz    x20, L1478
L13f8:
        add     x19, sp, #0x57
        mov     w5, w27
        mov     x4, x19
        mov     x0, x24
        mov     x3, x19
        mov     x2, x19
        mov     x1, x19
        mov     w6, #0x1
        bl      L17d0
        mov     w5, w25
        mov     x0, x24
        mov     x4, x19
        mov     w7, #0xffffff80
L142c:
        mov     x2, x4
        mov     x1, x4
        mov     x3, x4
        mov     w6, #0x1
        strb    w7, [sp, #87]
        bl      L17d0
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L14b8
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #96
        ret
L1478:
        mov     x4, x26
        mov     x3, x23
        mov     x2, x22
        mov     x1, x21
        mov     w6, w20
        mov     x0, x24
        mov     w5, #0x0
        bl      L17d0
        cmp     x20, w25, uxtw
        b.ne    L13f8
        ldrb    w7, [sp, #87]
        add     x4, sp, #0x57
        mov     w5, w20
        mov     x0, x24
        orr     w7, w7, #0xffffff80
        b       L142c
L14b8:
        bl      L0e70
        nop

// mldsa_shake128x4_absorb_once (0x64 bytes)
L14c0:
        stp     x19, x20, [sp, #-64]!
        mov     x20, x1
        mov     x19, x0
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
        b       L1350

// mldsa_shake128x4_squeezeblocks (0x84 bytes)
L1524:
        cbz     x4, L15a4
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
L1550:
        mov     x0, x24
        bl      L1e20
        mov     x4, x19
        mov     x3, x20
        mov     x2, x21
        mov     x1, x22
        mov     x0, x24
        mov     w6, #0xa8
        mov     w5, #0x0
        bl      L1750
        add     x19, x19, #0xa8
        add     x20, x20, #0xa8
        add     x21, x21, #0xa8
        add     x22, x22, #0xa8
        subs    x23, x23, #0x1
        b.ne    L1550
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L15a4:
        ret
        nop
        nop

// mldsa_shake128x4_init (0x4 bytes)
L15b0:
        ret

// mldsa_shake128x4_release (0x1c bytes)
L15b4:
        stp     x19, x30, [sp, #-16]!
        mov     x2, #0x320
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e80
        ldp     x19, x30, [sp], #16
        ret

// mldsa_shake256x4_absorb_once (0x64 bytes)
L15d0:
        stp     x19, x20, [sp, #-64]!
        mov     x20, x1
        mov     x19, x0
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
        b       L1350

// mldsa_shake256x4_squeezeblocks (0x84 bytes)
L1634:
        cbz     x4, L16b4
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
L1660:
        mov     x0, x24
        bl      L1e20
        mov     x4, x19
        mov     x3, x20
        mov     x2, x21
        mov     x1, x22
        mov     x0, x24
        mov     w6, #0x88
        mov     w5, #0x0
        bl      L1750
        add     x19, x19, #0x88
        add     x20, x20, #0x88
        add     x21, x21, #0x88
        add     x22, x22, #0x88
        subs    x23, x23, #0x1
        b.ne    L1660
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L16b4:
        ret
        nop
        nop

// mldsa_shake256x4_init (0x4 bytes)
L16c0:
        ret

// mldsa_shake256x4_release (0x1c bytes)
L16c4:
        stp     x19, x30, [sp, #-16]!
        mov     x2, #0x320
        mov     x19, x0
        mov     w1, #0x0
        bl      L0e80
        ldp     x19, x30, [sp], #16
        ret

// mldsa_keccakf1600_extract_bytes (0x30 bytes)
L16e0:
        mov     w2, w2
        cbz     w3, L170c
        mov     w3, w3
        add     x4, x0, x2
        mov     x0, #0x0
        nop
L16f8:
        ldrb    w2, [x4, x0]
        strb    w2, [x1, x0]
        add     x0, x0, #0x1
        cmp     x3, x0
        b.ne    L16f8
L170c:
        ret

// mldsa_keccakf1600_xor_bytes (0x38 bytes)
L1710:
        mov     w2, w2
        cbz     w3, L1744
        mov     w5, w3
        add     x3, x0, x2
        mov     x0, #0x0
        nop
L1728:
        ldrb    w2, [x3, x0]
        ldrb    w4, [x1, x0]
        eor     w2, w2, w4
        strb    w2, [x3, x0]
        add     x0, x0, #0x1
        cmp     x5, x0
        b.ne    L1728
L1744:
        ret
        nop
        nop

// mldsa_keccakf1600x4_extract_bytes (0x80 bytes)
L1750:
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
        bl      L16e0
        mov     w3, w20
        mov     w2, w19
        mov     x1, x24
        add     x0, x21, #0xc8
        bl      L16e0
        mov     w3, w20
        mov     w2, w19
        mov     x1, x23
        add     x0, x21, #0x190
        bl      L16e0
        ldp     x23, x24, [sp, #32]
        mov     w3, w20
        ldr     x30, [sp, #48]
        mov     w2, w19
        mov     x1, x22
        add     x0, x21, #0x258
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        b       L16e0

// mldsa_keccakf1600x4_xor_bytes (0x80 bytes)
L17d0:
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
        bl      L1710
        mov     w3, w20
        mov     w2, w19
        mov     x1, x24
        add     x0, x21, #0xc8
        bl      L1710
        mov     w3, w20
        mov     w2, w19
        mov     x1, x23
        add     x0, x21, #0x190
        bl      L1710
        ldp     x23, x24, [sp, #32]
        mov     w3, w20
        ldr     x30, [sp, #48]
        mov     w2, w19
        mov     x1, x22
        add     x0, x21, #0x258
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        b       L1710

// mldsa_keccakf1600_permute (0x5d0 bytes)
L1850:
        stp     x19, x20, [sp, #-192]!
        .inst   0xb0000041  // adrp x1, 0xa000
        add     x1, x1, #0xef0
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
L1900:
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
        b.ne    L1900
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
L1e20:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L1850
        add     x0, x19, #0xc8
        bl      L1850
        add     x0, x19, #0x190
        bl      L1850
        add     x0, x19, #0x258
        ldp     x19, x30, [sp], #16
        b       L1850
        nop
        nop

// mldsa44_unpack_pk_t1 (0x14 bytes)
L1e50:
        add     w2, w2, w2, lsl #2
        lsl     w2, w2, #6
        add     x2, x2, #0x20
        add     x1, x1, x2
        b       L28c0

// mldsa44_pack_sk_rho_key_tr (0x28 bytes)
L1e64:
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

// mldsa44_unpack_sk (0xb0 bytes)
L1e90:
        stp     x19, x20, [sp, #-64]!
        add     x7, x6, #0x40
        mov     x20, x3
        stp     x21, x22, [sp, #16]
        mov     x21, x6
        mov     x6, x1
        stp     x23, x24, [sp, #32]
        add     x1, x21, #0x80
        mov     x23, x5
        stp     x25, x30, [sp, #48]
        mov     x24, x4
        mov     x22, x3
        ldp     q0, q1, [x21]
        add     x19, x21, #0x380
        add     x25, x21, #0xa00
        stp     q0, q1, [x0]
        mov     x0, x4
        ldp     q0, q1, [x21, #32]
        stp     q0, q1, [x2]
        ldp     q0, q1, [x7]
        stp     q0, q1, [x6]
        ldp     q0, q1, [x7, #32]
        stp     q0, q1, [x6, #32]
        bl      L3a34
        mov     x0, x24
        bl      L37f0
        add     x1, x21, #0x200
        mov     x0, x23
        bl      L3ab0
        mov     x0, x23
        bl      L3920
L1f0c:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x1a0
        bl      L2a60
        add     x20, x20, #0x400
        cmp     x19, x25
        b.ne    L1f0c
        ldp     x23, x24, [sp, #32]
        mov     x0, x22
        ldp     x21, x22, [sp, #16]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        b       L3920

// mldsa44_pack_sig_c (0xc bytes)
L1f40:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ret
        nop

// mldsa44_pack_sig_h (0xf8 bytes)
L1f50:
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
L1fb0:
        mov     x1, x28
        mov     x0, x20
        bl      L2c84
        mov     x4, #0x0
        b       L1fdc
L1fc4:
        cmp     w7, #0x0
        ccmp    w5, w27, #0x0, ne
        b.eq    L1ff0
        add     x4, x4, #0x1
        cmp     x4, #0x100
        b.eq    L200c
L1fdc:
        ldr     w5, [x21, x4, lsl #2]
        ldr     w7, [x20, x4, lsl #2]
        add     w6, w5, w25
        cmp     w6, w22
        b.ls    L1fc4
L1ff0:
        cmp     w19, #0x50
        b.eq    L2028
        strb    w4, [x26, w19, uxtw]
        add     x4, x4, #0x1
        add     w19, w19, #0x1
        cmp     x4, #0x100
        b.ne    L1fdc
L200c:
        add     x28, x28, #0xc0
        strb    w19, [x23], #1
        add     x21, x21, #0x400
        cmp     x28, x24
        b.ne    L1fb0
        mov     w0, #0x0
        b       L202c
L2028:
        mov     w0, #0xffffffff
L202c:
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
L2050:
        add     w2, w2, w2, lsl #3
        lsl     w2, w2, #6
        add     x2, x2, #0x20
        add     x0, x0, x2
        b       L3474

// mldsa44_sig_unpack_hints (0x100 bytes)
L2064:
        stp     x19, x20, [sp, #-48]!
        mov     x6, x0
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        add     x22, x1, #0x920
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        mov     w23, w2
        cbz     w2, L2090
        add     w0, w2, #0x4f
        ldrb    w21, [x22, w0, uxtw]
L2090:
        add     w0, w23, #0x50
        ldrb    w20, [x22, w0, uxtw]
        cmp     w20, #0x50
        ccmp    w21, w20, #0x2, ls
        b.hi    L2104
        mov     x0, x6
        mov     w1, #0x0
        mov     x2, #0x400
        bl      L0e80
        add     x3, x19, w21, uxtb
        mov     x6, x0
        mov     w1, w21
        mov     w7, #0x1
        cmp     w21, w20
        b.cs    L2118
        nop
L20d0:
        ldrb    w4, [x3, #2336]
        mov     w5, w1
        add     w1, w1, #0x1
        add     x3, x3, #0x1
        str     w7, [x6, x4, lsl #2]
        cmp     w20, w1
        b.ls    L2118
        cmp     w21, w1
        b.cs    L20d0
        ldrb    w0, [x22, w5, uxtw]
        ldrb    w4, [x3, #2336]
        cmp     w4, w0
        b.hi    L20d0
L2104:
        mov     w0, #0xffffffff
L2108:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L2118:
        cmp     w23, #0x3
        b.eq    L2134
L2120:
        mov     w0, #0x0
L2124:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L2134:
        cmp     w20, #0x50
        b.eq    L2120
        ldrb    w0, [x22, x20]
        add     x20, x20, #0x1
        cbnz    w0, L2104
L2148:
        cmp     w20, #0x50
        b.eq    L2124
        ldrb    w0, [x22, x20]
        add     x20, x20, #0x1
        cbz     w0, L2148
        mov     w0, #0xffffffff
        b       L2108
        nop
        nop
        nop

// mld_rej_uniform_c.constprop.0 (0x6c bytes)
L2170:
        mov     x9, x0
        cmp     w1, #0xff
        b.hi    L21d4
        mov     w8, #0x3
        sub     w8, w8, w2
        b       L2194
L2188:
        mov     w1, w0
L218c:
        cmp     w3, w7
        b.cc    L21d4
L2194:
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
        b.hi    L218c
        str     w4, [x9, w1, uxtw #2]
        cmp     w1, #0xff
        b.ne    L2188
        ret
L21d4:
        mov     w0, w1
        ret
        nop

// mldsa_poly_reduce (0x30 bytes)
L21e0:
        .inst   0x90000042  // adrp x2, 0xa000
        add     x1, x0, #0x400
        movi    v3.4s, #0x40, lsl #16
        ldr     q2, [x2, #4016]
L21f0:
        ldr     q0, [x0]
        add     v1.4s, v0.4s, v3.4s
        sshr    v1.4s, v1.4s, #23
        mla     v0.4s, v1.4s, v2.4s
        str     q0, [x0], #16
        cmp     x1, x0
        b.ne    L21f0
        ret

// mldsa_poly_caddq (0x3c bytes)
L2210:
        mov     w5, #0xe001
        add     x4, x0, #0x400
        movk    w5, #0x7f, lsl #16
        nop
L2220:
        ldr     w3, [x0]
        sxtw    x1, w3
        asr     x1, x1, #31
        add     w2, w3, w5
        eor     w2, w2, w3
        and     w1, w2, w1
        eor     w1, w1, w3
        str     w1, [x0], #4
        cmp     x0, x4
        b.ne    L2220
        ret
        nop

// mldsa_poly_add (0x28 bytes)
L2250:
        mov     x2, #0x0
        nop
L2258:
        ldr     q0, [x0, x2]
        ldr     q1, [x1, x2]
        add     v0.4s, v0.4s, v1.4s
        str     q0, [x0, x2]
        add     x2, x2, #0x10
        cmp     x2, #0x400
        b.ne    L2258
        ret
        nop
        nop

// mldsa_poly_sub (0x28 bytes)
L2280:
        mov     x2, #0x0
        nop
L2288:
        ldr     q0, [x0, x2]
        ldr     q1, [x1, x2]
        sub     v0.4s, v0.4s, v1.4s
        str     q0, [x0, x2]
        add     x2, x2, #0x10
        cmp     x2, #0x400
        b.ne    L2288
        ret
        nop
        nop

// mldsa_poly_shiftl (0x20 bytes)
L22b0:
        add     x1, x0, #0x400
        nop
L22b8:
        ldr     q0, [x0]
        shl     v0.4s, v0.4s, #13
        str     q0, [x0], #16
        cmp     x0, x1
        b.ne    L22b8
        ret

// mldsa_poly_ntt (0xcc bytes)
L22d0:
        .inst   0x90000049  // adrp x9, 0xa000
        mov     w15, #0x2001
        mov     x6, x0
        add     x9, x9, #0xfe0
        mov     w3, #0x0
        mov     w8, #0x64f7
        mov     w13, #0x1
        mov     w16, #0x100
        movk    w15, #0x380, lsl #16
        mov     w14, #0xff801fff
L22f8:
        add     w12, w3, #0x1
        mov     w0, #0x0
        lsl     w3, w13, w3
        lsr     w2, w16, w12
        lsl     w5, w2, #1
        nop
L2310:
        add     w3, w3, #0x1
        cmp     w0, w2
        b.cs    L2368
        mov     w4, w0
        neg     x1, x4, lsl #2
        add     x1, x1, w2, uxtw #2
        add     x1, x6, x1
        nop
L2330:
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
        b.hi    L2330
L2368:
        add     w0, w0, w5
        add     w2, w2, w5
        cmp     w0, #0xff
        b.hi    L2380
        ldr     w8, [x9, w3, uxtw #2]
        b       L2310
L2380:
        cmp     w12, #0x8
        b.eq    L2398
        lsl     w0, w13, w12
        mov     w3, w12
        ldr     w8, [x9, x0, lsl #2]
        b       L22f8
L2398:
        ret
        nop

// mldsa_poly_invntt_tomont (0x118 bytes)
L23a0:
        .inst   0x9000004a  // adrp x10, 0xa000
        mov     w14, #0x2001
        mov     x7, x0
        add     x10, x10, #0xfe0
        add     x11, x0, #0x4
        mov     w12, #0x8
        mov     w16, #0x100
        mov     w15, #0x1
        movk    w14, #0x380, lsl #16
        mov     w13, #0xff801fff
L23c8:
        lsr     w1, w16, w12
        mov     w2, #0x0
        lsl     w5, w15, w12
        lsl     w8, w1, #1
        sub     w5, w5, #0x1
        nop
L23e0:
        mov     w0, w5
        sub     w5, w5, #0x1
        ldr     w3, [x10, w0, uxtw #2]
        neg     w6, w3
        cmp     w1, w2
        b.ls    L244c
        sub     w0, w1, w2
        mov     w4, w1
        sub     w0, w0, #0x1
        mov     w3, w2
        add     x0, x0, x4
        sub     x3, x3, x4
        add     x4, x7, w1, uxtw #2
        add     x0, x11, x0, lsl #2
L2418:
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
        b.ne    L2418
L244c:
        add     w2, w2, w8
        add     w1, w1, w8
        cmp     w2, #0xff
        b.ls    L23e0
        subs    w12, w12, #0x1
        b.ne    L23c8
        .inst   0x90000042  // adrp x2, 0xa000
        .inst   0x90000041  // adrp x1, 0xa000
        mov     x0, x7
        ldr     q5, [x2, #4048]
        .inst   0x90000042  // adrp x2, 0xa000
        ldr     q4, [x1, #4032]
        add     x1, x7, #0x400
        ldr     q3, [x2, #4016]
        nop
L2488:
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
        b.ne    L2488
        ret
        nop
        nop

// mldsa_poly_pointwise_montgomery (0x50 bytes)
L24c0:
        .inst   0x90000042  // adrp x2, 0xa000
        ldr     q4, [x2, #4048]
        .inst   0x90000042  // adrp x2, 0xa000
        ldr     q3, [x2, #4016]
        mov     x2, #0x0
        nop
L24d8:
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
        b.ne    L24d8
        ret

// mldsa_poly_power2round (0x3c bytes)
L2510:
        movi    v4.4s, #0xf, msl #8
        mov     x3, #0x0
        mvni    v3.4s, #0x1f, msl #8
        nop
L2520:
        ldr     q0, [x2, x3]
        add     v1.4s, v0.4s, v4.4s
        and     v2.16b, v1.16b, v3.16b
        sshr    v1.4s, v1.4s, #13
        sub     v0.4s, v0.4s, v2.4s
        str     q1, [x0, x3]
        str     q0, [x1, x3]
        add     x3, x3, #0x10
        cmp     x3, #0x400
        b.ne    L2520
        ret
        nop

// mldsa_poly_uniform (0x104 bytes)
L2550:
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
        bl      L0e90
        mov     x1, x19
        mov     x2, #0x22
        mov     x0, x21
        bl      L0ec0
        mov     x0, x21
        bl      L0f50
        mov     x2, x21
        mov     x0, x20
        mov     x1, #0x348
        bl      L0fd0
        mov     x2, x20
        mov     x0, x22
        mov     w3, #0x348
        mov     w1, #0x0
        bl      L2170
        cmp     w0, #0xff
        b.hi    L2608
        mov     w19, w0
L25d8:
        mov     x2, x21
        mov     x0, x20
        mov     x1, #0xa8
        bl      L0fd0
        mov     w1, w19
        mov     x2, x20
        mov     x0, x22
        mov     w3, #0xa8
        bl      L2170
        mov     w19, w0
        cmp     w0, #0xff
        b.ls    L25d8
L2608:
        mov     x0, x21
        bl      L1080
        mov     x0, x20
        mov     x2, #0x348
        mov     w1, #0x0
        bl      L0e80
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1128]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L2650
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        add     sp, sp, #0x470
        ret
L2650:
        bl      L0e70

// mldsa_poly_uniform_4x (0x210 bytes)
L2654:
        mov     x12, #0x1140
        sub     sp, sp, x12
        .inst   0xb00000e5  // adrp x5, 0x1f000
        ldr     x5, [x5, #4088]
        stp     x19, x20, [sp]
        mov     x19, x4
        mov     x20, x1
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x22, sp, #0x9f
        stp     x23, x24, [sp, #32]
        and     x22, x22, #0xffffffffffffffe0
        add     x23, x22, #0xa20
        stp     x25, x26, [sp, #48]
        add     x26, sp, #0xe18
        add     x24, x22, #0x6c0
        stp     x27, x28, [sp, #64]
        mov     x28, x0
        mov     x27, x3
        str     x30, [sp, #80]
        add     x25, x22, #0x360
        stp     x0, x1, [sp, #96]
        stp     x2, x3, [sp, #112]
        ldr     x0, [x5]
        str     x0, [sp, #4408]
        mov     x0, #0x0
        mov     x0, x26
        bl      L15b0
        add     x4, x19, #0xc0
        add     x3, x19, #0x80
        add     x2, x19, #0x40
        mov     x1, x19
        mov     x0, x26
        mov     x5, #0x22
        bl      L14c0
        mov     x5, x26
        mov     x4, #0x5
        mov     x3, x23
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L1524
        mov     w3, #0x348
        mov     x2, x22
        mov     x0, x28
        mov     w1, #0x0
        bl      L2170
        mov     w19, w0
        mov     x2, x25
        mov     x0, x20
        mov     w1, #0x0
        bl      L2170
        mov     x2, x24
        mov     w20, w0
        mov     w1, #0x0
        mov     x0, x21
        bl      L2170
        mov     w21, w0
        mov     w1, #0x0
        mov     x0, x27
        mov     x2, x23
        bl      L2170
        cmp     w21, #0xff
        mov     w27, #0xff
        ccmp    w0, w27, #0x0, hi
        mov     w28, w0
        cset    w0, ls
        cmp     w20, w27
        ccmp    w19, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbz     w0, L2808
        nop
L2778:
        mov     x5, x26
        mov     x4, #0x1
        mov     x3, x23
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L1524
        ldr     x0, [sp, #96]
        mov     w3, #0xa8
        mov     w1, w19
        mov     x2, x22
        bl      L2170
        mov     w19, w0
        ldr     x0, [sp, #104]
        mov     w1, w20
        mov     x2, x25
        bl      L2170
        mov     w20, w0
        ldr     x0, [sp, #112]
        mov     w1, w21
        mov     x2, x24
        bl      L2170
        mov     w21, w0
        ldr     x0, [sp, #120]
        mov     w1, w28
        mov     x2, x23
        bl      L2170
        cmp     w0, #0xff
        ccmp    w21, w27, #0x0, hi
        mov     w28, w0
        cset    w0, ls
        cmp     w19, #0xff
        ccmp    w20, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbnz    w0, L2778
L2808:
        mov     x0, x26
        bl      L15b4
        mov     x0, x22
        mov     x2, #0xd80
        mov     w1, #0x0
        bl      L0e80
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L2860
        ldp     x19, x20, [sp]
        mov     x12, #0x1140
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret
L2860:
        bl      L0e70

// mldsa_polyt1_pack (0x5c bytes)
L2864:
        add     x4, x0, #0x140
L2868:
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
        b.ne    L2868
        ret

// mldsa_polyt1_unpack (0x74 bytes)
L28c0:
        add     x4, x1, #0x140
        nop
L28c8:
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
        b.ne    L28c8
        ret

// mldsa_polyt0_pack (0x128 bytes)
L2934:
        .inst   0xb00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-64]!
        add     x10, x0, #0x1a0
        ldr     x3, [x2]
        str     x3, [sp, #56]
        mov     x3, #0x0
        mov     w3, #0x1000
        nop
L2958:
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
        b.ne    L2958
        add     x0, sp, #0x18
        stp     xzr, xzr, [sp, #24]
        stp     xzr, xzr, [sp, #40]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #56]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L2a58
        ldr     x30, [sp], #64
        ret
L2a58:
        bl      L0e70
        nop

// mldsa_polyt0_unpack (0x154 bytes)
L2a60:
        add     x10, x1, #0x1a0
        mov     w9, #0x1000
L2a68:
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
        b.ne    L2a68
        ret

// mldsa_poly_chknorm (0x4c bytes)
L2bb4:
        sub     w5, w1, #0x1
        mov     x4, x0
        add     x6, x0, #0x400
        mov     w0, #0x0
        nop
L2bc8:
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
        b.ne    L2bc8
        ret

// mldsa_polyw1_pack_88 (0x60 bytes)
L2c00:
        add     x4, x0, #0xc0
        nop
L2c08:
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
        b.ne    L2c08
        ret

// mldsa_polyw1_pack_32 (0x24 bytes)
L2c60:
        add     x4, x1, #0x400
        nop
L2c68:
        ldr     w2, [x1, #4]
        ldr     w3, [x1], #8
        orr     w2, w3, w2, lsl #4
        strb    w2, [x0], #1
        cmp     x4, x1
        b.ne    L2c68
        ret

// mldsa_polyw1_unpack_88 (0x60 bytes)
L2c84:
        add     x4, x1, #0xc0
L2c88:
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
        b.ne    L2c88
        ret

// mldsa_polyw1_unpack_32 (0x2c bytes)
L2ce4:
        add     x3, x0, #0x400
L2ce8:
        ldrb    w2, [x1]
        add     x0, x0, #0x8
        and     w2, w2, #0xf
        stur    w2, [x0, #-8]
        ldrb    w2, [x1], #1
        lsr     w2, w2, #4
        stur    w2, [x0, #-4]
        cmp     x0, x3
        b.ne    L2ce8
        ret

// mld_rej_eta_c44.constprop.0 (0xa8 bytes)
L2d10:
        mov     x8, x0
        mov     w0, w1
        cmp     w1, #0xff
        b.hi    L2db4
        mov     w9, #0x1
        sub     w9, w9, w2
        mov     w7, #0xcd
        mov     w10, #0x2
L2d30:
        ldrb    w3, [x2]
        add     w5, w9, w2
        add     x2, x2, #0x1
        and     w4, w3, #0xf
        lsr     w3, w3, #4
        cmp     w4, #0xf
        b.eq    L2d68
        mul     w1, w4, w7
        lsr     w1, w1, #10
        add     w1, w1, w1, lsl #2
        sub     w4, w4, w1
        sub     w4, w10, w4
        str     w4, [x8, w0, uxtw #2]
        add     w0, w0, #0x1
L2d68:
        cmp     w0, #0xff
        mul     w1, w3, w7
        cset    w4, ls
        add     w6, w0, #0x1
        cmp     w4, #0x0
        ccmp    w3, #0xe, #0x2, ne
        b.hi    L2da4
        lsr     w1, w1, #10
        cmp     w6, #0xff
        cset    w4, ls
        add     w1, w1, w1, lsl #2
        sub     w3, w3, w1
        sub     w3, w10, w3
        str     w3, [x8, w0, uxtw #2]
        mov     w0, w6
L2da4:
        cmp     w5, #0x87
        cset    w1, ls
        tst     w4, w1
        b.ne    L2d30
L2db4:
        ret
        nop
        nop

// mldsa44_poly_decompose (0x80 bytes)
L2dc0:
        mov     w8, #0x1800
        mov     x5, #0x0
        mov     w10, #0x2c0b
        mov     w9, #0x2b
        movk    w8, #0xfffd, lsl #16
        mov     w7, #0x3ff000
        mov     w6, #0xff801fff
        nop
L2de0:
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
        b.ne    L2de0
        ret

// mldsa44_poly_use_hint (0xb0 bytes)
L2e40:
        mov     w10, #0x1800
        mov     x6, #0x0
        mov     w11, #0x2c0b
        mov     w7, #0x2b
        movk    w10, #0xfffd, lsl #16
        mov     w9, #0x3ff000
        mov     w8, #0xff801fff
        b       L2e78
L2e60:
        cmp     w2, #0x2b
        csinc   w2, wzr, w2, eq
L2e68:
        str     w2, [x0, x6]
        add     x6, x6, #0x4
        cmp     x6, #0x400
        b.eq    L2eec
L2e78:
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
        cbz     w12, L2e68
        sub     w4, w2, #0x1
        cmp     w3, #0x0
        b.gt    L2e60
        cmp     w2, #0x0
        csel    w2, w4, w7, ne
        str     w2, [x0, x6]
        add     x6, x6, #0x4
        cmp     x6, #0x400
        b.ne    L2e78
L2eec:
        ret

// mldsa44_poly_uniform_eta_4x (0x268 bytes)
L2ef0:
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
        bl      L16c0
        mov     x4, x21
        mov     x3, x20
        mov     x2, x19
        mov     x1, x28
        mov     x0, x26
        mov     x5, #0x42
        bl      L15d0
        mov     x3, x23
        mov     x5, x26
        mov     x4, #0x1
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L1634
        ldr     x0, [sp, #104]
        mov     x2, x22
        mov     w1, #0x0
        bl      L2d10
        mov     w19, w0
        ldr     x0, [sp, #112]
        mov     x2, x25
        mov     w1, #0x0
        bl      L2d10
        mov     w20, w0
        ldr     x0, [sp, #120]
        mov     x2, x24
        mov     w1, #0x0
        bl      L2d10
        mov     w21, w0
        ldr     x0, [sp, #128]
        mov     w1, #0x0
        mov     x2, x23
        bl      L2d10
        mov     w28, w0
        cmp     w21, w27
        ccmp    w0, w27, #0x0, hi
        cset    w0, ls
        cmp     w20, w27
        ccmp    w19, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbz     w0, L30ec
        nop
L3060:
        mov     x5, x26
        mov     x3, x23
        mov     x4, #0x1
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L1634
        ldr     x0, [sp, #104]
        mov     w1, w19
        mov     x2, x22
        bl      L2d10
        mov     w19, w0
        ldr     x0, [sp, #112]
        mov     w1, w20
        mov     x2, x25
        bl      L2d10
        mov     w20, w0
        ldr     x0, [sp, #120]
        mov     w1, w21
        mov     x2, x24
        bl      L2d10
        mov     w21, w0
        ldr     x0, [sp, #128]
        mov     w1, w28
        mov     x2, x23
        bl      L2d10
        cmp     w0, #0xff
        ccmp    w21, w27, #0x0, hi
        mov     w28, w0
        cset    w0, ls
        cmp     w19, #0xff
        ccmp    w20, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbnz    w0, L3060
L30ec:
        mov     x0, x26
        bl      L16c4
        mov     x0, x22
        mov     x2, #0x280
        mov     w1, #0x0
        bl      L0e80
        ldr     x19, [sp, #136]
        mov     x2, #0x180
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1992]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3154
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x7d0
        ret
L3154:
        bl      L0e70
        nop
        nop

// mldsa44_poly_challenge (0x168 bytes)
L3160:
        stp     x19, x20, [sp, #-448]!
        mov     x19, x1
        .inst   0x900000e3  // adrp x3, 0x1f000
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
        bl      L10a4
        mov     x1, x19
        mov     x2, #0x20
        mov     x0, x21
        bl      L10d0
        mov     x0, x21
        bl      L1160
        mov     x2, x21
        mov     x0, x20
        mov     x1, #0x88
        bl      L11e0
        mov     x2, x20
        mov     w0, #0x0
        mov     x3, #0x0
L31d0:
        ldrb    w1, [x2], #1
        lsl     x1, x1, x0
        add     w0, w0, #0x8
        orr     x3, x3, x1
        cmp     w0, #0x40
        b.ne    L31d0
        mov     x0, x23
        mov     x2, #0x400
        mov     w1, #0x0
        str     x3, [sp, #56]
        bl      L0e80
        mov     x19, #0xd9
        mov     w22, #0x1
        mov     w0, #0x8
        b       L321c
L320c:
        ldrb    w1, [x20, w0, uxtw]
        add     w0, w0, #0x1
        cmp     w1, w19
        b.ls    L3244
L321c:
        cmp     w0, #0x88
        b.ne    L320c
        mov     x0, x20
        mov     x1, #0x88
        mov     x2, x21
        bl      L11e0
        ldrb    w1, [x20]
        mov     w0, #0x1
        cmp     w1, w19
        b.hi    L320c
L3244:
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
        b.ne    L321c
        mov     x0, x21
        bl      L1290
        movi    v0.4s, #0x0
        str     xzr, [x20, #128]
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        stp     q0, q0, [x20, #64]
        stp     q0, q0, [x20, #96]
        add     x0, sp, #0x38
        str     xzr, [sp, #56]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #440]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L32c4
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #448
        ret
L32c4:
        bl      L0e70
        nop
        nop

// mldsa44_polyeta_pack (0xdc bytes)
L32d0:
        .inst   0x900000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        add     x10, x1, #0x400
        mov     w5, #0x2
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
L32f0:
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
        b.ne    L32f0
        add     x0, sp, #0x10
        str     xzr, [sp, #16]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L33a8
        ldr     x30, [sp], #32
        ret
L33a8:
        bl      L0e70
        nop

// mldsa44_polyeta_unpack (0xc4 bytes)
L33b0:
        movi    v2.4s, #0x2
        add     x5, x1, #0x60
L33b8:
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
        b.ne    L33b8
        ret

// mldsa44_polyz_pack (0xe0 bytes)
L3474:
        .inst   0x900000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-48]!
        add     x9, x1, #0x400
        mov     w6, #0x20000
        ldr     x3, [x2]
        str     x3, [sp, #40]
        mov     x3, #0x0
        nop
L3498:
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
        b.ne    L3498
        add     x0, sp, #0x18
        stp     xzr, xzr, [sp, #24]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #40]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3550
        ldr     x30, [sp], #48
        ret
L3550:
        bl      L0e70

// mldsa44_polyz_unpack (0xd0 bytes)
L3554:
        add     x8, x1, #0x240
        mov     w7, #0x20000
        nop
L3560:
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
        b.ne    L3560
        ret

// mldsa44_poly_uniform_gamma1_4x (0x18c bytes)
L3624:
        mov     x12, #0x1040
        sub     sp, sp, x12
        mov     x8, x4
        .inst   0x900000e9  // adrp x9, 0x1f000
        ldr     x9, [x9, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x9f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        add     x20, x19, #0xb00
        stp     x23, x24, [sp, #32]
        add     x22, x19, #0xb60
        add     x23, x19, #0xbc0
        stp     x25, x26, [sp, #48]
        add     x21, sp, #0xd18
        mov     x24, x1
        stp     x27, x28, [sp, #64]
        mov     x25, x0
        mov     x0, x21
        str     x30, [sp, #80]
        add     x26, x19, #0x840
        add     x27, x19, #0x580
        add     x28, x19, #0x2c0
        ldp     q0, q1, [x4, #32]
        add     x4, x19, #0xc20
        ldp     q2, q3, [x8]
        mov     x8, x9
        ldr     x9, [x8]
        str     x9, [sp, #4152]
        mov     x9, #0x0
        ldrh    w8, [sp, #4160]
        stp     q0, q1, [x20, #32]
        stp     q0, q1, [x22, #32]
        stp     x2, x3, [sp, #104]
        stp     q2, q3, [x20]
        stp     q2, q3, [x22]
        stp     q2, q3, [x23]
        stp     q0, q1, [x23, #32]
        stp     q2, q3, [x4]
        stp     q0, q1, [x4, #32]
        str     x4, [sp, #120]
        strh    w5, [x19, #2880]
        strh    w6, [x19, #2976]
        strh    w7, [x19, #3072]
        strh    w8, [x19, #3168]
        bl      L16c0
        ldr     x4, [sp, #120]
        mov     x3, x23
        mov     x2, x22
        mov     x1, x20
        mov     x0, x21
        mov     x5, #0x42
        bl      L15d0
        mov     x3, x26
        mov     x2, x27
        mov     x5, x21
        mov     x4, #0x5
        mov     x1, x28
        mov     x0, x19
        bl      L1634
        mov     x1, x19
        mov     x0, x25
        bl      L3554
        mov     x1, x28
        mov     x0, x24
        bl      L3554
        ldr     x0, [sp, #104]
        mov     x1, x27
        bl      L3554
        ldr     x0, [sp, #112]
        mov     x1, x26
        bl      L3554
        mov     x0, x21
        bl      L16c4
        mov     x0, x19
        mov     x2, #0xb00
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x180
        mov     x0, x20
        mov     w1, #0x0
        bl      L0e80
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4152]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L37ac
        ldp     x19, x20, [sp]
        mov     x12, #0x1040
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret
L37ac:
        bl      L0e70

// mldsa44_polyvecl_uniform_gamma1 (0x40 bytes)
L37b0:
        sub     sp, sp, #0x20
        sxth    w6, w2
        add     w3, w6, #0x3
        add     w7, w6, #0x2
        mov     x4, x1
        mov     w5, w2
        strh    w3, [sp]
        add     w6, w6, #0x1
        add     x3, x0, #0xc00
        add     x2, x0, #0x800
        add     x1, x0, #0x400
        str     x30, [sp, #16]
        bl      L3624
        ldr     x30, [sp, #16]
        add     sp, sp, #0x20
        ret

// mldsa44_polyvecl_ntt (0x28 bytes)
L37f0:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L22d0
        add     x0, x19, #0x400
        bl      L22d0
        add     x0, x19, #0x800
        bl      L22d0
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L22d0
        nop
        nop

// mldsa44_polyvecl_pointwise_acc_montgomery (0x78 bytes)
L3820:
        mov     x6, x0
        .inst   0xf0000020  // adrp x0, 0xa000
        mov     x4, x2
        mov     x5, x1
        ldr     q5, [x0, #4048]
        .inst   0xf0000020  // adrp x0, 0xa000
        mov     x1, #0x0
        ldr     q4, [x0, #4016]
L3840:
        add     x3, x4, x1
        movi    v1.4s, #0x0
        add     x2, x5, x1
        mov     x0, #0x0
        mov     v0.16b, v1.16b
L3854:
        ldr     q2, [x2, x0]
        ldr     q3, [x3, x0]
        add     x0, x0, #0x400
        smlal   v0.2d, v3.2s, v2.2s
        smlal2  v1.2d, v3.4s, v2.4s
        cmp     x0, #0x1, lsl #12
        b.ne    L3854
        uzp1    v2.4s, v0.4s, v1.4s
        mul     v2.4s, v2.4s, v5.4s
        smlal   v0.2d, v2.2s, v4.2s
        smlal2  v1.2d, v2.4s, v4.4s
        uzp2    v0.4s, v0.4s, v1.4s
        str     q0, [x6, x1]
        add     x1, x1, #0x10
        cmp     x1, #0x400
        b.ne    L3840
        ret
        nop
        nop

// mldsa44_polyvecl_chknorm (0x4c bytes)
L38a0:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     w20, #0x0
        stp     x21, x22, [sp, #16]
        mov     w21, w1
        add     x22, x0, #0x1, lsl #12
        str     x30, [sp, #32]
L38bc:
        mov     x0, x19
        mov     w1, w21
        add     x19, x19, #0x400
        bl      L2bb4
        orr     w20, w20, w0
        cmp     x19, x22
        b.ne    L38bc
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
        nop

// mldsa44_polyveck_caddq (0x28 bytes)
L38f0:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L2210
        add     x0, x19, #0x400
        bl      L2210
        add     x0, x19, #0x800
        bl      L2210
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L2210
        nop
        nop

// mldsa44_polyveck_ntt (0x28 bytes)
L3920:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L22d0
        add     x0, x19, #0x400
        bl      L22d0
        add     x0, x19, #0x800
        bl      L22d0
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L22d0
        nop
        nop

// mldsa44_polyveck_invntt_tomont (0x28 bytes)
L3950:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L23a0
        add     x0, x19, #0x400
        bl      L23a0
        add     x0, x19, #0x800
        bl      L23a0
        add     x0, x19, #0xc00
        ldp     x19, x30, [sp], #16
        b       L23a0
        nop
        nop

// mldsa44_polyveck_unpack_eta_chknorm (0x5c bytes)
L3980:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x20, x2
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        add     x23, x0, #0x180
L39a0:
        mov     x1, x19
        mov     x0, x20
        bl      L33b0
        mov     w1, w22
        mov     x0, x20
        add     x19, x19, #0x60
        bl      L2bb4
        orr     w21, w21, w0
        cmp     x19, x23
        b.ne    L39a0
        ldp     x23, x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret
        nop

// mldsa44_polyveck_decompose_pack_w1 (0x54 bytes)
L39e0:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x22, x0, #0x300
        str     x30, [sp, #32]
L39fc:
        mov     x1, x20
        mov     x0, x21
        bl      L2dc0
        add     x20, x20, #0x400
        mov     x0, x19
        mov     x1, x21
        add     x19, x19, #0xc0
        bl      L2c00
        cmp     x19, x22
        b.ne    L39fc
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mldsa44_polyvecl_unpack_eta (0x3c bytes)
L3a34:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x30, [sp, #16]
        add     x21, x1, #0x180
L3a48:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x60
        bl      L33b0
        add     x20, x20, #0x400
        cmp     x19, x21
        b.ne    L3a48
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa44_polyvecl_unpack_z (0x3c bytes)
L3a70:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x30, [sp, #16]
        add     x21, x1, #0x900
L3a84:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x240
        bl      L3554
        add     x20, x20, #0x400
        cmp     x19, x21
        b.ne    L3a84
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop

// mldsa44_polyveck_unpack_eta (0x3c bytes)
L3ab0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x30, [sp, #16]
        add     x21, x1, #0x180
L3ac4:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x60
        bl      L33b0
        add     x20, x20, #0x400
        cmp     x19, x21
        b.ne    L3ac4
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop

// mldsa44_polyvec_matrix_expand_eager (0x130 bytes)
L3af0:
        stp     x19, x20, [sp, #-352]!
        .inst   0x900000e3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        add     x20, sp, #0x5f
        stp     x21, x22, [sp, #16]
        and     x20, x20, #0xffffffffffffffe0
        mov     x2, x20
        stp     x23, x24, [sp, #32]
        mov     x24, x0
        add     x0, x20, #0x100
        stp     x25, x30, [sp, #48]
        ldr     x4, [x3]
        str     x4, [sp, #344]
        mov     x4, #0x0
L3b28:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x2]
        add     x2, x2, #0x40
        cmp     x0, x2
        b.ne    L3b28
        mov     w19, #0x4
        mov     w25, #0x1000
        mov     x23, #0xc00
        mov     x22, #0x800
        mov     x21, #0x400
L3b50:
        sub     w5, w19, #0x4
        mov     x2, x20
        mov     w1, w5
L3b5c:
        and     w4, w1, #0x3
        lsr     w3, w1, #2
        add     w1, w1, #0x1
        strb    w4, [x2, #32]
        strb    w3, [x2, #33]
        add     x2, x2, #0x40
        cmp     w19, w1
        b.ne    L3b5c
        sub     w3, w19, #0x1
        sub     w2, w19, #0x2
        sub     w1, w19, #0x3
        lsr     w5, w5, #2
        lsr     w3, w3, #2
        lsr     w2, w2, #2
        lsr     w1, w1, #2
        add     w19, w19, #0x4
        add     x0, x24, x5, lsl #12
        mov     x4, x20
        umaddl  x3, w3, w25, x23
        umaddl  x2, w2, w25, x22
        umaddl  x1, w1, w25, x21
        add     x3, x24, x3
        add     x2, x24, x2
        add     x1, x24, x1
        bl      L2654
        cmp     w19, #0x14
        b.ne    L3b50
        movi    v0.4s, #0x0
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        stp     q0, q0, [x20, #64]
        stp     q0, q0, [x20, #96]
        stp     q0, q0, [x20, #128]
        stp     q0, q0, [x20, #160]
        stp     q0, q0, [x20, #192]
        stp     q0, q0, [x20, #224]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #344]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3c1c
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #352
        ret
L3c1c:
        bl      L0e70

// mldsa44_polyvec_matrix_pointwise_montgomery_row_eager (0xc bytes)
L3c20:
        ubfiz   x3, x3, #12, #32
        add     x1, x1, x3
        b       L3820
        nop

// mldsa44_polyvec_matrix_pointwise_montgomery_yvec_eager (0x70 bytes)
L3c30:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x0
        mov     w19, #0x0
        stp     x21, x22, [sp, #16]
        mov     x22, x1
        mov     x1, x2
        mov     x2, #0x1000
        mov     x21, x3
        stp     x23, x30, [sp, #32]
        mov     x23, x0
        mov     x0, x3
        bl      L0e50
        mov     x0, x21
        bl      L37f0
L3c68:
        mov     w3, w19
        mov     x0, x20
        mov     x2, x21
        mov     x1, x22
        add     w19, w19, #0x1
        bl      L3c20
        add     x20, x20, #0x400
        cmp     w19, #0x4
        b.ne    L3c68
        ldp     x21, x22, [sp, #16]
        mov     x0, x23
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        b       L3950

// mld_compute_pack_t0_t144 (0x15c bytes)
L3ca0:
        mov     x12, #0x4870
        sub     sp, sp, x12
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
        mov     x0, #0x4400
        add     x20, x26, #0x4, lsl #12
        ldr     x2, [x3]
        str     x2, [sp, #18536]
        mov     x2, #0x0
        add     x19, x26, x0
        mov     x1, x4
        mov     x0, x26
        bl      L3af0
L3d04:
        mov     w3, w21
        mov     x2, x23
        mov     x1, x26
        mov     x0, x19
        bl      L3c20
        add     w21, w21, #0x1
        mov     x0, x19
        bl      L23a0
        mov     x1, x22
        mov     x0, x20
        bl      L33b0
        add     x22, x22, #0x60
        mov     x1, x20
        mov     x0, x19
        bl      L2250
        mov     x0, x19
        bl      L21e0
        mov     x0, x19
        bl      L2210
        mov     x2, x19
        mov     x1, x19
        mov     x0, x20
        bl      L2510
        mov     x0, x25
        mov     x1, x20
        bl      L2864
        add     x25, x25, #0x140
        mov     x0, x24
        mov     x1, x19
        bl      L2934
        add     x24, x24, #0x1a0
        cmp     w21, #0x4
        b.ne    L3d04
        mov     x0, x20
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x400
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x4000
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e80
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #18536]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3df8
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x4870
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        add     sp, sp, x12
        ret
L3df8:
        bl      L0e70
        nop

// mld_H44 (0x10c bytes)
L3e00:
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
        bl      L10a4
        mov     x2, x25
        mov     x1, x24
        mov     x0, x19
        bl      L10d0
        cbnz    x21, L3ee0
        cbnz    x20, L3ef4
L3e6c:
        mov     x0, x19
        bl      L1160
        mov     x2, x19
        mov     x1, x23
        mov     x0, x22
        bl      L11e0
        mov     x0, x19
        bl      L1290
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
        b.ne    L3f08
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #304
        ret
L3ee0:
        mov     x2, x21
        mov     x1, x26
        mov     x0, x19
        bl      L10d0
        cbz     x20, L3e6c
L3ef4:
        mov     x2, x20
        mov     x1, x27
        mov     x0, x19
        bl      L10d0
        b       L3e6c
L3f08:
        bl      L0e70
        nop

// mldsa44_keypair_internal (0x248 bytes)
L3f10:
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
        bl      L12b4
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
        bl      L2ef0
        mov     x1, x19
        mov     x0, x27
        bl      L32d0
        mov     x1, x26
        add     x0, x21, #0x260
        bl      L32d0
        mov     x1, x25
        add     x0, x21, #0x2c0
        bl      L32d0
        mov     x1, x24
        add     x0, x21, #0x320
        bl      L32d0
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
        bl      L2ef0
        mov     x1, x19
        add     x0, x21, #0x80
        bl      L32d0
        mov     x1, x26
        add     x0, x21, #0xe0
        bl      L32d0
        mov     x1, x25
        add     x0, x21, #0x140
        bl      L32d0
        mov     x1, x24
        add     x0, x21, #0x1a0
        bl      L32d0
        mov     x0, x19
        bl      L37f0
        ldp     q0, q1, [x20]
        mov     x4, x20
        mov     x3, x27
        mov     x2, x19
        add     x1, x21, #0x380
        add     x0, x23, #0x20
        stp     q0, q1, [x23]
        bl      L3ca0
        mov     x4, #0x1080
        mov     w25, w0
        add     x24, x19, x4
        cbnz    w0, L40b0
        mov     x0, x24
        mov     x2, x23
        mov     x3, #0x520
        mov     x1, #0x40
        bl      L12b4
        mov     x2, x24
        add     x3, x20, #0x60
        mov     x1, x20
        mov     x0, x21
        bl      L1e64
L40b0:
        mov     x0, x19
        mov     x2, #0x1000
        mov     w1, #0x0
        bl      L0e80
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
        cbnz    w25, L4130
L40ec:
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4472]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4154
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
L4130:
        mov     x0, x23
        mov     x2, #0x520
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0xa00
        mov     x0, x21
        mov     w1, #0x0
        bl      L0e80
        b       L40ec
L4154:
        bl      L0e70
        nop
        nop

// mldsa44_keypair (0x88 bytes)
L4160:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        .inst   0xf00000c2  // adrp x2, 0x1f000
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
        bl      L0e60
        cbnz    w0, L41dc
        mov     x1, x21
        mov     x0, x20
        mov     x2, x19
        bl      L3f10
L41ac:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xf00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #88]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L41e4
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #96
        ret
L41dc:
        mov     w0, #0xfffffffd
        b       L41ac
L41e4:
        bl      L0e70
        nop
        nop

// mldsa44_signature_internal (0x500 bytes)
L41f0:
        mov     x12, #0xadb0
        sub     sp, sp, x12
        add     x8, sp, #0xbf
        mov     x11, #0xab00
        and     x9, x8, #0xffffffffffffffe0
        .inst   0xf00000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        add     x10, x9, x11
        add     x12, x9, #0x9, lsl #12
        add     x11, x9, #0x7, lsl #12
        stp     x19, x20, [sp]
        mov     x20, x3
        mov     x19, x5
        stp     x21, x22, [sp, #16]
        mov     x21, x4
        mov     x4, x12
        stp     x23, x24, [sp, #32]
        mov     w24, w7
        mov     x23, x1
        stp     x25, x26, [sp, #48]
        add     x25, x10, #0x20
        mov     x22, x2
        stp     x27, x28, [sp, #64]
        mov     x1, x25
        mov     x26, x10
        str     x30, [sp, #80]
        add     x2, x10, #0x60
        str     x0, [sp, #96]
        mov     x5, x11
        stp     x10, x9, [sp, #128]
        add     x9, x9, #0x8, lsl #12
        mov     x3, x9
        str     x9, [sp, #112]
        mov     x0, x10
        stp     x12, x11, [sp, #144]
        mov     x12, #0x8040
        add     x9, sp, x12
        ldr     x7, [x8]
        str     x7, [x9, #11624]
        mov     x7, #0x0
        bl      L1e90
        cbnz    w24, L46d0
        mov     x3, #0x40
        mov     x7, x22
        mov     x6, x23
        mov     x5, x21
        mov     x4, x20
        mov     x2, x25
        add     x0, x26, #0x80
        mov     x1, x3
        bl      L3e00
L42bc:
        ldp     x24, x22, [sp, #128]
        mov     x2, #0xacd8
        mov     x4, x19
        mov     x5, #0x20
        mov     x8, #0xa800
        mov     x9, #0xac00
        mov     x10, #0xa400
        mov     x3, x5
        add     x21, sp, x2
        mov     x7, #0x40
        add     x6, x24, #0x80
        add     x2, x24, #0x60
        add     x1, x22, x8
        add     x0, x24, #0xc0
        add     x26, x22, x9
        add     x23, x22, x10
        str     x1, [sp, #120]
        mov     x1, x7
        bl      L3e00
        add     x27, x22, #0x6, lsl #12
        add     x19, x22, #0x5, lsl #12
        add     x25, x22, #0x4, lsl #12
        add     x20, x22, #0xa, lsl #12
        mov     x1, x24
        mov     x0, x22
        str     wzr, [sp, #108]
        bl      L3af0
L4328:
        ldrh    w2, [sp, #108]
        mov     x0, x27
        ldr     x22, [sp, #128]
        add     x1, x22, #0xc0
        bl      L37b0
        ldr     x1, [sp, #136]
        mov     x3, x19
        mov     x2, x27
        mov     x0, x25
        bl      L3c30
        mov     x0, x25
        bl      L38f0
        ldr     x24, [sp, #120]
        mov     x2, x19
        mov     x1, x25
        mov     x0, x24
        bl      L39e0
        mov     x0, x21
        bl      L10a4
        add     x1, x22, #0x80
        mov     x0, x21
        mov     x2, #0x40
        bl      L10d0
        mov     x1, x24
        mov     x2, #0x300
        mov     x0, x21
        bl      L10d0
        mov     x0, x21
        bl      L1160
        mov     x2, x21
        mov     x1, #0x20
        mov     x0, x26
        bl      L11e0
        mov     x0, x21
        bl      L1290
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x21, #64]
        stp     q0, q0, [x21, #96]
        stp     q0, q0, [x21, #128]
        stp     q0, q0, [x21, #160]
        str     q0, [x21, #192]
        mov     x1, x26
        mov     x0, x23
        ldr     x28, [sp, #144]
        bl      L3160
        mov     x24, x27
        mov     x0, x23
        mov     w22, #0x0
        bl      L22d0
L43f4:
        mov     x2, #0x400
        mov     x1, x28
        mov     x0, x20
        bl      L0e50
        mov     x1, x23
        mov     x0, x20
        bl      L24c0
        mov     x0, x20
        bl      L23a0
        mov     x2, #0x400
        mov     x1, x24
        mov     x0, x19
        bl      L0e50
        mov     x1, x19
        mov     x0, x20
        bl      L2250
        mov     x0, x20
        bl      L21e0
        mov     w1, #0xffb2
        mov     x0, x20
        movk    w1, #0x1, lsl #16
        bl      L2bb4
        cbnz    w0, L46c8
        ldr     x0, [sp, #96]
        mov     w2, w22
        mov     x1, x20
        add     w22, w22, #0x1
        add     x28, x28, #0x400
        add     x24, x24, #0x400
        bl      L2050
        cmp     w22, #0x4
        b.ne    L43f4
        ldr     x28, [sp, #112]
        mov     x22, x25
        ldr     x24, [sp, #152]
L4480:
        mov     x2, #0x400
        mov     x1, x24
        mov     x0, x19
        bl      L0e50
        mov     x1, x23
        mov     x0, x19
        bl      L24c0
        mov     x0, x19
        bl      L23a0
        mov     x1, x19
        mov     x0, x22
        bl      L2280
        mov     x0, x22
        bl      L21e0
        mov     w1, #0x73b2
        mov     x0, x22
        movk    w1, #0x1, lsl #16
        bl      L2bb4
        cbnz    w0, L46c8
        mov     x2, #0x400
        mov     x1, x28
        mov     x0, x19
        bl      L0e50
        mov     x1, x23
        mov     x0, x19
        bl      L24c0
        mov     x0, x19
        bl      L23a0
        mov     x0, x19
        bl      L21e0
        mov     w1, #0x7400
        mov     x0, x19
        movk    w1, #0x1, lsl #16
        bl      L2bb4
        cbnz    w0, L46c8
        mov     x0, x22
        mov     x1, x19
        bl      L2250
        add     x24, x24, #0x400
        ldr     x0, [sp, #112]
        add     x28, x28, #0x400
        add     x22, x22, #0x400
        cmp     x24, x0
        b.ne    L4480
        ldr     x22, [sp, #96]
        mov     x1, x26
        mov     x0, x22
        bl      L1f40
        ldr     x2, [sp, #120]
        mov     x0, x22
        mov     x3, x19
        mov     x1, x25
        bl      L1f50
        mov     w22, w0
L4558:
        mov     x0, x20
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x400
        mov     x0, x23
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x1000
        mov     x0, x25
        mov     w1, #0x0
        bl      L0e80
        ldr     x24, [sp, #120]
        mov     x2, #0x300
        mov     w1, #0x0
        mov     x0, x24
        bl      L0e80
        mov     x2, #0x1000
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x1000
        mov     x0, x27
        mov     w1, #0x0
        bl      L0e80
        stp     xzr, xzr, [x26]
        stp     xzr, xzr, [x26, #16]
        cbz     w22, L4604
        cmn     w22, #0x1
        b.ne    L45f0
        ldr     w0, [sp, #108]
        mov     w1, #0xfff8
        add     w0, w0, #0x4
        and     w2, w0, #0xffff
        str     w2, [sp, #108]
        cmp     w1, w0, uxth
        b.ne    L4328
        mov     w22, #0xfffffffc
L45f0:
        ldr     x19, [sp, #96]
        mov     x2, #0x974
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
L4604:
        ldr     x19, [sp, #152]
        mov     x2, #0x1000
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
        ldr     x19, [sp, #112]
        mov     x2, #0x1000
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
        ldr     x19, [sp, #144]
        mov     x2, #0x1000
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
        ldr     x19, [sp, #136]
        mov     x2, #0x4000
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
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
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     x1, #0x8040
        add     x2, sp, x1
        ldr     x3, [x2, #11624]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.ne    L46ec
        ldp     x19, x20, [sp]
        mov     w0, w22
        ldp     x21, x22, [sp, #16]
        mov     x12, #0xadb0
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret
L46c8:
        mov     w22, #0xffffffff
        b       L4558
L46d0:
        ldr     x0, [sp, #128]
        ldp     q2, q3, [x23]
        add     x0, x0, #0x80
        ldp     q0, q1, [x23, #32]
        stp     q2, q3, [x0]
        stp     q0, q1, [x0, #32]
        b       L42bc
L46ec:
        bl      L0e70

// mldsa44_signature_extmu (0xa8 bytes)
L46f0:
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
        bl      L0e60
        cbnz    w0, L478c
        mov     x6, x22
        mov     x1, x21
        mov     x0, x20
        mov     x5, x19
        mov     w7, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        bl      L41f0
L4758:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xf00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #104]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L4794
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret
L478c:
        mov     w0, #0xfffffffd
        b       L4758
L4794:
        bl      L0e70
        nop
        nop

// mldsa44_verify_internal (0x458 bytes)
L47a0:
        mov     x12, #0x60f0
        sub     sp, sp, x12
        mov     x7, x0
        stp     x19, x20, [sp]
        mov     x19, x1
        mov     x20, x4
        stp     x21, x22, [sp, #16]
        add     x21, sp, #0x9f
        and     x21, x21, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        add     x24, x21, #0x6, lsl #12
        mov     x23, x2
        stp     x25, x26, [sp, #48]
        add     x25, x21, #0x4, lsl #12
        mov     w26, w6
        stp     x27, x28, [sp, #64]
        str     x30, [sp, #80]
        stp     x5, x0, [sp, #104]
        ldp     q0, q1, [x7]
        str     x3, [sp, #120]
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x1, [x0]
        str     x1, [sp, #24808]
        mov     x1, #0x0
        mov     x0, x25
        add     x1, x7, #0x20
        stp     q0, q1, [x24, #-160]
        bl      L3a70
        mov     w1, #0xffb2
        mov     x0, x25
        movk    w1, #0x1, lsl #16
        bl      L38a0
        cbnz    w0, L4bb4
        mov     w22, w0
        cbz     w26, L4b00
        ldp     q2, q3, [x19]
        sub     x24, x24, #0x100
        ldp     q0, q1, [x19, #32]
        mov     x6, #0x5c00
        mov     x7, #0x5f00
        add     x28, x21, x6
        add     x27, x21, x7
        stp     q2, q3, [x24]
        stp     q0, q1, [x24, #32]
L4854:
        mov     x3, #0x5f60
        add     x1, x21, x3
        mov     x4, #0x5400
        mov     x5, #0x5800
        mov     x19, x1
        add     x26, x21, x5
        add     x20, x21, x4
        mov     x0, x25
        str     x1, [sp, #120]
        bl      L37f0
        mov     x24, x28
        ldr     x1, [sp, #104]
        mov     x0, x21
        bl      L3af0
        mov     x1, x19
        mov     x0, x26
        bl      L3160
        add     x19, x21, #0x5, lsl #12
        mov     x0, x26
        bl      L22d0
L48a4:
        mov     w3, w22
        mov     x2, x25
        mov     x1, x21
        mov     x0, x20
        bl      L3c20
        ldr     x1, [sp, #104]
        mov     w2, w22
        mov     x0, x19
        bl      L1e50
        mov     x0, x19
        bl      L22b0
        mov     x0, x19
        bl      L22d0
        mov     x1, x26
        mov     x0, x19
        bl      L24c0
        mov     x1, x19
        mov     x0, x20
        bl      L2280
        mov     x0, x20
        bl      L21e0
        mov     x0, x20
        bl      L23a0
        mov     x0, x20
        bl      L2210
        ldr     x1, [sp, #112]
        mov     w2, w22
        mov     x0, x19
        bl      L2064
        mov     w23, w0
        cbnz    w0, L4ba4
        mov     x1, x19
        mov     x0, x20
        bl      L2e40
        add     w22, w22, #0x1
        mov     x0, x24
        mov     x1, x20
        bl      L2c00
        add     x24, x24, #0xc0
        cmp     w22, #0x4
        b.ne    L48a4
        mov     x1, #0x5f40
        mov     x0, #0x6018
        add     x24, sp, x0
        add     x22, x21, x1
        mov     x0, x24
        bl      L10a4
        mov     x0, x24
        mov     x1, x27
        mov     x2, #0x40
        bl      L10d0
        mov     x1, x28
        mov     x2, #0x300
        mov     x0, x24
        bl      L10d0
        mov     x0, x24
        bl      L1160
        mov     x2, x24
        mov     x1, #0x20
        mov     x0, x22
        bl      L11e0
        mov     x0, x24
        bl      L1290
        movi    v0.4s, #0x0
        stp     q0, q0, [x24]
        stp     q0, q0, [x24, #32]
        stp     q0, q0, [x24, #64]
        stp     q0, q0, [x24, #96]
        stp     q0, q0, [x24, #128]
        stp     q0, q0, [x24, #160]
        str     q0, [x24, #192]
        ldr     q4, [x21, #24384]
        ldr     q3, [x21, #24400]
        ldr     q1, [x21, #24416]
        ldr     q2, [x21, #24432]
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
        b.ne    L4bac
L4a3c:
        mov     x0, x19
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x400
        mov     x0, x20
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x4000
        mov     x0, x21
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x400
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x1000
        mov     x0, x25
        mov     w1, #0x0
        bl      L0e80
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
        bl      L0e80
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24808]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4bf4
        ldp     x19, x20, [sp]
        mov     w0, w23
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x60f0
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret
L4b00:
        mov     x8, #0x6018
        mov     x9, #0x5c00
        add     x24, sp, x8
        add     x28, x21, x9
        mov     x0, x24
        bl      L10a4
        ldr     x1, [sp, #104]
        mov     x2, #0x520
        mov     x0, x24
        bl      L10d0
        mov     x0, x24
        bl      L1160
        mov     x2, x24
        mov     x1, #0x40
        mov     x0, x28
        bl      L11e0
        mov     x0, x24
        bl      L1290
        movi    v0.4s, #0x0
        stp     q0, q0, [x24]
        stp     q0, q0, [x24, #32]
        stp     q0, q0, [x24, #64]
        stp     q0, q0, [x24, #96]
        stp     q0, q0, [x24, #128]
        stp     q0, q0, [x24, #160]
        str     q0, [x24, #192]
        ldr     x4, [sp, #120]
        mov     x10, #0x5f00
        add     x27, x21, x10
        mov     x3, #0x40
        mov     x7, x23
        mov     x6, x19
        mov     x5, x20
        mov     x0, x27
        mov     x2, x28
        mov     x1, x3
        bl      L3e00
        movi    v0.4s, #0x0
        stp     q0, q0, [x28]
        stp     q0, q0, [x28, #32]
        b       L4854
L4ba4:
        mov     x2, #0x5f40
        add     x22, x21, x2
L4bac:
        mov     w23, #0xfffffffa
        b       L4a3c
L4bb4:
        mov     x11, #0x5c00
        mov     x12, #0x5f00
        mov     x13, #0x5f60
        mov     x14, #0x5800
        add     x0, x21, x13
        mov     x15, #0x5400
        mov     x16, #0x5f40
        add     x28, x21, x11
        add     x27, x21, x12
        add     x26, x21, x14
        add     x20, x21, x15
        add     x19, x21, #0x5, lsl #12
        add     x22, x21, x16
        mov     w23, #0xfffffffa
        str     x0, [sp, #120]
        b       L4a3c
L4bf4:
        bl      L0e70
        nop
        nop

// mldsa44_verify_extmu (0x18 bytes)
L4c00:
        mov     x5, x2
        mov     w6, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        b       L47a0
        nop
        nop

// mldsa44_prepare_domain_separation_prefix (0x19c bytes)
L4c20:
        cmp     x4, #0xff
        b.hi    L4c80
        stp     x19, x21, [sp, #-64]!
        mov     x19, x4
        mov     x21, x0
        str     x30, [sp, #32]
        cbz     w5, L4c64
        stp     x22, x23, [sp, #16]
        mov     x23, x1
        sub     w1, w5, #0x1
        mov     x0, #0x0
        cmp     w1, #0xb
        b.ls    L4c88
        ldp     x22, x23, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
L4c64:
        strb    wzr, [x0]
        strb    w4, [x21, #1]
        cbnz    x4, L4ca4
L4c70:
        add     x0, x19, #0x2
L4c74:
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
L4c80:
        mov     x0, #0x0
        ret
L4c88:
        .inst   0xf0000020  // adrp x0, 0xb000
        mov     x22, x2
        add     x0, x0, #0x3e0
        ldrb    w0, [x0, w1, uxtw]
        .inst   0x10000061  // adr     x1, 4ca4 <mldsa44_prepare_domain_separation_prefix+0x84>
        add     x0, x1, w0, sxtb #2
        br      x0
L4ca4:
        mov     x1, x3
        mov     x2, x4
        add     x0, x0, #0x2
        bl      L0e50
        b       L4c70
        cmp     x2, #0x20
        b.ne    L4d30
L4cc0:
        mov     w0, #0x1
        strb    w0, [x21]
        strb    w19, [x21, #1]
        cbnz    x19, L4da0
L4cd0:
        .inst   0xf0000021  // adrp x1, 0xb000
        add     x4, x1, #0x3f0
        mov     w3, #0x0
        nop
L4ce0:
        ldr     w0, [x4]
        cmp     w5, w0
        b.eq    L4d54
        add     w3, w3, #0x1
        add     x4, x4, #0x10
        cmp     w3, #0xc
        b.ne    L4ce0
        add     x0, x19, #0xd
        mov     x1, x23
        mov     x2, x22
        add     x0, x21, x0
        bl      L0e50
        add     x0, x22, #0xd
        ldp     x22, x23, [sp, #16]
        add     x0, x0, x19
L4d1c:
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
        cmp     x2, #0x1c
        b.eq    L4cc0
L4d30:
        ldp     x22, x23, [sp, #16]
        mov     x0, #0x0
        b       L4c74
        cmp     x2, #0x40
        b.eq    L4cc0
        b       L4d30
        cmp     x2, #0x30
        b.eq    L4cc0
        b       L4d30
L4d54:
        mov     x0, #0x4
        add     x1, x1, #0x3f0
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
        bl      L0e50
        add     x0, x22, #0xd
        ldp     x22, x23, [sp, #16]
        add     x0, x0, x19
        b       L4d1c
L4da0:
        mov     x1, x3
        mov     x2, x19
        add     x0, x21, #0x2
        str     w5, [sp, #60]
        bl      L0e50
        ldr     w5, [sp, #60]
        b       L4cd0
        nop

// mldsa44_signature (0x10c bytes)
L4dc0:
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
        bl      L4c20
        cbnz    x0, L4e7c
        add     x22, x19, #0x160
        mov     w26, #0xfffffff7
L4e1c:
        mov     x0, x20
        mov     x2, #0x974
        mov     w1, #0x0
        bl      L0e80
L4e2c:
        stp     xzr, xzr, [x19, #352]
        stp     xzr, xzr, [x22, #16]
        mov     x2, #0x14c
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e80
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #488]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4ec8
        ldp     x21, x22, [sp, #16]
        mov     w0, w26
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #496
        ret
L4e7c:
        add     x22, x19, #0x160
        mov     x21, x0
        mov     x1, #0x20
        mov     x0, x22
        mov     w26, #0xfffffffd
        bl      L0e60
        cbnz    w0, L4e1c
        mov     x6, x25
        mov     x4, x21
        mov     x2, x24
        mov     x1, x23
        mov     x5, x22
        mov     x3, x19
        mov     x0, x20
        mov     w7, #0x0
        bl      L41f0
        mov     w26, w0
        cbz     w0, L4e2c
        b       L4e1c
L4ec8:
        bl      L0e70
        nop

// mldsa44_verify (0xbc bytes)
L4ed0:
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
        bl      L4c20
        cbz     x0, L4f80
        mov     x4, x0
        mov     x5, x22
        mov     x0, x20
        mov     x2, x23
        mov     x1, x21
        mov     x3, x19
        mov     w6, #0x0
        bl      L47a0
        mov     w20, w0
L4f40:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e80
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4f88
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret
L4f80:
        mov     w20, #0xfffffff7
        b       L4f40
L4f88:
        bl      L0e70
        nop

// mldsa44_signature_pre_hash_internal (0xd0 bytes)
L4f90:
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
        cbnz    w7, L5014
L4fc0:
        mov     w21, #0xfffffff7
L4fc4:
        mov     x0, x20
        mov     x2, #0x974
        mov     w1, #0x0
        bl      L0e80
L4fd4:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e80
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L505c
        ldr     x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #416
        ret
L5014:
        mov     x21, x5
        mov     x22, x6
        mov     w5, w7
        mov     x0, x19
        bl      L4c20
        cbz     x0, L4fc0
        mov     x5, x21
        mov     x2, x0
        mov     x6, x22
        mov     x1, x19
        mov     x0, x20
        mov     w7, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L41f0
        mov     w21, w0
        cbz     w0, L4fd4
        b       L4fc4
L505c:
        bl      L0e70

// mldsa44_signature_pre_hash_shake256 (0xbc bytes)
L5060:
        stp     x19, x20, [sp, #-160]!
        mov     x8, x2
        mov     x2, x1
        .inst   0xd00000c7  // adrp x7, 0x1f000
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
        bl      L12b4
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x0, x20
        mov     x1, x19
        mov     w7, #0xc
        mov     x2, #0x40
        bl      L4f90
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xd00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #152]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L5118
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret
L5118:
        bl      L0e70
        nop

// mldsa44_verify_pre_hash_internal (0xbc bytes)
L5120:
        stp     x19, x20, [sp, #-400]!
        .inst   0xd00000c7  // adrp x7, 0x1f000
        ldr     x7, [x7, #4088]
        str     x30, [sp, #24]
        add     x19, sp, #0x3f
        ldr     x8, [x7]
        str     x8, [sp, #392]
        mov     x8, #0x0
        and     x19, x19, #0xffffffffffffffe0
        cbz     w6, L51cc
        mov     x20, x0
        mov     x0, x19
        str     x21, [sp, #16]
        mov     x21, x5
        mov     w5, w6
        bl      L4c20
        mov     x2, x0
        cbz     x0, L51c8
        mov     x5, x21
        mov     x0, x20
        mov     x1, x19
        mov     w6, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L47a0
        mov     w20, w0
        ldr     x21, [sp, #16]
L518c:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e80
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #392]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L51d4
        ldr     x30, [sp, #24]
        mov     w0, w20
        ldp     x19, x20, [sp], #400
        ret
L51c8:
        ldr     x21, [sp, #16]
L51cc:
        mov     w20, #0xfffffff7
        b       L518c
L51d4:
        str     x21, [sp, #16]
        bl      L0e70
        nop

// mldsa44_verify_pre_hash_shake256 (0xac bytes)
L51e0:
        stp     x19, x20, [sp, #-144]!
        mov     x7, x2
        mov     x2, x1
        .inst   0xd00000c6  // adrp x6, 0x1f000
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
        bl      L12b4
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x0, x20
        mov     x1, x19
        mov     w6, #0xc
        mov     x2, #0x40
        bl      L5120
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xd00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #136]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L5288
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #144
        ret
L5288:
        bl      L0e70
        nop

// mldsa44_pk_from_sk (0x320 bytes)
L5290:
        mov     x12, #0x1bd0
        sub     sp, sp, x12
        .inst   0xd00000c4  // adrp x4, 0x1f000
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
        bl      L3a34
        mov     w1, #0x3
        mov     x0, x19
        bl      L38a0
        mov     x2, x26
        mov     w1, #0x3
        mov     w25, w0
        mov     x0, x28
        bl      L3980
        mov     w27, w0
        mov     x0, x19
        bl      L37f0
        ldp     q0, q1, [x22]
        mov     x3, x28
        mov     x4, x23
        mov     x1, x24
        mov     x2, x19
        add     x0, x21, #0x20
        stp     q0, q1, [x21]
        bl      L3ca0
        mov     w22, w0
        cbz     w0, L5440
        mov     x6, #0x1a80
        mov     x7, #0x1ac0
        add     x28, x19, x6
        add     x20, x19, x7
L5390:
        mov     x0, x21
        mov     x2, #0x520
        mov     w1, #0x0
        bl      L0e80
L53a0:
        mov     x0, x24
        mov     x2, #0x680
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x400
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x1000
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e80
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
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #7112]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L55ac
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
L5440:
        movi    v1.4s, #0x0
        add     x20, x20, #0x380
        mov     x0, x24
        add     x1, x24, #0x680
        mov     v2.16b, v1.16b
        nop
L5458:
        ldr     q0, [x20], #16
        ldr     q3, [x0], #16
        eor     v0.16b, v0.16b, v3.16b
        orr     v2.16b, v2.16b, v0.16b
        eor     v1.16b, v1.16b, v0.16b
        cmp     x1, x0
        b.ne    L5458
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
        bl      L12b4
        movi    v0.4s, #0x0
        ldr     w4, [sp, #108]
        mov     x0, x28
        add     x2, x28, #0x40
        mov     x1, x20
        mov     v2.16b, v0.16b
L5514:
        ldr     q1, [x0], #16
        ldr     q3, [x1], #16
        eor     v1.16b, v1.16b, v3.16b
        orr     v2.16b, v2.16b, v1.16b
        eor     v0.16b, v0.16b, v1.16b
        cmp     x0, x2
        b.ne    L5514
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
        b.eq    L53a0
        mov     w22, #0xfffffff9
        b       L5390
L55ac:
        bl      L0e70

// mldsa65_unpack_pk_t1 (0x14 bytes)
L55b0:
        add     w2, w2, w2, lsl #2
        lsl     w2, w2, #6
        add     x2, x2, #0x20
        add     x1, x1, x2
        b       L28c0

// mldsa65_pack_sk_rho_key_tr (0x28 bytes)
L55c4:
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

// mldsa65_unpack_sk (0xb4 bytes)
L55f0:
        stp     x19, x20, [sp, #-64]!
        add     x7, x6, #0x40
        mov     x20, x3
        stp     x21, x22, [sp, #16]
        mov     x21, x6
        mov     x6, x1
        stp     x23, x24, [sp, #32]
        add     x1, x21, #0x80
        mov     x24, x5
        stp     x25, x30, [sp, #48]
        mov     x23, x3
        mov     x25, x4
        ldp     q0, q1, [x21]
        add     x19, x21, #0x600
        add     x22, x21, #0xfc0
        stp     q0, q1, [x0]
        mov     x0, x4
        ldp     q0, q1, [x21, #32]
        stp     q0, q1, [x2]
        ldp     q0, q1, [x7]
        stp     q0, q1, [x6]
        ldp     q0, q1, [x7, #32]
        stp     q0, q1, [x6, #32]
        bl      L6550
        mov     x0, x25
        bl      L62b0
        add     x1, x21, #0x300
        mov     x0, x24
        bl      L65d0
        mov     x0, x24
        bl      L6410
        nop
L5670:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x1a0
        bl      L2a60
        add     x20, x20, #0x400
        cmp     x19, x22
        b.ne    L5670
        ldp     x21, x22, [sp, #16]
        mov     x0, x23
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        b       L6410

// mldsa65_pack_sig_c (0x14 bytes)
L56a4:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ldr     q0, [x1, #32]
        str     q0, [x0, #32]
        ret
        nop
        nop

// mldsa65_pack_sig_h (0xec bytes)
L56c0:
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
L5714:
        mov     x1, x28
        mov     x0, x20
        bl      L2ce4
        mov     x4, #0x0
        b       L5740
L5728:
        cmp     w7, #0x0
        ccmp    w5, w27, #0x0, ne
        b.eq    L5754
        add     x4, x4, #0x1
        cmp     x4, #0x100
        b.eq    L5770
L5740:
        ldr     w5, [x21, x4, lsl #2]
        ldr     w7, [x20, x4, lsl #2]
        add     w6, w5, w25
        cmp     w6, w22
        b.ls    L5728
L5754:
        cmp     w19, #0x37
        b.eq    L578c
        strb    w4, [x26, w19, uxtw]
        add     x4, x4, #0x1
        add     w19, w19, #0x1
        cmp     x4, #0x100
        b.ne    L5740
L5770:
        add     x28, x28, #0x80
        strb    w19, [x23], #1
        add     x21, x21, #0x400
        cmp     x28, x24
        b.ne    L5714
        mov     w0, #0x0
        b       L5790
L578c:
        mov     w0, #0xffffffff
L5790:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #96
        ret
        nop

// mldsa65_pack_sig_z (0x14 bytes)
L57b0:
        add     w2, w2, w2, lsl #2
        lsl     w2, w2, #7
        add     x2, x2, #0x30
        add     x0, x0, x2
        b       L5ed0

// mldsa65_sig_unpack_hints (0x100 bytes)
L57c4:
        stp     x19, x20, [sp, #-48]!
        mov     x6, x0
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        add     x22, x1, #0xcb0
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        mov     w23, w2
        cbz     w2, L57f0
        add     w0, w2, #0x36
        ldrb    w21, [x22, w0, uxtw]
L57f0:
        add     w0, w23, #0x37
        ldrb    w20, [x22, w0, uxtw]
        cmp     w20, #0x37
        ccmp    w21, w20, #0x2, ls
        b.hi    L5864
        mov     x0, x6
        mov     w1, #0x0
        mov     x2, #0x400
        bl      L0e80
        add     x3, x19, w21, uxtb
        mov     x6, x0
        mov     w1, w21
        mov     w7, #0x1
        cmp     w21, w20
        b.cs    L5878
        nop
L5830:
        ldrb    w4, [x3, #3248]
        mov     w5, w1
        add     w1, w1, #0x1
        add     x3, x3, #0x1
        str     w7, [x6, x4, lsl #2]
        cmp     w20, w1
        b.ls    L5878
        cmp     w21, w1
        b.cs    L5830
        ldrb    w0, [x22, w5, uxtw]
        ldrb    w4, [x3, #3248]
        cmp     w4, w0
        b.hi    L5830
L5864:
        mov     w0, #0xffffffff
L5868:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L5878:
        cmp     w23, #0x5
        b.eq    L5894
L5880:
        mov     w0, #0x0
L5884:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L5894:
        cmp     w20, #0x37
        b.eq    L5880
        ldrb    w0, [x22, x20]
        add     x20, x20, #0x1
        cbnz    w0, L5864
L58a8:
        cmp     w20, #0x37
        b.eq    L5884
        ldrb    w0, [x22, x20]
        add     x20, x20, #0x1
        cbz     w0, L58a8
        mov     w0, #0xffffffff
        b       L5868
        nop
        nop
        nop

// mld_rej_eta_c65.constprop.0 (0x88 bytes)
L58d0:
        mov     x9, x0
        mov     w0, w1
        cmp     w1, #0xff
        b.hi    L5954
        mov     w10, #0x1
        sub     w10, w10, w2
        mov     w5, #0x4
        nop
L58f0:
        ldrb    w4, [x2]
        add     w6, w10, w2
        add     x2, x2, #0x1
        and     w1, w4, #0xf
        lsr     w4, w4, #4
        sub     w7, w5, w1
        sub     w8, w5, w4
        cmp     w1, #0x8
        b.hi    L591c
        str     w7, [x9, w0, uxtw #2]
        add     w0, w0, #0x1
L591c:
        cmp     w0, #0xff
        add     w7, w0, #0x1
        cset    w1, ls
        cmp     w1, #0x0
        ccmp    w4, #0x8, #0x2, ne
        b.hi    L5944
        cmp     w7, #0xff
        str     w8, [x9, w0, uxtw #2]
        cset    w1, ls
        mov     w0, w7
L5944:
        cmp     w6, w3
        cset    w4, cc
        tst     w1, w4
        b.ne    L58f0
L5954:
        ret
        nop
        nop

// mldsa65_poly_decompose (0x64 bytes)
L5960:
        mov     x5, #0x0
        mov     w7, #0x3ff000
        mov     w6, #0xff801fff
        nop
L5970:
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
        b.ne    L5970
        ret

// mldsa65_poly_use_hint (0x7c bytes)
L59c4:
        mov     x6, #0x0
        mov     w10, #0x3ff000
        mov     w9, #0xff801fff
L59d0:
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
        cbz     w4, L5a2c
        csel    w2, w8, w7, le
L5a2c:
        str     w2, [x0, x6]
        add     x6, x6, #0x4
        cmp     x6, #0x400
        b.ne    L59d0
        ret

// mldsa65_poly_uniform_eta_4x (0x26c bytes)
L5a40:
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
        bl      L16c0
        mov     x4, x21
        mov     x3, x20
        mov     x2, x19
        mov     x1, x28
        mov     x0, x26
        mov     x5, #0x42
        bl      L15d0
        mov     x5, x26
        mov     x4, #0x2
        mov     x3, x23
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L1634
        ldr     x0, [sp, #104]
        mov     w3, #0x110
        mov     x2, x22
        mov     w1, #0x0
        bl      L58d0
        mov     w19, w0
        ldr     x0, [sp, #112]
        mov     x2, x25
        mov     w1, #0x0
        bl      L58d0
        mov     w20, w0
        ldr     x0, [sp, #120]
        mov     x2, x24
        mov     w1, #0x0
        bl      L58d0
        mov     w21, w0
        ldr     x0, [sp, #128]
        mov     w1, #0x0
        mov     x2, x23
        bl      L58d0
        mov     w28, w0
        cmp     w21, w27
        ccmp    w0, w27, #0x0, hi
        cset    w0, ls
        cmp     w20, w27
        ccmp    w19, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbz     w0, L5c40
L5bb0:
        mov     x5, x26
        mov     x4, #0x1
        mov     x3, x23
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L1634
        ldr     x0, [sp, #104]
        mov     w3, #0x88
        mov     w1, w19
        mov     x2, x22
        bl      L58d0
        mov     w19, w0
        ldr     x0, [sp, #112]
        mov     w1, w20
        mov     x2, x25
        bl      L58d0
        mov     w20, w0
        ldr     x0, [sp, #120]
        mov     w1, w21
        mov     x2, x24
        bl      L58d0
        mov     w21, w0
        ldr     x0, [sp, #128]
        mov     w1, w28
        mov     x2, x23
        bl      L58d0
        cmp     w0, #0xff
        ccmp    w21, w27, #0x0, hi
        mov     w28, w0
        cset    w0, ls
        cmp     w19, #0xff
        ccmp    w20, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbnz    w0, L5bb0
L5c40:
        mov     x0, x26
        bl      L16c4
        mov     x0, x22
        mov     x2, #0x480
        mov     w1, #0x0
        bl      L0e80
        ldr     x19, [sp, #136]
        mov     x2, #0x180
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #2504]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L5ca8
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x9d0
        ret
L5ca8:
        bl      L0e70
        nop

// mldsa65_poly_challenge (0x168 bytes)
L5cb0:
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
        bl      L10a4
        mov     x1, x19
        mov     x2, #0x30
        mov     x0, x21
        bl      L10d0
        mov     x0, x21
        bl      L1160
        mov     x2, x21
        mov     x0, x20
        mov     x1, #0x88
        bl      L11e0
        mov     x2, x20
        mov     w0, #0x0
        mov     x3, #0x0
L5d20:
        ldrb    w1, [x2], #1
        lsl     x1, x1, x0
        add     w0, w0, #0x8
        orr     x3, x3, x1
        cmp     w0, #0x40
        b.ne    L5d20
        mov     x0, x23
        mov     x2, #0x400
        mov     w1, #0x0
        str     x3, [sp, #56]
        bl      L0e80
        mov     x19, #0xcf
        mov     w22, #0x1
        mov     w0, #0x8
        b       L5d6c
L5d5c:
        ldrb    w1, [x20, w0, uxtw]
        add     w0, w0, #0x1
        cmp     w1, w19
        b.ls    L5d94
L5d6c:
        cmp     w0, #0x88
        b.ne    L5d5c
        mov     x0, x20
        mov     x1, #0x88
        mov     x2, x21
        bl      L11e0
        ldrb    w1, [x20]
        mov     w0, #0x1
        cmp     w1, w19
        b.hi    L5d5c
L5d94:
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
        b.ne    L5d6c
        mov     x0, x21
        bl      L1290
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
        b.ne    L5e14
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #448
        ret
L5e14:
        bl      L0e70
        nop
        nop

// mldsa65_polyeta_pack (0x74 bytes)
L5e20:
        .inst   0xd00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        add     x5, x1, #0x400
        mov     w4, #0x4
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
L5e40:
        ldr     w2, [x1, #4]
        ldr     w3, [x1], #8
        sub     w2, w4, w2
        sub     w3, w4, w3
        ubfiz   w2, w2, #4, #8
        orr     w2, w2, w3
        strb    w2, [x0], #1
        cmp     x5, x1
        b.ne    L5e40
        add     x0, sp, #0x10
        str     xzr, [sp, #16]
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L5e90
        ldr     x30, [sp], #32
        ret
L5e90:
        bl      L0e70

// mldsa65_polyeta_unpack (0x3c bytes)
L5e94:
        add     x5, x0, #0x400
        mov     w4, #0x4
        nop
L5ea0:
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
        b.ne    L5ea0
        ret

// mldsa65_polyz_pack (0x94 bytes)
L5ed0:
        .inst   0xd00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-48]!
        add     x7, x0, #0x280
        mov     w5, #0x80000
        ldr     x3, [x2]
        str     x3, [sp, #40]
        mov     x3, #0x0
L5ef0:
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
        b.ne    L5ef0
        add     x0, sp, #0x18
        stp     xzr, xzr, [sp, #24]
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #40]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L5f60
        ldr     x30, [sp], #48
        ret
L5f60:
        bl      L0e70

// mldsa65_polyz_unpack (0x74 bytes)
L5f64:
        add     x6, x1, #0x280
        mov     w5, #0x80000
        nop
L5f70:
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
        b.ne    L5f70
        ret
        nop
        nop

// mldsa65_poly_uniform_gamma1 (0xe4 bytes)
L5fe0:
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
        bl      L10a4
        mov     x1, x19
        mov     x2, #0x42
        mov     x0, x21
        bl      L10d0
        mov     x0, x21
        bl      L1160
        mov     x2, x21
        mov     x0, x20
        mov     x1, #0x2a8
        bl      L11e0
        mov     x1, x20
        mov     x0, x22
        bl      L5f64
        mov     x0, x21
        bl      L1290
        mov     x0, x20
        mov     x2, #0x2a8
        mov     w1, #0x0
        bl      L0e80
        movi    v0.4s, #0x0
        strh    wzr, [x19, #64]
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1064]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L60c0
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        add     sp, sp, #0x430
        ret
L60c0:
        bl      L0e70

// mldsa65_poly_uniform_gamma1_4x (0x18c bytes)
L60c4:
        mov     x12, #0x1040
        sub     sp, sp, x12
        mov     x8, x4
        .inst   0xb00000c9  // adrp x9, 0x1f000
        ldr     x9, [x9, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x9f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        add     x20, x19, #0xb00
        stp     x23, x24, [sp, #32]
        add     x22, x19, #0xb60
        add     x23, x19, #0xbc0
        stp     x25, x26, [sp, #48]
        add     x21, sp, #0xd18
        mov     x24, x1
        stp     x27, x28, [sp, #64]
        mov     x25, x0
        mov     x0, x21
        str     x30, [sp, #80]
        add     x26, x19, #0x840
        add     x27, x19, #0x580
        add     x28, x19, #0x2c0
        ldp     q0, q1, [x4, #32]
        add     x4, x19, #0xc20
        ldp     q2, q3, [x8]
        mov     x8, x9
        ldr     x9, [x8]
        str     x9, [sp, #4152]
        mov     x9, #0x0
        ldrh    w8, [sp, #4160]
        stp     q0, q1, [x20, #32]
        stp     q0, q1, [x22, #32]
        stp     x2, x3, [sp, #104]
        stp     q2, q3, [x20]
        stp     q2, q3, [x22]
        stp     q2, q3, [x23]
        stp     q0, q1, [x23, #32]
        stp     q2, q3, [x4]
        stp     q0, q1, [x4, #32]
        str     x4, [sp, #120]
        strh    w5, [x19, #2880]
        strh    w6, [x19, #2976]
        strh    w7, [x19, #3072]
        strh    w8, [x19, #3168]
        bl      L16c0
        ldr     x4, [sp, #120]
        mov     x3, x23
        mov     x2, x22
        mov     x1, x20
        mov     x0, x21
        mov     x5, #0x42
        bl      L15d0
        mov     x3, x26
        mov     x2, x27
        mov     x5, x21
        mov     x4, #0x5
        mov     x1, x28
        mov     x0, x19
        bl      L1634
        mov     x1, x19
        mov     x0, x25
        bl      L5f64
        mov     x1, x28
        mov     x0, x24
        bl      L5f64
        ldr     x0, [sp, #104]
        mov     x1, x27
        bl      L5f64
        ldr     x0, [sp, #112]
        mov     x1, x26
        bl      L5f64
        mov     x0, x21
        bl      L16c4
        mov     x0, x19
        mov     x2, #0xb00
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x180
        mov     x0, x20
        mov     w1, #0x0
        bl      L0e80
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4152]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L624c
        ldp     x19, x20, [sp]
        mov     x12, #0x1040
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret
L624c:
        bl      L0e70

// mldsa65_polyvecl_uniform_gamma1 (0x5c bytes)
L6250:
        sub     sp, sp, #0x30
        mov     x4, x1
        mov     w5, w2
        stp     x19, x20, [sp, #16]
        sxth    w19, w2
        add     w3, w19, #0x3
        strh    w3, [sp]
        add     w7, w19, #0x2
        add     w6, w19, #0x1
        mov     x20, x0
        add     x3, x0, #0xc00
        add     x2, x0, #0x800
        stp     x21, x30, [sp, #32]
        mov     x21, x1
        add     x1, x0, #0x400
        bl      L60c4
        add     w2, w19, #0x4
        mov     x1, x21
        ldp     x21, x30, [sp, #32]
        add     x0, x20, #0x1, lsl #12
        ldp     x19, x20, [sp, #16]
        add     sp, sp, #0x30
        b       L5fe0
        nop

// mldsa65_polyvecl_ntt (0x38 bytes)
L62b0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1400
        add     x20, x19, x0
        str     x30, [sp, #16]
        nop
L62c8:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L22d0
        cmp     x19, x20
        b.ne    L62c8
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop
        nop

// mldsa65_polyvecl_pointwise_acc_montgomery (0x84 bytes)
L62f0:
        mov     x7, x0
        .inst   0x90000020  // adrp x0, 0xa000
        mov     x5, x2
        mov     x6, x1
        ldr     q5, [x0, #4048]
        .inst   0x90000020  // adrp x0, 0xa000
        mov     x1, #0x0
        mov     x4, #0x1400
        ldr     q4, [x0, #4016]
        nop
L6318:
        add     x3, x5, x1
        movi    v1.4s, #0x0
        add     x2, x6, x1
        mov     x0, #0x0
        mov     v0.16b, v1.16b
        nop
L6330:
        ldr     q2, [x2, x0]
        ldr     q3, [x3, x0]
        add     x0, x0, #0x400
        smlal   v0.2d, v3.2s, v2.2s
        smlal2  v1.2d, v3.4s, v2.4s
        cmp     x0, x4
        b.ne    L6330
        uzp1    v2.4s, v0.4s, v1.4s
        mul     v2.4s, v2.4s, v5.4s
        smlal   v0.2d, v2.2s, v4.2s
        smlal2  v1.2d, v2.4s, v4.4s
        uzp2    v0.4s, v0.4s, v1.4s
        str     q0, [x7, x1]
        add     x1, x1, #0x10
        cmp     x1, #0x400
        b.ne    L6318
        ret

// mldsa65_polyvecl_chknorm (0x54 bytes)
L6374:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x0, #0x1400
        stp     x21, x22, [sp, #16]
        mov     w21, w1
        add     x22, x19, x0
        mov     w20, #0x0
        str     x30, [sp, #32]
        nop
L6398:
        mov     x0, x19
        mov     w1, w21
        add     x19, x19, #0x400
        bl      L2bb4
        orr     w20, w20, w0
        cmp     x19, x22
        b.ne    L6398
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
        nop
        nop

// mldsa65_polyveck_caddq (0x38 bytes)
L63d0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1800
        add     x20, x19, x0
        str     x30, [sp, #16]
        nop
L63e8:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L2210
        cmp     x19, x20
        b.ne    L63e8
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop
        nop

// mldsa65_polyveck_ntt (0x38 bytes)
L6410:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1800
        add     x20, x19, x0
        str     x30, [sp, #16]
        nop
L6428:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L22d0
        cmp     x19, x20
        b.ne    L6428
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop
        nop

// mldsa65_polyveck_invntt_tomont (0x38 bytes)
L6450:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1800
        add     x20, x19, x0
        str     x30, [sp, #16]
        nop
L6468:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L23a0
        cmp     x19, x20
        b.ne    L6468
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop
        nop

// mldsa65_polyveck_unpack_eta_chknorm (0x5c bytes)
L6490:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x20, x2
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        add     x23, x0, #0x300
L64b0:
        mov     x1, x19
        mov     x0, x20
        bl      L5e94
        mov     w1, w22
        mov     x0, x20
        add     x19, x19, #0x80
        bl      L2bb4
        orr     w21, w21, w0
        cmp     x19, x23
        b.ne    L64b0
        ldp     x23, x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret
        nop

// mldsa65_polyveck_decompose_pack_w1 (0x58 bytes)
L64f0:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x0
        mov     x19, x1
        mov     x0, #0x1800
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x22, x1, x0
        str     x30, [sp, #32]
L6510:
        mov     x1, x19
        mov     x0, x21
        bl      L5960
        add     x19, x19, #0x400
        mov     x0, x20
        mov     x1, x21
        bl      L2c60
        add     x20, x20, #0x80
        cmp     x19, x22
        b.ne    L6510
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
        nop
        nop

// mldsa65_polyvecl_unpack_eta (0x40 bytes)
L6550:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1400
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L6568:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L5e94
        add     x20, x20, #0x80
        cmp     x19, x21
        b.ne    L6568
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyvecl_unpack_z (0x40 bytes)
L6590:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x30, [sp, #16]
        add     x21, x1, #0xc80
        nop
L65a8:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x280
        bl      L5f64
        add     x20, x20, #0x400
        cmp     x19, x21
        b.ne    L65a8
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyveck_unpack_eta (0x40 bytes)
L65d0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        mov     x0, #0x1800
        stp     x21, x30, [sp, #16]
        add     x21, x19, x0
L65e8:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L5e94
        add     x20, x20, #0x80
        cmp     x19, x21
        b.ne    L65e8
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa65_polyvec_matrix_expand_eager (0x18c bytes)
L6610:
        stp     x19, x20, [sp, #-336]!
        .inst   0xb00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        stp     x23, x30, [sp, #32]
        add     x23, sp, #0x4f
        and     x23, x23, #0xffffffffffffffe0
        add     x2, x23, #0x100
        mov     x0, x23
        ldr     x4, [x3]
        str     x4, [sp, #328]
        mov     x4, #0x0
L6644:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        add     x0, x0, #0x40
        cmp     x2, x0
        b.ne    L6644
        mov     w20, #0xcccd
        mov     w19, #0x4
        movk    w20, #0xcccc, lsl #16
        mov     w22, #0x5
L6668:
        sub     w0, w19, #0x4
        mov     x3, x23
        mov     w2, w0
L6674:
        umull   x1, w2, w20
        add     x3, x3, #0x40
        lsr     x1, x1, #34
        sturb   w1, [x3, #-31]
        add     w1, w1, w1, lsl #2
        sub     w1, w2, w1
        add     w2, w2, #0x1
        sturb   w1, [x3, #-32]
        cmp     w19, w2
        b.ne    L6674
        sub     w8, w19, #0x3
        sub     w7, w19, #0x2
        sub     w6, w19, #0x1
        umull   x5, w0, w20
        add     w19, w19, #0x4
        mov     x4, x23
        umull   x1, w8, w20
        umull   x2, w7, w20
        lsr     x5, x5, #34
        umull   x3, w6, w20
        lsr     x1, x1, #34
        add     w9, w5, w5, lsl #2
        lsr     x2, x2, #34
        sub     w0, w0, w9
        lsr     x3, x3, #34
        add     w9, w1, w1, lsl #2
        add     w10, w2, w2, lsl #2
        sub     w8, w8, w9
        add     w9, w3, w3, lsl #2
        sub     w7, w7, w10
        sub     w6, w6, w9
        umaddl  x0, w5, w22, x0
        umaddl  x1, w1, w22, x8
        umaddl  x2, w2, w22, x7
        umaddl  x3, w3, w22, x6
        add     x0, x21, x0, lsl #10
        add     x1, x21, x1, lsl #10
        add     x2, x21, x2, lsl #10
        add     x3, x21, x3, lsl #10
        bl      L2654
        cmp     w19, #0x20
        b.ne    L6668
        mov     w2, #0x503
        mov     x1, x23
        add     x0, x21, #0x7, lsl #12
        strh    w2, [x23, #32]
        bl      L2550
        mov     w2, #0x504
        mov     x1, x23
        mov     x0, #0x7400
        add     x0, x21, x0
        strh    w2, [x23, #32]
        bl      L2550
        movi    v0.4s, #0x0
        stp     q0, q0, [x23]
        stp     q0, q0, [x23, #32]
        stp     q0, q0, [x23, #64]
        stp     q0, q0, [x23, #96]
        stp     q0, q0, [x23, #128]
        stp     q0, q0, [x23, #160]
        stp     q0, q0, [x23, #192]
        stp     q0, q0, [x23, #224]
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #328]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L6798
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #336
        ret
L6798:
        bl      L0e70
        nop

// mldsa65_polyvec_matrix_pointwise_montgomery_row_eager (0xc bytes)
L67a0:
        mov     w4, #0x1400
        umaddl  x1, w3, w4, x1
        b       L62f0
        nop

// mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager (0x70 bytes)
L67b0:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x0
        mov     w19, #0x0
        stp     x21, x22, [sp, #16]
        mov     x22, x1
        mov     x1, x2
        mov     x2, #0x1400
        mov     x21, x3
        stp     x23, x30, [sp, #32]
        mov     x23, x0
        mov     x0, x3
        bl      L0e50
        mov     x0, x21
        bl      L62b0
L67e8:
        mov     w3, w19
        mov     x0, x20
        mov     x2, x21
        mov     x1, x22
        add     w19, w19, #0x1
        bl      L67a0
        add     x20, x20, #0x400
        cmp     w19, #0x6
        b.ne    L67e8
        ldp     x21, x22, [sp, #16]
        mov     x0, x23
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        b       L6450

// mld_compute_pack_t0_t165 (0x16c bytes)
L6820:
        mov     x12, #0x8070
        sub     sp, sp, x12
        stp     x21, x22, [sp, #16]
        mov     x22, x3
        mov     w21, #0x0
        .inst   0xb00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x25, x26, [sp, #48]
        add     x26, sp, #0x6f
        and     x26, x26, #0xffffffffffffffe0
        stp     x19, x20, [sp]
        mov     x25, x0
        stp     x23, x24, [sp, #32]
        mov     x24, x1
        mov     x1, #0x7800
        str     x30, [sp, #64]
        add     x20, x26, x1
        mov     x1, x4
        add     x4, sp, #0x8, lsl #12
        mov     x23, x2
        ldr     x2, [x3]
        str     x2, [x4, #104]
        mov     x2, #0x0
        mov     x0, #0x7c00
        add     x19, x26, x0
        mov     x0, x26
        bl      L6610
        nop
L6890:
        mov     w3, w21
        mov     x2, x23
        mov     x1, x26
        mov     x0, x19
        bl      L67a0
        add     w21, w21, #0x1
        mov     x0, x19
        bl      L23a0
        mov     x1, x22
        mov     x0, x20
        bl      L5e94
        add     x22, x22, #0x80
        mov     x1, x20
        mov     x0, x19
        bl      L2250
        mov     x0, x19
        bl      L21e0
        mov     x0, x19
        bl      L2210
        mov     x2, x19
        mov     x1, x19
        mov     x0, x20
        bl      L2510
        mov     x0, x25
        mov     x1, x20
        bl      L2864
        add     x25, x25, #0x140
        mov     x0, x24
        mov     x1, x19
        bl      L2934
        add     x24, x24, #0x1a0
        cmp     w21, #0x6
        b.ne    L6890
        mov     x0, x20
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x400
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x7800
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e80
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0x8, lsl #12
        ldr     x3, [x2, #104]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.ne    L6988
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x8070
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        add     sp, sp, x12
        ret
L6988:
        bl      L0e70
        nop

// mld_H65 (0x10c bytes)
L6990:
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
        bl      L10a4
        mov     x2, x25
        mov     x1, x24
        mov     x0, x19
        bl      L10d0
        cbnz    x21, L6a70
        cbnz    x20, L6a84
L69fc:
        mov     x0, x19
        bl      L1160
        mov     x2, x19
        mov     x1, x23
        mov     x0, x22
        bl      L11e0
        mov     x0, x19
        bl      L1290
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
        b.ne    L6a98
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #304
        ret
L6a70:
        mov     x2, x21
        mov     x1, x26
        mov     x0, x19
        bl      L10d0
        cbz     x20, L69fc
L6a84:
        mov     x2, x20
        mov     x1, x27
        mov     x0, x19
        bl      L10d0
        b       L69fc
L6a98:
        bl      L0e70
        nop

// mldsa65_keypair_internal (0x2a0 bytes)
L6aa0:
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
        bl      L12b4
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
        bl      L5a40
        mov     x1, x19
        add     x0, x20, #0x400
        bl      L5e20
        mov     x1, x24
        add     x0, x20, #0x480
        bl      L5e20
        mov     x1, x25
        add     x0, x20, #0x500
        bl      L5e20
        mov     x1, x26
        add     x0, x20, #0x580
        bl      L5e20
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
        bl      L5a40
        mov     x1, x28
        add     x0, x20, #0x280
        add     x28, x20, #0x300
        bl      L5e20
        mov     x1, x19
        mov     x0, x28
        bl      L5e20
        mov     x1, x24
        add     x0, x20, #0x380
        bl      L5e20
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
        bl      L5a40
        mov     x1, x19
        add     x0, x20, #0x80
        bl      L5e20
        mov     x1, x24
        add     x0, x20, #0x100
        bl      L5e20
        mov     x1, x25
        add     x0, x20, #0x180
        bl      L5e20
        mov     x1, x26
        add     x0, x20, #0x200
        bl      L5e20
        mov     x0, x19
        bl      L62b0
        ldp     q0, q1, [x21]
        mov     x3, x28
        mov     x4, x21
        mov     x2, x19
        add     x1, x20, #0x600
        add     x0, x23, #0x20
        stp     q0, q1, [x23]
        bl      L6820
        mov     x5, #0x1480
        mov     w25, w0
        add     x24, x19, x5
        cbnz    w0, L6c98
        mov     x0, x24
        mov     x2, x23
        mov     x3, #0x7a0
        mov     x1, #0x40
        bl      L12b4
        mov     x2, x24
        add     x3, x21, #0x60
        mov     x1, x21
        mov     x0, x20
        bl      L55c4
L6c98:
        mov     x0, x19
        mov     x2, #0x1400
        mov     w1, #0x0
        bl      L0e80
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
        cbnz    w25, L6d18
L6cd4:
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #5496]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L6d3c
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
L6d18:
        mov     x0, x23
        mov     x2, #0x7a0
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0xfc0
        mov     x0, x20
        mov     w1, #0x0
        bl      L0e80
        b       L6cd4
L6d3c:
        bl      L0e70

// mldsa65_keypair (0x88 bytes)
L6d40:
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
        bl      L0e60
        cbnz    w0, L6dbc
        mov     x1, x21
        mov     x0, x20
        mov     x2, x19
        bl      L6aa0
L6d8c:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xb00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #88]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L6dc4
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #96
        ret
L6dbc:
        mov     w0, #0xfffffffd
        b       L6d8c
L6dc4:
        bl      L0e70
        nop
        nop

// mldsa65_signature_internal (0x510 bytes)
L6dd0:
        sub     sp, sp, #0x9c0
        mov     x12, #0xe800
        sub     sp, sp, #0x10, lsl #12
        mov     x13, #0xa800
        add     x8, sp, #0xbf
        and     x9, x8, #0xffffffffffffffe0
        add     x10, x9, #0x10, lsl #12
        add     x11, x9, #0x9, lsl #12
        add     x10, x10, #0x700
        add     x12, x9, x12
        .inst   0xb00000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        stp     x10, x9, [sp, #128]
        add     x9, x9, x13
        stp     x19, x20, [sp]
        mov     x20, x3
        mov     x3, x9
        stp     x21, x22, [sp, #16]
        mov     x19, x5
        mov     x22, x2
        stp     x23, x24, [sp, #32]
        mov     w24, w7
        mov     x23, x1
        stp     x25, x26, [sp, #48]
        add     x25, x10, #0x20
        mov     x21, x4
        stp     x27, x28, [sp, #64]
        mov     x1, x25
        mov     x26, x10
        str     x30, [sp, #80]
        add     x2, x10, #0x60
        str     x0, [sp, #96]
        mov     x5, x11
        str     x9, [sp, #104]
        add     x9, sp, #0x10, lsl #12
        stp     x12, x11, [sp, #144]
        add     x9, x9, #0x40
        mov     x4, x12
        ldr     x7, [x8]
        str     x7, [x9, #2424]
        mov     x7, #0x0
        mov     x0, x10
        bl      L55f0
        cbnz    w24, L72c0
        mov     x3, #0x40
        mov     x7, x22
        mov     x6, x23
        mov     x5, x21
        mov     x4, x20
        mov     x2, x25
        add     x0, x26, #0x80
        mov     x1, x3
        bl      L6990
L6ea4:
        ldp     x24, x22, [sp, #128]
        mov     x1, #0xd400
        mov     x4, x19
        mov     x5, #0x20
        mov     x8, #0x7800
        mov     x9, #0xfc00
        mov     x3, x5
        mov     x7, #0x40
        add     x21, sp, #0x10, lsl #12
        add     x6, x24, #0x80
        add     x2, x24, #0x60
        add     x27, x22, x1
        add     x1, x22, #0x10, lsl #12
        add     x1, x1, #0x400
        add     x0, x24, #0xc0
        add     x26, x22, x8
        add     x25, x22, #0x10, lsl #12
        add     x20, x22, x9
        str     x1, [sp, #120]
        mov     x1, x7
        bl      L6990
        add     x21, x21, #0x8e8
        add     x19, x22, #0xc, lsl #12
        add     x25, x25, #0x800
        add     x23, x22, #0x10, lsl #12
        mov     x1, x24
        mov     x0, x22
        str     wzr, [sp, #116]
        bl      L6610
L6f18:
        ldrh    w2, [sp, #116]
        mov     x0, x27
        ldr     x22, [sp, #128]
        add     x1, x22, #0xc0
        bl      L6250
        ldr     x1, [sp, #136]
        mov     x3, x19
        mov     x2, x27
        mov     x0, x26
        bl      L67b0
        mov     x0, x26
        bl      L63d0
        ldr     x24, [sp, #120]
        mov     x2, x19
        mov     x1, x26
        mov     x0, x24
        bl      L64f0
        mov     x0, x21
        bl      L10a4
        add     x1, x22, #0x80
        mov     x0, x21
        mov     x2, #0x40
        bl      L10d0
        mov     x1, x24
        mov     x2, #0x300
        mov     x0, x21
        bl      L10d0
        mov     x0, x21
        bl      L1160
        mov     x2, x21
        mov     x1, #0x30
        mov     x0, x25
        bl      L11e0
        mov     x0, x21
        bl      L1290
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x21, #64]
        stp     q0, q0, [x21, #96]
        stp     q0, q0, [x21, #128]
        stp     q0, q0, [x21, #160]
        str     q0, [x21, #192]
        mov     x1, x25
        mov     x0, x23
        ldr     x28, [sp, #144]
        bl      L5cb0
        mov     x24, x27
        mov     x0, x23
        mov     w22, #0x0
        bl      L22d0
L6fe4:
        mov     x2, #0x400
        mov     x1, x28
        mov     x0, x20
        bl      L0e50
        mov     x1, x23
        mov     x0, x20
        bl      L24c0
        mov     x0, x20
        bl      L23a0
        mov     x2, #0x400
        mov     x1, x24
        mov     x0, x19
        bl      L0e50
        mov     x1, x19
        mov     x0, x20
        bl      L2250
        mov     x0, x20
        bl      L21e0
        mov     w1, #0xff3c
        mov     x0, x20
        movk    w1, #0x7, lsl #16
        bl      L2bb4
        cbnz    w0, L72b8
        ldr     x0, [sp, #96]
        mov     w2, w22
        mov     x1, x20
        add     w22, w22, #0x1
        add     x28, x28, #0x400
        add     x24, x24, #0x400
        bl      L57b0
        cmp     w22, #0x5
        b.ne    L6fe4
        ldr     x28, [sp, #104]
        mov     x22, x26
        ldr     x24, [sp, #152]
L7070:
        mov     x2, #0x400
        mov     x1, x24
        mov     x0, x19
        bl      L0e50
        mov     x1, x23
        mov     x0, x19
        bl      L24c0
        mov     x0, x19
        bl      L23a0
        mov     x1, x19
        mov     x0, x22
        bl      L2280
        mov     x0, x22
        bl      L21e0
        mov     w1, #0xfe3c
        mov     x0, x22
        movk    w1, #0x3, lsl #16
        bl      L2bb4
        cbnz    w0, L72b8
        mov     x2, #0x400
        mov     x1, x28
        mov     x0, x19
        bl      L0e50
        mov     x1, x23
        mov     x0, x19
        bl      L24c0
        mov     x0, x19
        bl      L23a0
        mov     x0, x19
        bl      L21e0
        mov     x0, x19
        mov     w1, #0x3ff00
        bl      L2bb4
        cbnz    w0, L72b8
        mov     x0, x22
        mov     x1, x19
        bl      L2250
        add     x24, x24, #0x400
        ldr     x0, [sp, #104]
        add     x28, x28, #0x400
        add     x22, x22, #0x400
        cmp     x24, x0
        b.ne    L7070
        ldr     x22, [sp, #96]
        mov     x1, x25
        mov     x0, x22
        bl      L56a4
        ldr     x2, [sp, #120]
        mov     x0, x22
        mov     x3, x19
        mov     x1, x26
        bl      L56c0
        mov     w22, w0
L7144:
        mov     x0, x20
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x400
        mov     x0, x23
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x1800
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e80
        ldr     x24, [sp, #120]
        mov     x2, #0x300
        mov     w1, #0x0
        mov     x0, x24
        bl      L0e80
        mov     x2, #0x1400
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x1400
        mov     x0, x27
        mov     w1, #0x0
        bl      L0e80
        stp     xzr, xzr, [x25]
        stp     xzr, xzr, [x25, #16]
        stp     xzr, xzr, [x25, #32]
        cbz     w22, L71f4
        cmn     w22, #0x1
        b.ne    L71e0
        ldr     w0, [sp, #116]
        mov     w1, #0xfffa
        add     w0, w0, #0x5
        and     w2, w0, #0xffff
        str     w2, [sp, #116]
        cmp     w1, w0, uxth
        b.ne    L6f18
        mov     w22, #0xfffffffc
L71e0:
        ldr     x19, [sp, #96]
        mov     x2, #0xced
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
L71f4:
        ldr     x19, [sp, #152]
        mov     x2, #0x1800
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
        ldr     x19, [sp, #104]
        mov     x2, #0x1800
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
        ldr     x19, [sp, #144]
        mov     x2, #0x1400
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
        ldr     x19, [sp, #136]
        mov     x2, #0x7800
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
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
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0x10, lsl #12
        add     x2, x2, #0x40
        ldr     x3, [x2, #2424]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.ne    L72dc
        ldp     x19, x20, [sp]
        mov     w0, w22
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x9c0
        add     sp, sp, #0x10, lsl #12
        ret
L72b8:
        mov     w22, #0xffffffff
        b       L7144
L72c0:
        ldr     x0, [sp, #128]
        ldp     q2, q3, [x23]
        add     x0, x0, #0x80
        ldp     q0, q1, [x23, #32]
        stp     q2, q3, [x0]
        stp     q0, q1, [x0, #32]
        b       L6ea4
L72dc:
        bl      L0e70

// mldsa65_signature_extmu (0xa8 bytes)
L72e0:
        stp     x19, x20, [sp, #-112]!
        mov     x20, x0
        .inst   0x900000c3  // adrp x3, 0x1f000
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
        bl      L0e60
        cbnz    w0, L737c
        mov     x6, x22
        mov     x1, x21
        mov     x0, x20
        mov     x5, x19
        mov     w7, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        bl      L6dd0
L7348:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0x900000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #104]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L7384
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret
L737c:
        mov     w0, #0xfffffffd
        b       L7348
L7384:
        bl      L0e70
        nop
        nop

// mldsa65_verify_internal (0x4b4 bytes)
L7390:
        mov     x12, #0x9d20
        sub     sp, sp, x12
        stp     x19, x20, [sp]
        mov     x19, #0x9c00
        mov     x20, #0x7800
        stp     x21, x22, [sp, #16]
        add     x22, sp, #0x9f
        and     x22, x22, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        add     x23, x22, x19
        sub     x7, x23, #0x80
        stp     x25, x26, [sp, #48]
        mov     x25, x0
        mov     x26, #0x8020
        stp     x27, x28, [sp, #64]
        mov     x28, x1
        add     x1, sp, x26
        str     x30, [sp, #80]
        mov     x21, x2
        str     x5, [sp, #96]
        add     x27, x22, x20
        ldp     q1, q2, [x0]
        mov     x19, x3
        ldr     q0, [x0, #32]
        mov     x20, x4
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     w24, w6
        ldr     x2, [x0]
        str     x2, [x1, #7416]
        mov     x2, #0x0
        mov     x0, x27
        add     x1, x25, #0x30
        stp     q1, q2, [x7]
        str     q0, [x7, #32]
        bl      L6590
        mov     w1, #0xff3c
        mov     x0, x27
        movk    w1, #0x7, lsl #16
        bl      L6374
        cbnz    w0, L77f8
        mov     w26, w0
        cbz     w24, L7740
        ldp     q2, q3, [x28]
        sub     x0, x23, #0x100
        ldp     q0, q1, [x28, #32]
        mov     x8, #0x9800
        add     x1, x22, x8
        mov     x9, #0x9b00
        str     x1, [sp, #104]
        add     x1, x22, x9
        str     x1, [sp, #112]
        stp     q2, q3, [x0]
        stp     q0, q1, [x0, #32]
L7468:
        mov     x5, #0x9b80
        add     x1, x22, x5
        mov     x6, #0x9400
        mov     x19, x1
        add     x28, x22, x6
        mov     x0, x27
        str     x1, [sp, #120]
        bl      L62b0
        add     x20, x22, #0x9, lsl #12
        ldr     x1, [sp, #96]
        mov     x0, x22
        mov     w21, #0x0
        bl      L6610
        mov     x1, x19
        mov     x7, #0x8c00
        ldr     x24, [sp, #104]
        mov     x0, x28
        add     x19, x22, x7
        bl      L5cb0
        mov     x0, x28
        bl      L22d0
L74bc:
        mov     w3, w21
        mov     x2, x27
        mov     x1, x22
        mov     x0, x20
        bl      L67a0
        ldr     x1, [sp, #96]
        mov     w2, w21
        mov     x0, x19
        bl      L55b0
        mov     x0, x19
        bl      L22b0
        mov     x0, x19
        bl      L22d0
        mov     x1, x28
        mov     x0, x19
        bl      L24c0
        mov     x1, x19
        mov     x0, x20
        bl      L2280
        mov     x0, x20
        bl      L21e0
        mov     x0, x20
        bl      L23a0
        mov     x0, x20
        bl      L2210
        mov     w2, w21
        mov     x1, x25
        mov     x0, x19
        bl      L57c4
        mov     w23, w0
        cbnz    w0, L77e8
        mov     x1, x19
        mov     x0, x20
        bl      L59c4
        add     w21, w21, #0x1
        mov     x0, x24
        mov     x1, x20
        bl      L2c60
        add     x24, x24, #0x80
        cmp     w21, #0x6
        b.ne    L74bc
        mov     x3, #0x9b40
        mov     x2, #0x9c48
        add     x21, sp, x2
        add     x24, x22, x3
        mov     x0, x21
        bl      L10a4
        ldr     x1, [sp, #112]
        mov     x0, x21
        mov     x2, #0x40
        bl      L10d0
        ldr     x1, [sp, #104]
        mov     x2, #0x300
        mov     x0, x21
        bl      L10d0
        mov     x0, x21
        bl      L1160
        mov     x2, x21
        mov     x1, #0x30
        mov     x0, x24
        bl      L11e0
        mov     x0, x21
        bl      L1290
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
L75e4:
        ldr     q1, [x0], #16
        add     w26, w26, #0x1
        ldr     q3, [x1], #16
        eor     v1.16b, v1.16b, v3.16b
        orr     v2.16b, v2.16b, v1.16b
        eor     v0.16b, v0.16b, v1.16b
        cmp     w26, #0x3
        b.ne    L75e4
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
        b.ne    L77f0
L7664:
        mov     x0, x19
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x400
        mov     x0, x20
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x7800
        mov     x0, x22
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x400
        mov     x0, x28
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x1400
        mov     x0, x27
        mov     w1, #0x0
        bl      L0e80
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
        bl      L0e80
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     x1, #0x8020
        add     x2, sp, x1
        ldr     x3, [x2, #7416]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.ne    L7840
        ldp     x19, x20, [sp]
        mov     w0, w23
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x9d20
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret
L7740:
        mov     x10, #0x9c48
        mov     x11, #0x9800
        add     x23, sp, x10
        add     x24, x22, x11
        mov     x0, x23
        str     x24, [sp, #104]
        bl      L10a4
        ldr     x1, [sp, #96]
        mov     x2, #0x7a0
        mov     x0, x23
        bl      L10d0
        mov     x0, x23
        bl      L1160
        mov     x2, x23
        mov     x1, #0x40
        mov     x0, x24
        bl      L11e0
        mov     x0, x23
        bl      L1290
        movi    v0.4s, #0x0
        stp     q0, q0, [x23]
        stp     q0, q0, [x23, #32]
        stp     q0, q0, [x23, #64]
        stp     q0, q0, [x23, #96]
        stp     q0, q0, [x23, #128]
        stp     q0, q0, [x23, #160]
        str     q0, [x23, #192]
        mov     x12, #0x9b00
        mov     x3, #0x40
        add     x0, x22, x12
        mov     x7, x21
        mov     x6, x28
        mov     x5, x20
        mov     x4, x19
        mov     x2, x24
        mov     x1, x3
        str     x0, [sp, #112]
        bl      L6990
        movi    v0.4s, #0x0
        stp     q0, q0, [x24]
        stp     q0, q0, [x24, #32]
        b       L7468
L77e8:
        mov     x4, #0x9b40
        add     x24, x22, x4
L77f0:
        mov     w23, #0xfffffffa
        b       L7664
L77f8:
        mov     x13, #0x9800
        add     x0, x22, x13
        mov     x17, #0x9b00
        str     x0, [sp, #104]
        add     x0, x22, x17
        mov     x14, #0x9400
        mov     x15, #0x8c00
        mov     x16, #0x9b40
        mov     x18, #0x9b80
        add     x28, x22, x14
        add     x20, x22, #0x9, lsl #12
        add     x19, x22, x15
        add     x24, x22, x16
        mov     w23, #0xfffffffa
        str     x0, [sp, #112]
        add     x0, x22, x18
        str     x0, [sp, #120]
        b       L7664
L7840:
        bl      L0e70

// mldsa65_verify_extmu (0x18 bytes)
L7844:
        mov     x5, x2
        mov     w6, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        b       L7390
        nop

// mldsa65_prepare_domain_separation_prefix (0x19c bytes)
L7860:
        cmp     x4, #0xff
        b.hi    L78c0
        stp     x19, x21, [sp, #-64]!
        mov     x19, x4
        mov     x21, x0
        str     x30, [sp, #32]
        cbz     w5, L78a4
        stp     x22, x23, [sp, #16]
        mov     x23, x1
        sub     w1, w5, #0x1
        mov     x0, #0x0
        cmp     w1, #0xb
        b.ls    L78c8
        ldp     x22, x23, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
L78a4:
        strb    wzr, [x0]
        strb    w4, [x21, #1]
        cbnz    x4, L78e4
L78b0:
        add     x0, x19, #0x2
L78b4:
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
L78c0:
        mov     x0, #0x0
        ret
L78c8:
        .inst   0x90000020  // adrp x0, 0xb000
        mov     x22, x2
        add     x0, x0, #0x4b0
        ldrb    w0, [x0, w1, uxtw]
        .inst   0x10000061  // adr     x1, 78e4 <mldsa65_prepare_domain_separation_prefix+0x84>
        add     x0, x1, w0, sxtb #2
        br      x0
L78e4:
        mov     x1, x3
        mov     x2, x4
        add     x0, x0, #0x2
        bl      L0e50
        b       L78b0
        cmp     x2, #0x20
        b.ne    L7970
L7900:
        mov     w0, #0x1
        strb    w0, [x21]
        strb    w19, [x21, #1]
        cbnz    x19, L79e0
L7910:
        .inst   0x90000021  // adrp x1, 0xb000
        add     x4, x1, #0x4c0
        mov     w3, #0x0
        nop
L7920:
        ldr     w0, [x4]
        cmp     w5, w0
        b.eq    L7994
        add     w3, w3, #0x1
        add     x4, x4, #0x10
        cmp     w3, #0xc
        b.ne    L7920
        add     x0, x19, #0xd
        mov     x1, x23
        mov     x2, x22
        add     x0, x21, x0
        bl      L0e50
        add     x0, x22, #0xd
        ldp     x22, x23, [sp, #16]
        add     x0, x0, x19
L795c:
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
        cmp     x2, #0x1c
        b.eq    L7900
L7970:
        ldp     x22, x23, [sp, #16]
        mov     x0, #0x0
        b       L78b4
        cmp     x2, #0x40
        b.eq    L7900
        b       L7970
        cmp     x2, #0x30
        b.eq    L7900
        b       L7970
L7994:
        mov     x0, #0x4
        add     x1, x1, #0x4c0
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
        bl      L0e50
        add     x0, x22, #0xd
        ldp     x22, x23, [sp, #16]
        add     x0, x0, x19
        b       L795c
L79e0:
        mov     x1, x3
        mov     x2, x19
        add     x0, x21, #0x2
        str     w5, [sp, #60]
        bl      L0e50
        ldr     w5, [sp, #60]
        b       L7910
        nop

// mldsa65_signature (0x10c bytes)
L7a00:
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
        bl      L7860
        cbnz    x0, L7abc
        add     x22, x19, #0x160
        mov     w26, #0xfffffff7
L7a5c:
        mov     x0, x20
        mov     x2, #0xced
        mov     w1, #0x0
        bl      L0e80
L7a6c:
        stp     xzr, xzr, [x19, #352]
        stp     xzr, xzr, [x22, #16]
        mov     x2, #0x14c
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e80
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #488]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L7b08
        ldp     x21, x22, [sp, #16]
        mov     w0, w26
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #496
        ret
L7abc:
        add     x22, x19, #0x160
        mov     x21, x0
        mov     x1, #0x20
        mov     x0, x22
        mov     w26, #0xfffffffd
        bl      L0e60
        cbnz    w0, L7a5c
        mov     x6, x25
        mov     x4, x21
        mov     x2, x24
        mov     x1, x23
        mov     x5, x22
        mov     x3, x19
        mov     x0, x20
        mov     w7, #0x0
        bl      L6dd0
        mov     w26, w0
        cbz     w0, L7a6c
        b       L7a5c
L7b08:
        bl      L0e70
        nop

// mldsa65_verify (0xbc bytes)
L7b10:
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
        bl      L7860
        cbz     x0, L7bc0
        mov     x4, x0
        mov     x5, x22
        mov     x0, x20
        mov     x2, x23
        mov     x1, x21
        mov     x3, x19
        mov     w6, #0x0
        bl      L7390
        mov     w20, w0
L7b80:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e80
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L7bc8
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret
L7bc0:
        mov     w20, #0xfffffff7
        b       L7b80
L7bc8:
        bl      L0e70
        nop

// mldsa65_signature_pre_hash_internal (0xd0 bytes)
L7bd0:
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
        cbnz    w7, L7c54
L7c00:
        mov     w21, #0xfffffff7
L7c04:
        mov     x0, x20
        mov     x2, #0xced
        mov     w1, #0x0
        bl      L0e80
L7c14:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e80
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L7c9c
        ldr     x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #416
        ret
L7c54:
        mov     x21, x5
        mov     x22, x6
        mov     w5, w7
        mov     x0, x19
        bl      L7860
        cbz     x0, L7c00
        mov     x5, x21
        mov     x2, x0
        mov     x6, x22
        mov     x1, x19
        mov     x0, x20
        mov     w7, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L6dd0
        mov     w21, w0
        cbz     w0, L7c14
        b       L7c04
L7c9c:
        bl      L0e70

// mldsa65_signature_pre_hash_shake256 (0xbc bytes)
L7ca0:
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
        bl      L12b4
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x0, x20
        mov     x1, x19
        mov     w7, #0xc
        mov     x2, #0x40
        bl      L7bd0
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0x900000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #152]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L7d58
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret
L7d58:
        bl      L0e70
        nop

// mldsa65_verify_pre_hash_internal (0xbc bytes)
L7d60:
        stp     x19, x20, [sp, #-400]!
        .inst   0x900000c7  // adrp x7, 0x1f000
        ldr     x7, [x7, #4088]
        str     x30, [sp, #24]
        add     x19, sp, #0x3f
        ldr     x8, [x7]
        str     x8, [sp, #392]
        mov     x8, #0x0
        and     x19, x19, #0xffffffffffffffe0
        cbz     w6, L7e0c
        mov     x20, x0
        mov     x0, x19
        str     x21, [sp, #16]
        mov     x21, x5
        mov     w5, w6
        bl      L7860
        mov     x2, x0
        cbz     x0, L7e08
        mov     x5, x21
        mov     x0, x20
        mov     x1, x19
        mov     w6, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L7390
        mov     w20, w0
        ldr     x21, [sp, #16]
L7dcc:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e80
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #392]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L7e14
        ldr     x30, [sp, #24]
        mov     w0, w20
        ldp     x19, x20, [sp], #400
        ret
L7e08:
        ldr     x21, [sp, #16]
L7e0c:
        mov     w20, #0xfffffff7
        b       L7dcc
L7e14:
        str     x21, [sp, #16]
        bl      L0e70
        nop

// mldsa65_verify_pre_hash_shake256 (0xac bytes)
L7e20:
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
        bl      L12b4
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x0, x20
        mov     x1, x19
        mov     w6, #0xc
        mov     x2, #0x40
        bl      L7d60
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0x900000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #136]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L7ec8
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #144
        ret
L7ec8:
        bl      L0e70
        nop

// mldsa65_pk_from_sk (0x328 bytes)
L7ed0:
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
        bl      L6550
        mov     w1, #0x5
        mov     x0, x19
        bl      L6374
        mov     x2, x26
        mov     w1, #0x5
        mov     w25, w0
        mov     x0, x22
        bl      L6490
        mov     w27, w0
        mov     x0, x19
        bl      L62b0
        ldp     q0, q1, [x28]
        mov     x3, x22
        mov     x4, x23
        mov     x1, x24
        mov     x2, x19
        add     x0, x21, #0x20
        stp     q0, q1, [x21]
        bl      L6820
        mov     w22, w0
        cbz     w0, L8088
        mov     x6, #0x21c0
        mov     x7, #0x2200
        add     x28, x19, x6
        add     x20, x19, x7
L7fd8:
        mov     x0, x21
        mov     x2, #0x7a0
        mov     w1, #0x0
        bl      L0e80
L7fe8:
        mov     x0, x24
        mov     x2, #0x9c0
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x400
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x1400
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e80
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
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #8968]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L81f4
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
L8088:
        movi    v1.4s, #0x0
        add     x20, x20, #0x600
        mov     x0, x24
        add     x1, x24, #0x9c0
        mov     v2.16b, v1.16b
        nop
L80a0:
        ldr     q0, [x20], #16
        ldr     q3, [x0], #16
        eor     v0.16b, v0.16b, v3.16b
        orr     v2.16b, v2.16b, v0.16b
        eor     v1.16b, v1.16b, v0.16b
        cmp     x1, x0
        b.ne    L80a0
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
        bl      L12b4
        movi    v0.4s, #0x0
        ldr     w4, [sp, #108]
        mov     x0, x28
        add     x2, x28, #0x40
        mov     x1, x20
        mov     v2.16b, v0.16b
L815c:
        ldr     q1, [x0], #16
        ldr     q3, [x1], #16
        eor     v1.16b, v1.16b, v3.16b
        orr     v2.16b, v2.16b, v1.16b
        eor     v0.16b, v0.16b, v1.16b
        cmp     x0, x2
        b.ne    L815c
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
        b.eq    L7fe8
        mov     w22, #0xfffffff9
        b       L7fd8
L81f4:
        bl      L0e70
        nop
        nop

// mldsa87_unpack_pk_t1 (0x14 bytes)
L8200:
        add     w2, w2, w2, lsl #2
        lsl     w2, w2, #6
        add     x2, x2, #0x20
        add     x1, x1, x2
        b       L28c0

// mldsa87_pack_sk_rho_key_tr (0x28 bytes)
L8214:
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

// mldsa87_unpack_sk (0xb4 bytes)
L8240:
        stp     x19, x20, [sp, #-64]!
        add     x7, x6, #0x40
        mov     x20, x3
        stp     x21, x22, [sp, #16]
        mov     x21, x6
        mov     x6, x1
        stp     x23, x24, [sp, #32]
        add     x1, x21, #0x80
        mov     x23, x3
        stp     x25, x30, [sp, #48]
        mov     x3, #0x1320
        mov     x24, x5
        ldp     q0, q1, [x21]
        mov     x25, x4
        add     x22, x21, x3
        add     x19, x21, #0x620
        stp     q0, q1, [x0]
        mov     x0, x4
        ldp     q0, q1, [x21, #32]
        stp     q0, q1, [x2]
        ldp     q0, q1, [x7]
        stp     q0, q1, [x6]
        ldp     q0, q1, [x7, #32]
        stp     q0, q1, [x6, #32]
        bl      L91e0
        mov     x0, x25
        bl      L8f70
        add     x1, x21, #0x320
        mov     x0, x24
        bl      L9260
        mov     x0, x24
        bl      L90c0
L82c0:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x1a0
        bl      L2a60
        add     x20, x20, #0x400
        cmp     x19, x22
        b.ne    L82c0
        ldp     x21, x22, [sp, #16]
        mov     x0, x23
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        b       L90c0

// mldsa87_pack_sig_c (0x14 bytes)
L82f4:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        ldp     q0, q1, [x1, #32]
        stp     q0, q1, [x0, #32]
        ret
        nop
        nop

// mldsa87_pack_sig_h (0xf8 bytes)
L8310:
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
L8370:
        mov     x1, x28
        mov     x0, x20
        bl      L2ce4
        mov     x4, #0x0
        b       L839c
L8384:
        cmp     w7, #0x0
        ccmp    w5, w27, #0x0, ne
        b.eq    L83b0
        add     x4, x4, #0x1
        cmp     x4, #0x100
        b.eq    L83cc
L839c:
        ldr     w5, [x21, x4, lsl #2]
        ldr     w7, [x20, x4, lsl #2]
        add     w6, w5, w25
        cmp     w6, w22
        b.ls    L8384
L83b0:
        cmp     w19, #0x4b
        b.eq    L83e8
        strb    w4, [x26, w19, uxtw]
        add     x4, x4, #0x1
        add     w19, w19, #0x1
        cmp     x4, #0x100
        b.ne    L839c
L83cc:
        add     x28, x28, #0x80
        strb    w19, [x23], #1
        add     x21, x21, #0x400
        cmp     x28, x24
        b.ne    L8370
        mov     w0, #0x0
        b       L83ec
L83e8:
        mov     w0, #0xffffffff
L83ec:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #96
        ret
        nop
        nop

// mldsa87_pack_sig_z (0x14 bytes)
L8410:
        add     w2, w2, w2, lsl #2
        lsl     w2, w2, #7
        add     x2, x2, #0x40
        add     x0, x0, x2
        b       L8c44

// mldsa87_sig_unpack_hints (0x108 bytes)
L8424:
        stp     x19, x20, [sp, #-48]!
        mov     x3, #0x11c0
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x6, x0
        add     x22, x1, x3
        stp     x23, x30, [sp, #32]
        mov     w21, #0x0
        mov     w23, w2
        cbz     w2, L8454
        add     w0, w2, #0x4a
        ldrb    w21, [x22, w0, uxtw]
L8454:
        add     w0, w23, #0x4b
        ldrb    w20, [x22, w0, uxtw]
        cmp     w20, #0x4b
        ccmp    w21, w20, #0x2, ls
        b.hi    L84c8
        mov     x0, x6
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e80
        mov     x6, x0
        cmp     w21, w20
        b.cs    L84dc
        mov     w0, #0x11c0
        add     w0, w21, w0
        mov     w3, w21
        add     x1, x19, x0
        mov     w7, #0x1
L8498:
        ldrb    w4, [x1], #1
        mov     w5, w3
        add     w3, w3, #0x1
        str     w7, [x6, x4, lsl #2]
        cmp     w20, w3
        b.ls    L84dc
        cmp     w21, w3
        b.cs    L8498
        ldrb    w0, [x22, w5, uxtw]
        ldrb    w4, [x1]
        cmp     w4, w0
        b.hi    L8498
L84c8:
        mov     w0, #0xffffffff
L84cc:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L84dc:
        cmp     w23, #0x7
        b.eq    L84f8
L84e4:
        mov     w0, #0x0
L84e8:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L84f8:
        cmp     w20, #0x4b
        b.eq    L84e4
        ldrb    w0, [x22, x20]
        add     x20, x20, #0x1
        cbnz    w0, L84c8
        nop
L8510:
        cmp     w20, #0x4b
        b.eq    L84e8
        ldrb    w0, [x22, x20]
        add     x20, x20, #0x1
        cbz     w0, L8510
        mov     w0, #0xffffffff
        b       L84cc
        nop

// mld_rej_eta_c87.constprop.0 (0xa8 bytes)
L8530:
        mov     x8, x0
        mov     w0, w1
        cmp     w1, #0xff
        b.hi    L85d4
        mov     w9, #0x1
        sub     w9, w9, w2
        mov     w7, #0xcd
        mov     w10, #0x2
L8550:
        ldrb    w3, [x2]
        add     w5, w9, w2
        add     x2, x2, #0x1
        and     w4, w3, #0xf
        lsr     w3, w3, #4
        cmp     w4, #0xf
        b.eq    L8588
        mul     w1, w4, w7
        lsr     w1, w1, #10
        add     w1, w1, w1, lsl #2
        sub     w4, w4, w1
        sub     w4, w10, w4
        str     w4, [x8, w0, uxtw #2]
        add     w0, w0, #0x1
L8588:
        cmp     w0, #0xff
        mul     w1, w3, w7
        cset    w4, ls
        add     w6, w0, #0x1
        cmp     w4, #0x0
        ccmp    w3, #0xe, #0x2, ne
        b.hi    L85c4
        lsr     w1, w1, #10
        cmp     w6, #0xff
        cset    w4, ls
        add     w1, w1, w1, lsl #2
        sub     w3, w3, w1
        sub     w3, w10, w3
        str     w3, [x8, w0, uxtw #2]
        mov     w0, w6
L85c4:
        cmp     w5, #0x87
        cset    w1, ls
        tst     w4, w1
        b.ne    L8550
L85d4:
        ret
        nop
        nop

// mldsa87_poly_decompose (0x64 bytes)
L85e0:
        mov     x5, #0x0
        mov     w7, #0x3ff000
        mov     w6, #0xff801fff
        nop
L85f0:
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
        b.ne    L85f0
        ret

// mldsa87_poly_use_hint (0x7c bytes)
L8644:
        mov     x6, #0x0
        mov     w10, #0x3ff000
        mov     w9, #0xff801fff
L8650:
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
        cbz     w4, L86ac
        csel    w2, w8, w7, le
L86ac:
        str     w2, [x0, x6]
        add     x6, x6, #0x4
        cmp     x6, #0x400
        b.ne    L8650
        ret

// mldsa87_poly_uniform_eta_4x (0x268 bytes)
L86c0:
        sub     sp, sp, #0x7d0
        mov     x8, x4
        .inst   0xf00000a4  // adrp x4, 0x1f000
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
        bl      L16c0
        mov     x4, x21
        mov     x3, x20
        mov     x2, x19
        mov     x1, x28
        mov     x0, x26
        mov     x5, #0x42
        bl      L15d0
        mov     x3, x23
        mov     x5, x26
        mov     x4, #0x1
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L1634
        ldr     x0, [sp, #104]
        mov     x2, x22
        mov     w1, #0x0
        bl      L8530
        mov     w19, w0
        ldr     x0, [sp, #112]
        mov     x2, x25
        mov     w1, #0x0
        bl      L8530
        mov     w20, w0
        ldr     x0, [sp, #120]
        mov     x2, x24
        mov     w1, #0x0
        bl      L8530
        mov     w21, w0
        ldr     x0, [sp, #128]
        mov     w1, #0x0
        mov     x2, x23
        bl      L8530
        mov     w28, w0
        cmp     w21, w27
        ccmp    w0, w27, #0x0, hi
        cset    w0, ls
        cmp     w20, w27
        ccmp    w19, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbz     w0, L88bc
        nop
L8830:
        mov     x5, x26
        mov     x3, x23
        mov     x4, #0x1
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L1634
        ldr     x0, [sp, #104]
        mov     w1, w19
        mov     x2, x22
        bl      L8530
        mov     w19, w0
        ldr     x0, [sp, #112]
        mov     w1, w20
        mov     x2, x25
        bl      L8530
        mov     w20, w0
        ldr     x0, [sp, #120]
        mov     w1, w21
        mov     x2, x24
        bl      L8530
        mov     w21, w0
        ldr     x0, [sp, #128]
        mov     w1, w28
        mov     x2, x23
        bl      L8530
        cmp     w0, #0xff
        ccmp    w21, w27, #0x0, hi
        mov     w28, w0
        cset    w0, ls
        cmp     w19, #0xff
        ccmp    w20, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbnz    w0, L8830
L88bc:
        mov     x0, x26
        bl      L16c4
        mov     x0, x22
        mov     x2, #0x280
        mov     w1, #0x0
        bl      L0e80
        ldr     x19, [sp, #136]
        mov     x2, #0x180
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1992]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L8924
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x7d0
        ret
L8924:
        bl      L0e70
        nop
        nop

// mldsa87_poly_challenge (0x168 bytes)
L8930:
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
        bl      L10a4
        mov     x1, x19
        mov     x2, #0x40
        mov     x0, x21
        bl      L10d0
        mov     x0, x21
        bl      L1160
        mov     x2, x21
        mov     x0, x20
        mov     x1, #0x88
        bl      L11e0
        mov     x2, x20
        mov     w0, #0x0
        mov     x3, #0x0
L89a0:
        ldrb    w1, [x2], #1
        lsl     x1, x1, x0
        add     w0, w0, #0x8
        orr     x3, x3, x1
        cmp     w0, #0x40
        b.ne    L89a0
        mov     x0, x23
        mov     x2, #0x400
        mov     w1, #0x0
        str     x3, [sp, #56]
        bl      L0e80
        mov     x19, #0xc4
        mov     w22, #0x1
        mov     w0, #0x8
        b       L89ec
L89dc:
        ldrb    w1, [x20, w0, uxtw]
        add     w0, w0, #0x1
        cmp     w1, w19
        b.ls    L8a14
L89ec:
        cmp     w0, #0x88
        b.ne    L89dc
        mov     x0, x20
        mov     x1, #0x88
        mov     x2, x21
        bl      L11e0
        ldrb    w1, [x20]
        mov     w0, #0x1
        cmp     w1, w19
        b.hi    L89dc
L8a14:
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
        b.ne    L89ec
        mov     x0, x21
        bl      L1290
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
        b.ne    L8a94
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #448
        ret
L8a94:
        bl      L0e70
        nop
        nop

// mldsa87_polyeta_pack (0xdc bytes)
L8aa0:
        .inst   0xf00000a2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        add     x10, x1, #0x400
        mov     w5, #0x2
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
L8ac0:
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
        b.ne    L8ac0
        add     x0, sp, #0x10
        str     xzr, [sp, #16]
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L8b78
        ldr     x30, [sp], #32
        ret
L8b78:
        bl      L0e70
        nop

// mldsa87_polyeta_unpack (0xc4 bytes)
L8b80:
        movi    v2.4s, #0x2
        add     x5, x1, #0x60
L8b88:
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
        b.ne    L8b88
        ret

// mldsa87_polyz_pack (0x98 bytes)
L8c44:
        .inst   0xf00000a2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-48]!
        add     x7, x0, #0x280
        mov     w5, #0x80000
        ldr     x3, [x2]
        str     x3, [sp, #40]
        mov     x3, #0x0
        nop
L8c68:
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
        b.ne    L8c68
        add     x0, sp, #0x18
        stp     xzr, xzr, [sp, #24]
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #40]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L8cd8
        ldr     x30, [sp], #48
        ret
L8cd8:
        bl      L0e70
        nop

// mldsa87_polyz_unpack (0x70 bytes)
L8ce0:
        add     x6, x1, #0x280
        mov     w5, #0x80000
L8ce8:
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
        b.ne    L8ce8
        ret

// mldsa87_poly_uniform_gamma1_4x (0x18c bytes)
L8d50:
        mov     x12, #0x1040
        sub     sp, sp, x12
        mov     x8, x4
        .inst   0xf00000a9  // adrp x9, 0x1f000
        ldr     x9, [x9, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x9f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        add     x20, x19, #0xb00
        stp     x23, x24, [sp, #32]
        add     x22, x19, #0xb60
        add     x23, x19, #0xbc0
        stp     x25, x26, [sp, #48]
        add     x21, sp, #0xd18
        mov     x24, x1
        stp     x27, x28, [sp, #64]
        mov     x25, x0
        mov     x0, x21
        str     x30, [sp, #80]
        add     x26, x19, #0x840
        add     x27, x19, #0x580
        add     x28, x19, #0x2c0
        ldp     q0, q1, [x4, #32]
        add     x4, x19, #0xc20
        ldp     q2, q3, [x8]
        mov     x8, x9
        ldr     x9, [x8]
        str     x9, [sp, #4152]
        mov     x9, #0x0
        ldrh    w8, [sp, #4160]
        stp     q0, q1, [x20, #32]
        stp     q0, q1, [x22, #32]
        stp     x2, x3, [sp, #104]
        stp     q2, q3, [x20]
        stp     q2, q3, [x22]
        stp     q2, q3, [x23]
        stp     q0, q1, [x23, #32]
        stp     q2, q3, [x4]
        stp     q0, q1, [x4, #32]
        str     x4, [sp, #120]
        strh    w5, [x19, #2880]
        strh    w6, [x19, #2976]
        strh    w7, [x19, #3072]
        strh    w8, [x19, #3168]
        bl      L16c0
        ldr     x4, [sp, #120]
        mov     x3, x23
        mov     x2, x22
        mov     x1, x20
        mov     x0, x21
        mov     x5, #0x42
        bl      L15d0
        mov     x3, x26
        mov     x2, x27
        mov     x5, x21
        mov     x4, #0x5
        mov     x1, x28
        mov     x0, x19
        bl      L1634
        mov     x1, x19
        mov     x0, x25
        bl      L8ce0
        mov     x1, x28
        mov     x0, x24
        bl      L8ce0
        ldr     x0, [sp, #104]
        mov     x1, x27
        bl      L8ce0
        ldr     x0, [sp, #112]
        mov     x1, x26
        bl      L8ce0
        mov     x0, x21
        bl      L16c4
        mov     x0, x19
        mov     x2, #0xb00
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x180
        mov     x0, x20
        mov     w1, #0x0
        bl      L0e80
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4152]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L8ed8
        ldp     x19, x20, [sp]
        mov     x12, #0x1040
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret
L8ed8:
        bl      L0e70
        nop

// mldsa87_polyvecl_uniform_gamma1 (0x90 bytes)
L8ee0:
        sub     sp, sp, #0x40
        mov     w3, #0xff
        mov     x4, x1
        mov     w5, w2
        strh    w3, [sp]
        stp     x19, x20, [sp, #16]
        sxth    w19, w2
        mov     x20, x0
        stp     x21, x22, [sp, #32]
        add     x22, x0, #0xc00
        mov     x21, x1
        add     w7, w19, #0x2
        add     w6, w19, #0x1
        mov     x3, x22
        add     x1, x0, #0x400
        add     x2, x0, #0x800
        str     x30, [sp, #48]
        bl      L8d50
        add     w0, w19, #0x6
        strh    w0, [sp]
        mov     x1, #0x1800
        add     w7, w19, #0x5
        add     x3, x20, x1
        add     w6, w19, #0x4
        add     w5, w19, #0x3
        mov     x0, x22
        mov     x4, x21
        add     x1, x20, #0x1, lsl #12
        mov     x2, #0x1400
        add     x2, x20, x2
        bl      L8d50
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldr     x30, [sp, #48]
        add     sp, sp, #0x40
        ret

// mldsa87_polyvecl_ntt (0x38 bytes)
L8f70:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x0, #0x1c00
        add     x20, x19, x0
        str     x30, [sp, #16]
        nop
L8f88:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L22d0
        cmp     x19, x20
        b.ne    L8f88
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop
        nop

// mldsa87_polyvecl_pointwise_acc_montgomery (0x84 bytes)
L8fb0:
        mov     x7, x0
        .inst   0xd0000000  // adrp x0, 0xa000
        mov     x5, x2
        mov     x6, x1
        ldr     q5, [x0, #4048]
        .inst   0xd0000000  // adrp x0, 0xa000
        mov     x1, #0x0
        mov     x4, #0x1c00
        ldr     q4, [x0, #4016]
        nop
L8fd8:
        add     x3, x5, x1
        movi    v1.4s, #0x0
        add     x2, x6, x1
        mov     x0, #0x0
        mov     v0.16b, v1.16b
        nop
L8ff0:
        ldr     q2, [x2, x0]
        ldr     q3, [x3, x0]
        add     x0, x0, #0x400
        smlal   v0.2d, v3.2s, v2.2s
        smlal2  v1.2d, v3.4s, v2.4s
        cmp     x0, x4
        b.ne    L8ff0
        uzp1    v2.4s, v0.4s, v1.4s
        mul     v2.4s, v2.4s, v5.4s
        smlal   v0.2d, v2.2s, v4.2s
        smlal2  v1.2d, v2.4s, v4.4s
        uzp2    v0.4s, v0.4s, v1.4s
        str     q0, [x7, x1]
        add     x1, x1, #0x10
        cmp     x1, #0x400
        b.ne    L8fd8
        ret

// mldsa87_polyvecl_chknorm (0x54 bytes)
L9034:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x0, #0x1c00
        stp     x21, x22, [sp, #16]
        mov     w21, w1
        add     x22, x19, x0
        mov     w20, #0x0
        str     x30, [sp, #32]
        nop
L9058:
        mov     x0, x19
        mov     w1, w21
        add     x19, x19, #0x400
        bl      L2bb4
        orr     w20, w20, w0
        cmp     x19, x22
        b.ne    L9058
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
        nop
        nop

// mldsa87_polyveck_caddq (0x30 bytes)
L9090:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        add     x20, x0, #0x2, lsl #12
        str     x30, [sp, #16]
L90a0:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L2210
        cmp     x19, x20
        b.ne    L90a0
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_ntt (0x30 bytes)
L90c0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        add     x20, x0, #0x2, lsl #12
        str     x30, [sp, #16]
L90d0:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L22d0
        cmp     x19, x20
        b.ne    L90d0
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_invntt_tomont (0x30 bytes)
L90f0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        add     x20, x0, #0x2, lsl #12
        str     x30, [sp, #16]
L9100:
        mov     x0, x19
        add     x19, x19, #0x400
        bl      L23a0
        cmp     x19, x20
        b.ne    L9100
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_unpack_eta_chknorm (0x5c bytes)
L9120:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x0
        mov     x20, x2
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     w21, #0x0
        stp     x23, x30, [sp, #32]
        add     x23, x0, #0x300
L9140:
        mov     x1, x19
        mov     x0, x20
        bl      L8b80
        mov     w1, w22
        mov     x0, x20
        add     x19, x19, #0x60
        bl      L2bb4
        orr     w21, w21, w0
        cmp     x19, x23
        b.ne    L9140
        ldp     x23, x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret
        nop

// mldsa87_polyveck_decompose_pack_w1 (0x58 bytes)
L9180:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x22, x1, #0x2, lsl #12
        str     x30, [sp, #32]
        nop
L91a0:
        mov     x1, x19
        mov     x0, x21
        bl      L85e0
        add     x19, x19, #0x400
        mov     x0, x20
        mov     x1, x21
        bl      L2c60
        add     x20, x20, #0x80
        cmp     x19, x22
        b.ne    L91a0
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
        nop
        nop

// mldsa87_polyvecl_unpack_eta (0x40 bytes)
L91e0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x30, [sp, #16]
        add     x21, x1, #0x2a0
        nop
L91f8:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x60
        bl      L8b80
        add     x20, x20, #0x400
        cmp     x19, x21
        b.ne    L91f8
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyvecl_unpack_z (0x40 bytes)
L9220:
        stp     x19, x20, [sp, #-32]!
        mov     x20, x0
        mov     x19, x1
        mov     x0, #0x1180
        stp     x21, x30, [sp, #16]
        add     x21, x1, x0
L9238:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x280
        bl      L8ce0
        add     x20, x20, #0x400
        cmp     x19, x21
        b.ne    L9238
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyveck_unpack_eta (0x40 bytes)
L9260:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x30, [sp, #16]
        add     x21, x1, #0x300
        nop
L9278:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x60
        bl      L8b80
        add     x20, x20, #0x400
        cmp     x19, x21
        b.ne    L9278
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mldsa87_polyvec_matrix_expand_eager (0x1b0 bytes)
L92a0:
        stp     x19, x20, [sp, #-336]!
        .inst   0xd00000a3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x21, x22, [sp, #16]
        mov     x21, x0
        stp     x23, x30, [sp, #32]
        add     x23, sp, #0x4f
        and     x23, x23, #0xffffffffffffffe0
        add     x2, x23, #0x100
        mov     x0, x23
        ldr     x4, [x3]
        str     x4, [sp, #328]
        mov     x4, #0x0
L92d4:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        add     x0, x0, #0x40
        cmp     x2, x0
        b.ne    L92d4
        mov     w20, #0x4925
        mov     w19, #0x4
        movk    w20, #0x2492, lsl #16
        mov     w22, #0x7
L92f8:
        sub     w6, w19, #0x4
        mov     x5, x23
        mov     w2, w6
L9304:
        umull   x3, w2, w20
        add     x5, x5, #0x40
        lsr     x3, x3, #32
        sub     w1, w2, w3
        add     w1, w3, w1, lsr #1
        lsr     w1, w1, #2
        sturb   w1, [x5, #-31]
        lsl     w3, w1, #3
        sub     w1, w3, w1
        sub     w1, w2, w1
        add     w2, w2, #0x1
        sturb   w1, [x5, #-32]
        cmp     w19, w2
        b.ne    L9304
        sub     w9, w19, #0x3
        sub     w8, w19, #0x2
        sub     w7, w19, #0x1
        umull   x10, w6, w20
        add     w19, w19, #0x4
        mov     x4, x23
        umull   x12, w9, w20
        umull   x11, w8, w20
        lsr     x10, x10, #32
        umull   x5, w7, w20
        sub     w0, w6, w10
        lsr     x12, x12, #32
        lsr     x11, x11, #32
        sub     w1, w9, w12
        lsr     x5, x5, #32
        sub     w2, w8, w11
        sub     w3, w7, w5
        add     w1, w12, w1, lsr #1
        add     w2, w11, w2, lsr #1
        add     w0, w10, w0, lsr #1
        add     w3, w5, w3, lsr #1
        lsr     w1, w1, #2
        lsr     w2, w2, #2
        lsr     w0, w0, #2
        lsr     w3, w3, #2
        lsl     w12, w1, #3
        lsl     w11, w2, #3
        lsl     w5, w0, #3
        lsl     w10, w3, #3
        sub     w12, w12, w1
        sub     w11, w11, w2
        sub     w10, w10, w3
        sub     w5, w5, w0
        sub     w9, w9, w12
        sub     w8, w8, w11
        sub     w7, w7, w10
        sub     w5, w6, w5
        umaddl  x1, w1, w22, x9
        umaddl  x2, w2, w22, x8
        umaddl  x3, w3, w22, x7
        umaddl  x0, w0, w22, x5
        add     x1, x21, x1, lsl #10
        add     x2, x21, x2, lsl #10
        add     x3, x21, x3, lsl #10
        add     x0, x21, x0, lsl #10
        bl      L2654
        cmp     w19, #0x3c
        b.ne    L92f8
        movi    v0.4s, #0x0
        stp     q0, q0, [x23]
        stp     q0, q0, [x23, #32]
        stp     q0, q0, [x23, #64]
        stp     q0, q0, [x23, #96]
        stp     q0, q0, [x23, #128]
        stp     q0, q0, [x23, #160]
        stp     q0, q0, [x23, #192]
        stp     q0, q0, [x23, #224]
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #328]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L944c
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #336
        ret
L944c:
        bl      L0e70

// mldsa87_polyvec_matrix_pointwise_montgomery_row_eager (0xc bytes)
L9450:
        mov     w4, #0x1c00
        umaddl  x1, w3, w4, x1
        b       L8fb0
        nop

// mldsa87_polyvec_matrix_pointwise_montgomery_yvec_eager (0x70 bytes)
L9460:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x0
        mov     w19, #0x0
        stp     x21, x22, [sp, #16]
        mov     x22, x1
        mov     x1, x2
        mov     x2, #0x1c00
        mov     x21, x3
        stp     x23, x30, [sp, #32]
        mov     x23, x0
        mov     x0, x3
        bl      L0e50
        mov     x0, x21
        bl      L8f70
L9498:
        mov     w3, w19
        mov     x0, x20
        mov     x2, x21
        mov     x1, x22
        add     w19, w19, #0x1
        bl      L9450
        add     x20, x20, #0x400
        cmp     w19, #0x8
        b.ne    L9498
        ldp     x21, x22, [sp, #16]
        mov     x0, x23
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        b       L90f0

// mld_compute_pack_t0_t187 (0x164 bytes)
L94d0:
        mov     x12, #0xe870
        sub     sp, sp, x12
        stp     x21, x22, [sp, #16]
        mov     x22, x3
        mov     w21, #0x0
        .inst   0xd00000a3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        stp     x23, x24, [sp, #32]
        mov     x24, x1
        mov     x1, x4
        stp     x25, x26, [sp, #48]
        add     x4, sp, #0xc, lsl #12
        mov     x23, x2
        str     x30, [sp, #64]
        add     x26, sp, #0x6f
        and     x26, x26, #0xffffffffffffffe0
        mov     x25, x0
        ldr     x2, [x3]
        str     x2, [x4, #10344]
        mov     x2, #0x0
        mov     x0, #0xe400
        add     x20, x26, #0xe, lsl #12
        add     x19, x26, x0
        mov     x0, x26
        bl      L92a0
L9538:
        mov     w3, w21
        mov     x2, x23
        mov     x1, x26
        mov     x0, x19
        bl      L9450
        add     w21, w21, #0x1
        mov     x0, x19
        bl      L23a0
        mov     x1, x22
        mov     x0, x20
        bl      L8b80
        add     x22, x22, #0x60
        mov     x1, x20
        mov     x0, x19
        bl      L2250
        mov     x0, x19
        bl      L21e0
        mov     x0, x19
        bl      L2210
        mov     x2, x19
        mov     x1, x19
        mov     x0, x20
        bl      L2510
        mov     x0, x25
        mov     x1, x20
        bl      L2864
        add     x25, x25, #0x140
        mov     x0, x24
        mov     x1, x19
        bl      L2934
        add     x24, x24, #0x1a0
        cmp     w21, #0x8
        b.ne    L9538
        mov     x0, x20
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x400
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0xe000
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e80
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0xc, lsl #12
        ldr     x3, [x2, #10344]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.ne    L9630
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        mov     x12, #0xe870
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        add     sp, sp, x12
        ret
L9630:
        bl      L0e70

// mld_H87.constprop.0 (0x108 bytes)
L9634:
        stp     x19, x20, [sp, #-304]!
        mov     x20, x6
        .inst   0xd00000a7  // adrp x7, 0x1f000
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
        bl      L10a4
        mov     x2, x24
        mov     x1, x23
        mov     x0, x19
        bl      L10d0
        cbnz    x21, L9710
        cbnz    x20, L9724
L969c:
        mov     x0, x19
        bl      L1160
        mov     x2, x19
        mov     x1, #0x40
        mov     x0, x22
        bl      L11e0
        mov     x0, x19
        bl      L1290
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        str     q0, [x19, #192]
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L9738
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #304
        ret
L9710:
        mov     x2, x21
        mov     x1, x25
        mov     x0, x19
        bl      L10d0
        cbz     x20, L969c
L9724:
        mov     x2, x20
        mov     x1, x26
        mov     x0, x19
        bl      L10d0
        b       L969c
L9738:
        bl      L0e70
        nop

// mldsa87_keypair_internal (0x31c bytes)
L9740:
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
        .inst   0xd00000a2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        ldr     x0, [x2]
        str     x0, [sp, #7576]
        mov     x0, #0x0
        stp     q0, q1, [x27]
        mov     x2, x27
        mov     x0, x21
        strh    w4, [x19, #7392]
        bl      L12b4
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
        bl      L86c0
        mov     x1, x19
        add     x0, x20, #0x4a0
        bl      L8aa0
        mov     x1, x25
        add     x0, x20, #0x500
        bl      L8aa0
        mov     x1, x24
        add     x0, x20, #0x560
        bl      L8aa0
        mov     x1, x23
        add     x0, x20, #0x5c0
        bl      L8aa0
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
        bl      L86c0
        str     x28, [sp, #120]
        mov     x0, x28
        mov     x1, x19
        bl      L8aa0
        mov     x1, x25
        add     x0, x20, #0x380
        bl      L8aa0
        mov     x1, x24
        add     x0, x20, #0x3e0
        bl      L8aa0
        mov     x5, #0x1800
        mov     x1, x23
        add     x28, x19, x5
        add     x0, x20, #0x440
        bl      L8aa0
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
        bl      L86c0
        ldr     x0, [sp, #128]
        mov     x1, x0
        add     x0, x20, #0x200
        bl      L8aa0
        ldr     x9, [sp, #136]
        add     x0, x20, #0x260
        mov     x1, x9
        bl      L8aa0
        mov     x1, x28
        add     x0, x20, #0x2c0
        bl      L8aa0
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
        bl      L86c0
        mov     x1, x19
        add     x0, x20, #0x80
        bl      L8aa0
        mov     x1, x25
        add     x0, x20, #0xe0
        bl      L8aa0
        mov     x1, x24
        add     x0, x20, #0x140
        bl      L8aa0
        mov     x1, x23
        add     x0, x20, #0x1a0
        bl      L8aa0
        mov     x0, x19
        bl      L8f70
        ldp     q0, q1, [x21]
        mov     x7, #0x1c80
        ldr     x3, [sp, #120]
        mov     x4, x21
        mov     x2, x19
        add     x1, x20, #0x620
        add     x0, x22, #0x20
        add     x23, x19, x7
        stp     q0, q1, [x22]
        bl      L94d0
        mov     w24, w0
        cbnz    w0, L99b4
        mov     x0, x23
        mov     x2, x22
        mov     x3, #0xa20
        mov     x1, #0x40
        bl      L12b4
        mov     x2, x23
        add     x3, x21, #0x60
        mov     x1, x21
        mov     x0, x20
        bl      L8214
L99b4:
        mov     x0, x19
        mov     x2, #0x1c00
        mov     w1, #0x0
        bl      L0e80
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
        cbnz    w24, L9a34
L99f0:
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #7576]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L9a58
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
L9a34:
        mov     x0, x22
        mov     x2, #0xa20
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x1320
        mov     x0, x20
        mov     w1, #0x0
        bl      L0e80
        b       L99f0
L9a58:
        bl      L0e70
        nop

// mldsa87_keypair (0x88 bytes)
L9a60:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        .inst   0xd00000a2  // adrp x2, 0x1f000
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
        bl      L0e60
        cbnz    w0, L9adc
        mov     x1, x21
        mov     x0, x20
        mov     x2, x19
        bl      L9740
L9aac:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xd00000a1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #88]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L9ae4
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #96
        ret
L9adc:
        mov     w0, #0xfffffffd
        b       L9aac
L9ae4:
        bl      L0e70
        nop
        nop

// mldsa87_signature_internal (0x508 bytes)
L9af0:
        sub     sp, sp, #0x2d0
        sub     sp, sp, #0x1a, lsl #12
        add     x8, sp, #0xbf
        and     x9, x8, #0xffffffffffffffe0
        add     x10, x9, #0x1a, lsl #12
        add     x11, x9, #0x10, lsl #12
        add     x12, x9, #0x17, lsl #12
        stp     x10, x9, [sp, #128]
        add     x9, x9, #0x12, lsl #12
        .inst   0xd00000a8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        add     x12, x12, #0x800
        stp     x19, x20, [sp]
        mov     x20, x3
        mov     x3, x9
        stp     x21, x22, [sp, #16]
        mov     x19, x5
        mov     x22, x2
        stp     x23, x24, [sp, #32]
        mov     w24, w7
        mov     x23, x1
        stp     x25, x26, [sp, #48]
        add     x25, x10, #0x20
        mov     x21, x4
        stp     x27, x28, [sp, #64]
        mov     x1, x25
        mov     x26, x10
        str     x30, [sp, #80]
        add     x2, x10, #0x60
        str     x0, [sp, #96]
        mov     x5, x11
        str     x9, [sp, #104]
        add     x9, sp, #0x18, lsl #12
        stp     x12, x11, [sp, #144]
        add     x9, x9, #0x40
        mov     x4, x12
        ldr     x7, [x8]
        str     x7, [x9, #8840]
        mov     x7, #0x0
        mov     x0, x10
        bl      L8240
        cbnz    w24, L9fd8
        mov     x6, x22
        mov     x5, x23
        mov     x4, x21
        mov     x3, x20
        mov     x1, x25
        add     x0, x26, #0x80
        mov     x2, #0x40
        bl      L9634
L9bb8:
        ldp     x24, x21, [sp, #128]
        mov     x3, x19
        mov     x4, #0x20
        mov     x2, x4
        mov     x6, #0x40
        add     x22, sp, #0x1a, lsl #12
        str     wzr, [sp, #116]
        add     x22, x22, #0x1f8
        add     x5, x24, #0x80
        add     x1, x21, #0x19, lsl #12
        add     x1, x1, #0xc00
        add     x0, x24, #0xc0
        add     x27, x21, #0x15, lsl #12
        add     x25, x21, #0x1a, lsl #12
        add     x23, x21, #0x19, lsl #12
        add     x20, x21, #0x19, lsl #12
        str     x1, [sp, #120]
        add     x1, x24, #0x60
        bl      L9634
        add     x27, x27, #0xc00
        add     x19, x21, #0x14, lsl #12
        add     x26, x21, #0xe, lsl #12
        add     x25, x25, #0x100
        add     x23, x23, #0x800
        add     x20, x20, #0x400
        mov     x1, x24
        mov     x0, x21
        bl      L92a0
L9c28:
        ldrh    w2, [sp, #116]
        mov     x0, x27
        ldr     x21, [sp, #128]
        add     x1, x21, #0xc0
        bl      L8ee0
        ldr     x1, [sp, #136]
        mov     x3, x19
        mov     x2, x27
        mov     x0, x26
        bl      L9460
        mov     x0, x26
        bl      L9090
        ldr     x24, [sp, #120]
        mov     x2, x19
        mov     x1, x26
        mov     x0, x24
        bl      L9180
        mov     x0, x22
        bl      L10a4
        add     x1, x21, #0x80
        mov     x0, x22
        mov     x2, #0x40
        bl      L10d0
        mov     x1, x24
        mov     x2, #0x400
        mov     x0, x22
        bl      L10d0
        mov     x0, x22
        bl      L1160
        mov     x2, x22
        mov     x1, #0x40
        mov     x0, x25
        bl      L11e0
        mov     x0, x22
        bl      L1290
        movi    v0.4s, #0x0
        stp     q0, q0, [x22]
        stp     q0, q0, [x22, #32]
        stp     q0, q0, [x22, #64]
        stp     q0, q0, [x22, #96]
        stp     q0, q0, [x22, #128]
        stp     q0, q0, [x22, #160]
        str     q0, [x22, #192]
        mov     x1, x25
        mov     x0, x23
        ldr     x28, [sp, #144]
        bl      L8930
        mov     x24, x27
        mov     x0, x23
        mov     w21, #0x0
        bl      L22d0
        nop
L9cf8:
        mov     x2, #0x400
        mov     x1, x28
        mov     x0, x20
        bl      L0e50
        mov     x1, x23
        mov     x0, x20
        bl      L24c0
        mov     x0, x20
        bl      L23a0
        mov     x2, #0x400
        mov     x1, x24
        mov     x0, x19
        bl      L0e50
        mov     x1, x19
        mov     x0, x20
        bl      L2250
        mov     x0, x20
        bl      L21e0
        mov     w1, #0xff88
        mov     x0, x20
        movk    w1, #0x7, lsl #16
        bl      L2bb4
        cbnz    w0, L9fd0
        ldr     x0, [sp, #96]
        mov     w2, w21
        mov     x1, x20
        add     w21, w21, #0x1
        add     x28, x28, #0x400
        add     x24, x24, #0x400
        bl      L8410
        cmp     w21, #0x7
        b.ne    L9cf8
        ldr     x28, [sp, #104]
        mov     x21, x26
        ldr     x24, [sp, #152]
        nop
L9d88:
        mov     x2, #0x400
        mov     x1, x24
        mov     x0, x19
        bl      L0e50
        mov     x1, x23
        mov     x0, x19
        bl      L24c0
        mov     x0, x19
        bl      L23a0
        mov     x1, x19
        mov     x0, x21
        bl      L2280
        mov     x0, x21
        bl      L21e0
        mov     w1, #0xfe88
        mov     x0, x21
        movk    w1, #0x3, lsl #16
        bl      L2bb4
        cbnz    w0, L9fd0
        mov     x2, #0x400
        mov     x1, x28
        mov     x0, x19
        bl      L0e50
        mov     x1, x23
        mov     x0, x19
        bl      L24c0
        mov     x0, x19
        bl      L23a0
        mov     x0, x19
        bl      L21e0
        mov     x0, x19
        mov     w1, #0x3ff00
        bl      L2bb4
        cbnz    w0, L9fd0
        mov     x0, x21
        mov     x1, x19
        bl      L2250
        add     x24, x24, #0x400
        ldr     x0, [sp, #104]
        add     x28, x28, #0x400
        add     x21, x21, #0x400
        cmp     x24, x0
        b.ne    L9d88
        ldr     x21, [sp, #96]
        mov     x1, x25
        mov     x0, x21
        bl      L82f4
        ldr     x2, [sp, #120]
        mov     x0, x21
        mov     x3, x19
        mov     x1, x26
        bl      L8310
        mov     w21, w0
L9e5c:
        mov     x0, x20
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x400
        mov     x0, x23
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x2000
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e80
        ldr     x24, [sp, #120]
        mov     x2, #0x400
        mov     w1, #0x0
        mov     x0, x24
        bl      L0e80
        mov     x2, #0x1c00
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x1c00
        mov     x0, x27
        mov     w1, #0x0
        bl      L0e80
        movi    v0.4s, #0x0
        stp     q0, q0, [x25]
        stp     q0, q0, [x25, #32]
        cbz     w21, L9f0c
        cmn     w21, #0x1
        b.ne    L9ef8
        ldr     w0, [sp, #116]
        mov     w1, #0xfff7
        add     w0, w0, #0x7
        and     w2, w0, #0xffff
        str     w2, [sp, #116]
        cmp     w1, w0, uxth
        b.ne    L9c28
        mov     w21, #0xfffffffc
L9ef8:
        ldr     x19, [sp, #96]
        mov     x2, #0x1213
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
L9f0c:
        ldr     x19, [sp, #152]
        mov     x2, #0x2000
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
        ldr     x19, [sp, #104]
        mov     x2, #0x2000
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
        ldr     x19, [sp, #144]
        mov     x2, #0x1c00
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
        ldr     x19, [sp, #136]
        mov     x2, #0xe000
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
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
        .inst   0xd00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0x18, lsl #12
        add     x2, x2, #0x40
        ldr     x3, [x2, #8840]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.ne    L9ff4
        ldp     x19, x20, [sp]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x2d0
        add     sp, sp, #0x1a, lsl #12
        ret
L9fd0:
        mov     w21, #0xffffffff
        b       L9e5c
L9fd8:
        ldr     x0, [sp, #128]
        ldp     q2, q3, [x23]
        add     x0, x0, #0x80
        ldp     q0, q1, [x23, #32]
        stp     q2, q3, [x0]
        stp     q0, q1, [x0, #32]
        b       L9bb8
L9ff4:
        bl      L0e70
        nop
        nop

// mldsa87_signature_extmu (0xa8 bytes)
La000:
        stp     x19, x20, [sp, #-112]!
        mov     x20, x0
        .inst   0xb00000a3  // adrp x3, 0x1f000
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
        bl      L0e60
        cbnz    w0, La09c
        mov     x6, x22
        mov     x1, x21
        mov     x0, x20
        mov     x5, x19
        mov     w7, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        bl      L9af0
La068:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xb00000a1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #104]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    La0a4
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret
La09c:
        mov     w0, #0xfffffffd
        b       La068
La0a4:
        bl      L0e70
        nop
        nop

// mldsa87_verify_internal (0x48c bytes)
La0b0:
        sub     sp, sp, #0xe30
        sub     sp, sp, #0x10, lsl #12
        stp     x19, x20, [sp]
        mov     x20, x2
        mov     x19, x4
        stp     x21, x22, [sp, #16]
        mov     x22, x3
        stp     x23, x24, [sp, #32]
        add     x23, sp, #0x9f
        and     x23, x23, #0xffffffffffffffe0
        stp     x25, x26, [sp, #48]
        mov     x25, x0
        add     x26, x23, #0xe, lsl #12
        stp     x27, x28, [sp, #64]
        add     x28, x23, #0x10, lsl #12
        mov     x27, x1
        str     x30, [sp, #80]
        add     x1, sp, #0x10, lsl #12
        str     x5, [sp, #96]
        add     x1, x1, #0x20
        ldp     q2, q3, [x0]
        add     x28, x28, #0xc00
        ldp     q0, q1, [x0, #32]
        add     x7, x28, #0x40
        .inst   0xb00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        mov     w24, w6
        ldr     x2, [x0]
        str     x2, [x1, #3592]
        mov     x2, #0x0
        mov     x0, x26
        add     x1, x25, #0x40
        stp     q2, q3, [x7]
        stp     q0, q1, [x7, #32]
        bl      L9220
        mov     w1, #0xff88
        mov     x0, x26
        movk    w1, #0x7, lsl #16
        bl      L9034
        cbnz    w0, La4f8
        mov     w21, w0
        cbz     w24, La44c
        add     x1, x23, #0x10, lsl #12
        add     x0, x28, #0x80
        ldp     q2, q3, [x27]
        add     x1, x1, #0x800
        ldp     q0, q1, [x27, #32]
        str     x1, [sp, #104]
        add     x1, x23, #0x10, lsl #12
        stp     q2, q3, [x0]
        add     x1, x1, #0xc80
        str     x1, [sp, #112]
        stp     q0, q1, [x0, #32]
La184:
        add     x1, x23, #0x10, lsl #12
        add     x1, x1, #0xc40
        mov     x0, x26
        mov     x19, x1
        str     x1, [sp, #120]
        add     x27, x23, #0x10, lsl #12
        add     x20, x23, #0x10, lsl #12
        bl      L8f70
        add     x27, x27, #0x400
        ldr     x1, [sp, #96]
        mov     x0, x23
        bl      L92a0
        mov     x1, x19
        mov     x0, #0xfc00
        ldr     x24, [sp, #104]
        add     x19, x23, x0
        mov     x0, x27
        bl      L8930
        mov     x0, x27
        bl      L22d0
        nop
La1d8:
        mov     w3, w21
        mov     x2, x26
        mov     x1, x23
        mov     x0, x20
        bl      L9450
        ldr     x1, [sp, #96]
        mov     w2, w21
        mov     x0, x19
        bl      L8200
        mov     x0, x19
        bl      L22b0
        mov     x0, x19
        bl      L22d0
        mov     x1, x27
        mov     x0, x19
        bl      L24c0
        mov     x1, x19
        mov     x0, x20
        bl      L2280
        mov     x0, x20
        bl      L21e0
        mov     x0, x20
        bl      L23a0
        mov     x0, x20
        bl      L2210
        mov     w2, w21
        mov     x1, x25
        mov     x0, x19
        bl      L8424
        mov     w22, w0
        cbnz    w0, La530
        mov     x1, x19
        mov     x0, x20
        bl      L8644
        add     w21, w21, #0x1
        mov     x0, x24
        mov     x1, x20
        bl      L2c60
        add     x24, x24, #0x80
        cmp     w21, #0x8
        b.ne    La1d8
        add     x21, sp, #0x10, lsl #12
        add     x21, x21, #0xd58
        mov     x0, x21
        bl      L10a4
        ldr     x1, [sp, #112]
        mov     x0, x21
        mov     x2, #0x40
        bl      L10d0
        ldr     x1, [sp, #104]
        mov     x2, #0x400
        mov     x0, x21
        bl      L10d0
        mov     x0, x21
        bl      L1160
        mov     x2, x21
        mov     x1, #0x40
        mov     x0, x28
        bl      L11e0
        mov     x0, x21
        bl      L1290
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x21, #64]
        stp     q0, q0, [x21, #96]
        stp     q0, q0, [x21, #128]
        stp     q0, q0, [x21, #160]
        str     q0, [x21, #192]
        ldr     x1, [sp, #120]
        mov     x0, x28
        mov     v2.16b, v0.16b
        add     x2, x28, #0x40
La2fc:
        ldr     q1, [x1], #16
        ldr     q3, [x0], #16
        eor     v1.16b, v1.16b, v3.16b
        orr     v2.16b, v2.16b, v1.16b
        eor     v0.16b, v0.16b, v1.16b
        cmp     x2, x0
        b.ne    La2fc
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
        b.ne    La530
La378:
        mov     x0, x19
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x400
        mov     x0, x20
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0xe000
        mov     x0, x23
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x400
        mov     x0, x27
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x1c00
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e80
        movi    v0.4s, #0x0
        stp     q0, q0, [x28]
        stp     q0, q0, [x28, #32]
        ldr     x0, [sp, #120]
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        ldr     x0, [sp, #112]
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        ldr     x19, [sp, #104]
        mov     x2, #0x400
        mov     w1, #0x0
        mov     x0, x19
        bl      L0e80
        .inst   0xb00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x2, sp, #0x10, lsl #12
        add     x2, x2, #0x20
        ldr     x3, [x2, #3592]
        ldr     x1, [x0]
        subs    x3, x3, x1
        mov     x1, #0x0
        b.ne    La538
        ldp     x19, x20, [sp]
        mov     w0, w22
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0xe30
        add     sp, sp, #0x10, lsl #12
        ret
La44c:
        add     x24, sp, #0x10, lsl #12
        add     x0, x23, #0x10, lsl #12
        add     x24, x24, #0xd58
        add     x0, x0, #0x800
        str     x0, [sp, #104]
        mov     x0, x24
        bl      L10a4
        ldr     x1, [sp, #96]
        mov     x2, #0xa20
        mov     x0, x24
        bl      L10d0
        mov     x0, x24
        bl      L1160
        ldr     x0, [sp, #104]
        mov     x2, x24
        mov     x1, #0x40
        bl      L11e0
        mov     x0, x24
        bl      L1290
        movi    v0.4s, #0x0
        stp     q0, q0, [x24]
        stp     q0, q0, [x24, #32]
        stp     q0, q0, [x24, #64]
        stp     q0, q0, [x24, #96]
        stp     q0, q0, [x24, #128]
        stp     q0, q0, [x24, #160]
        str     q0, [x24, #192]
        mov     x4, x19
        add     x1, x23, #0x10, lsl #12
        ldr     x19, [sp, #104]
        add     x1, x1, #0xc80
        mov     x0, x1
        mov     x6, x20
        mov     x5, x27
        mov     x3, x22
        mov     x2, #0x40
        str     x1, [sp, #112]
        mov     x1, x19
        bl      L9634
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        b       La184
La4f8:
        add     x0, x23, #0x10, lsl #12
        add     x27, x23, #0x10, lsl #12
        add     x0, x0, #0x800
        str     x0, [sp, #104]
        add     x0, x23, #0x10, lsl #12
        mov     x1, #0xfc00
        add     x0, x0, #0xc80
        add     x27, x27, #0x400
        add     x20, x23, #0x10, lsl #12
        add     x19, x23, x1
        str     x0, [sp, #112]
        add     x0, x23, #0x10, lsl #12
        add     x0, x0, #0xc40
        str     x0, [sp, #120]
La530:
        mov     w22, #0xfffffffa
        b       La378
La538:
        bl      L0e70
        nop

// mldsa87_verify_extmu (0x18 bytes)
La540:
        mov     x5, x2
        mov     w6, #0x1
        mov     x4, #0x0
        mov     x3, #0x0
        mov     x2, #0x40
        b       La0b0
        nop
        nop

// mldsa87_prepare_domain_separation_prefix (0x19c bytes)
La560:
        cmp     x4, #0xff
        b.hi    La5c0
        stp     x19, x21, [sp, #-64]!
        mov     x19, x4
        mov     x21, x0
        str     x30, [sp, #32]
        cbz     w5, La5a4
        stp     x22, x23, [sp, #16]
        mov     x23, x1
        sub     w1, w5, #0x1
        mov     x0, #0x0
        cmp     w1, #0xb
        b.ls    La5c8
        ldp     x22, x23, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
La5a4:
        strb    wzr, [x0]
        strb    w4, [x21, #1]
        cbnz    x4, La5e4
La5b0:
        add     x0, x19, #0x2
La5b4:
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
La5c0:
        mov     x0, #0x0
        ret
La5c8:
        .inst   0xb0000000  // adrp x0, 0xb000
        mov     x22, x2
        add     x0, x0, #0x580
        ldrb    w0, [x0, w1, uxtw]
        .inst   0x10000061  // adr     x1, a5e4 <mldsa87_prepare_domain_separation_prefix+0x84>
        add     x0, x1, w0, sxtb #2
        br      x0
La5e4:
        mov     x1, x3
        mov     x2, x4
        add     x0, x0, #0x2
        bl      L0e50
        b       La5b0
        cmp     x2, #0x20
        b.ne    La670
La600:
        mov     w0, #0x1
        strb    w0, [x21]
        strb    w19, [x21, #1]
        cbnz    x19, La6e0
La610:
        .inst   0xb0000001  // adrp x1, 0xb000
        add     x4, x1, #0x590
        mov     w3, #0x0
        nop
La620:
        ldr     w0, [x4]
        cmp     w5, w0
        b.eq    La694
        add     w3, w3, #0x1
        add     x4, x4, #0x10
        cmp     w3, #0xc
        b.ne    La620
        add     x0, x19, #0xd
        mov     x1, x23
        mov     x2, x22
        add     x0, x21, x0
        bl      L0e50
        add     x0, x22, #0xd
        ldp     x22, x23, [sp, #16]
        add     x0, x0, x19
La65c:
        ldr     x30, [sp, #32]
        ldp     x19, x21, [sp], #64
        ret
        cmp     x2, #0x1c
        b.eq    La600
La670:
        ldp     x22, x23, [sp, #16]
        mov     x0, #0x0
        b       La5b4
        cmp     x2, #0x40
        b.eq    La600
        b       La670
        cmp     x2, #0x30
        b.eq    La600
        b       La670
La694:
        mov     x0, #0x4
        add     x1, x1, #0x590
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
        bl      L0e50
        add     x0, x22, #0xd
        ldp     x22, x23, [sp, #16]
        add     x0, x0, x19
        b       La65c
La6e0:
        mov     x1, x3
        mov     x2, x19
        add     x0, x21, #0x2
        str     w5, [sp, #60]
        bl      L0e50
        ldr     w5, [sp, #60]
        b       La610
        nop

// mldsa87_signature (0x10c bytes)
La700:
        stp     x19, x20, [sp, #-496]!
        mov     x20, x0
        .inst   0xb00000a7  // adrp x7, 0x1f000
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
        bl      La560
        cbnz    x0, La7bc
        add     x22, x19, #0x160
        mov     w26, #0xfffffff7
La75c:
        mov     x0, x20
        mov     x2, #0x1213
        mov     w1, #0x0
        bl      L0e80
La76c:
        stp     xzr, xzr, [x19, #352]
        stp     xzr, xzr, [x22, #16]
        mov     x2, #0x14c
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e80
        .inst   0xb00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #488]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    La808
        ldp     x21, x22, [sp, #16]
        mov     w0, w26
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #496
        ret
La7bc:
        add     x22, x19, #0x160
        mov     x21, x0
        mov     x1, #0x20
        mov     x0, x22
        mov     w26, #0xfffffffd
        bl      L0e60
        cbnz    w0, La75c
        mov     x6, x25
        mov     x4, x21
        mov     x2, x24
        mov     x1, x23
        mov     x5, x22
        mov     x3, x19
        mov     x0, x20
        mov     w7, #0x0
        bl      L9af0
        mov     w26, w0
        cbz     w0, La76c
        b       La75c
La808:
        bl      L0e70
        nop

// mldsa87_verify (0xbc bytes)
La810:
        stp     x19, x20, [sp, #-416]!
        mov     x20, x0
        .inst   0xb00000a6  // adrp x6, 0x1f000
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
        bl      La560
        cbz     x0, La8c0
        mov     x4, x0
        mov     x5, x22
        mov     x0, x20
        mov     x2, x23
        mov     x1, x21
        mov     x3, x19
        mov     w6, #0x0
        bl      La0b0
        mov     w20, w0
La880:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e80
        .inst   0xb00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    La8c8
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #416
        ret
La8c0:
        mov     w20, #0xfffffff7
        b       La880
La8c8:
        bl      L0e70
        nop

// mldsa87_signature_pre_hash_internal (0xd0 bytes)
La8d0:
        stp     x19, x20, [sp, #-416]!
        mov     x20, x0
        .inst   0xb00000a8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x4f
        str     x30, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        ldr     x9, [x8]
        str     x9, [sp, #408]
        mov     x9, #0x0
        cbnz    w7, La954
La900:
        mov     w21, #0xfffffff7
La904:
        mov     x0, x20
        mov     x2, #0x1213
        mov     w1, #0x0
        bl      L0e80
La914:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e80
        .inst   0xb00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #408]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    La99c
        ldr     x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #416
        ret
La954:
        mov     x21, x5
        mov     x22, x6
        mov     w5, w7
        mov     x0, x19
        bl      La560
        cbz     x0, La900
        mov     x5, x21
        mov     x2, x0
        mov     x6, x22
        mov     x1, x19
        mov     x0, x20
        mov     w7, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      L9af0
        mov     w21, w0
        cbz     w0, La914
        b       La904
La99c:
        bl      L0e70

// mldsa87_signature_pre_hash_shake256 (0xbc bytes)
La9a0:
        stp     x19, x20, [sp, #-160]!
        mov     x8, x2
        mov     x2, x1
        .inst   0xb00000a7  // adrp x7, 0x1f000
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
        bl      L12b4
        mov     x6, x24
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x0, x20
        mov     x1, x19
        mov     w7, #0xc
        mov     x2, #0x40
        bl      La8d0
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xb00000a1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #152]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    Laa58
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #160
        ret
Laa58:
        bl      L0e70
        nop

// mldsa87_verify_pre_hash_internal (0xbc bytes)
Laa60:
        stp     x19, x20, [sp, #-400]!
        .inst   0xb00000a7  // adrp x7, 0x1f000
        ldr     x7, [x7, #4088]
        str     x30, [sp, #24]
        add     x19, sp, #0x3f
        ldr     x8, [x7]
        str     x8, [sp, #392]
        mov     x8, #0x0
        and     x19, x19, #0xffffffffffffffe0
        cbz     w6, Lab0c
        mov     x20, x0
        mov     x0, x19
        str     x21, [sp, #16]
        mov     x21, x5
        mov     w5, w6
        bl      La560
        mov     x2, x0
        cbz     x0, Lab08
        mov     x5, x21
        mov     x0, x20
        mov     x1, x19
        mov     w6, #0x0
        mov     x4, #0x0
        mov     x3, #0x0
        bl      La0b0
        mov     w20, w0
        ldr     x21, [sp, #16]
Laacc:
        mov     x0, x19
        mov     x2, #0x14c
        mov     w1, #0x0
        bl      L0e80
        .inst   0xb00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #392]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    Lab14
        ldr     x30, [sp, #24]
        mov     w0, w20
        ldp     x19, x20, [sp], #400
        ret
Lab08:
        ldr     x21, [sp, #16]
Lab0c:
        mov     w20, #0xfffffff7
        b       Laacc
Lab14:
        str     x21, [sp, #16]
        bl      L0e70
        nop

// mldsa87_verify_pre_hash_shake256 (0xac bytes)
Lab20:
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
        bl      L12b4
        mov     x5, x23
        mov     x4, x22
        mov     x3, x21
        mov     x0, x20
        mov     x1, x19
        mov     w6, #0xc
        mov     x2, #0x40
        bl      Laa60
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xb00000a1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #136]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    Labc8
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #144
        ret
Labc8:
        bl      L0e70
        nop

// mldsa87_pk_from_sk (0x320 bytes)
Labd0:
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
        bl      L91e0
        mov     w1, #0x3
        mov     x0, x19
        bl      L9034
        mov     x2, x26
        mov     w1, #0x3
        mov     w25, w0
        mov     x0, x28
        bl      L9120
        mov     w27, w0
        mov     x0, x19
        bl      L8f70
        ldp     q0, q1, [x22]
        mov     x3, x28
        mov     x4, x23
        mov     x1, x24
        mov     x2, x19
        add     x0, x21, #0x20
        stp     q0, q1, [x21]
        bl      L94d0
        mov     w22, w0
        cbz     w0, Lad84
        mov     x6, #0x2d00
        mov     x7, #0x2d40
        add     x28, x19, x6
        add     x20, x19, x7
Lacd4:
        mov     x0, x21
        mov     x2, #0xa20
        mov     w1, #0x0
        bl      L0e80
Lace4:
        mov     x0, x24
        mov     x2, #0xd00
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x400
        mov     x0, x26
        mov     w1, #0x0
        bl      L0e80
        mov     x2, #0x1c00
        mov     x0, x19
        mov     w1, #0x0
        bl      L0e80
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
        b.ne    Laeec
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
Lad84:
        movi    v1.4s, #0x0
        add     x20, x20, #0x620
        mov     x0, x24
        add     x1, x24, #0xd00
        mov     v2.16b, v1.16b
Lad98:
        ldr     q0, [x20], #16
        ldr     q3, [x0], #16
        eor     v0.16b, v0.16b, v3.16b
        orr     v2.16b, v2.16b, v0.16b
        eor     v1.16b, v1.16b, v0.16b
        cmp     x1, x0
        b.ne    Lad98
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
        bl      L12b4
        movi    v0.4s, #0x0
        ldr     w4, [sp, #108]
        mov     x0, x28
        add     x2, x28, #0x40
        mov     x1, x20
        mov     v2.16b, v0.16b
Lae54:
        ldr     q1, [x0], #16
        ldr     q3, [x1], #16
        eor     v1.16b, v1.16b, v3.16b
        orr     v2.16b, v2.16b, v1.16b
        eor     v0.16b, v0.16b, v1.16b
        cmp     x0, x2
        b.ne    Lae54
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
        b.eq    Lace4
        mov     w22, #0xfffffff9
        b       Lacd4
Laeec:
        bl      L0e70

// Padding (0xaef0 to 0xaef0)


// The read-only data (0xaef0 to 0xb650)

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
