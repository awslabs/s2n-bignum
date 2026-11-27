// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// The code and read-only data of mlkem-native's libmlkem.so (gcc 12, -Os)
//
// This is a transcription of the binary
// binaries/aarch64/multilevel/gcc12/Os/libmlkem.so from the binary branch
// of mlkem-native (see README.md), as loaded at an address that is a
// multiple of 4096: the start of its first segment, from address 0 up to
// the end of the read-only data. The ELF header and dynamic linking
// information at the start are given as data, as are the padding and the
// read-only data at the end, while the procedure linkage table and the code
// are given as instructions. The ADRP instructions, which compute addresses
// of pages relative to that of the instruction, are given as words. The
// labels are named after the addresses in the binary.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_libmlkem_gcc12_Os)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_libmlkem_gcc12_Os)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_libmlkem_gcc12_Os):

// ELF header and dynamic linking information (0x0 to 0x7f0)

        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x0000000100b70003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x0000000000024f08
        .quad   0x0038004000000000
        .quad   0x0019001a00400005
        .quad   0x0000000500000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000006fc0
        .quad   0x0000000000006fc0
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
        .quad   0x0000001c00000011
        .quad   0x0000000d00000016
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001800000014
        .quad   0x0000000a00000011
        .quad   0x0000000f00000000
        .quad   0x0000000600000005
        .quad   0x0000001500000007
        .quad   0x0000000000000008
        .quad   0x0000000000000000
        .quad   0x0000001900000000
        .quad   0x0000001b00000000
        .quad   0x0000001300000000
        .quad   0x0000000e00000000
        .quad   0x0000000000000000
        .quad   0x0000001a00000017
        .quad   0x0000000000000009
        .quad   0x0000000000000003
        .quad   0x000000040000000c
        .quad   0x000000120000000b
        .quad   0x0000001000000000
        .quad   0x0000000000000002
        .quad   0x0000000000000000
        .quad   0x0000000700000011
        .quad   0x0000000700000002
        .quad   0x10e2681100ba0008
        .quad   0x4e41e1a21018344c
        .quad   0x0000000000000007
        .quad   0x0000000a00000008
        .quad   0x0000000b00000000
        .quad   0x0000000f0000000e
        .quad   0x0000001200000010
        .quad   0x0000000000000015
        .quad   0x0000001800000017
        .quad   0x0000001a00000019
        .quad   0x16c2d2ff00000000
        .quad   0xb06297357ef0d7dc
        .quad   0xe75d09fabccdaaab
        .quad   0x7ef0d7792fce7b36
        .quad   0x7fad8555ee0ec8b7
        .quad   0x884de195e75d0996
        .quad   0x835a16e0a53138a4
        .quad   0xd2675e2c16c2d869
        .quad   0xbccdb015d9726a43
        .quad   0xee0ec34dd2675dcb
        .quad   0x94bd4643ae74fb66
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0008000300000000
        .quad   0x0000000000000850
        .quad   0x0000000000000000
        .quad   0x0000001000000008
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000100000006a
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000083
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000100000001a
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000800120000012e
        .quad   0x0000000000003ba4
        .quad   0x0000000000000188
        .quad   0x000800120000003e
        .quad   0x00000000000010e8
        .quad   0x0000000000000090
        .quad   0x000800120000010d
        .quad   0x0000000000003a14
        .quad   0x00000000000000ec
        .quad   0x00080012000001a9
        .quad   0x0000000000005540
        .quad   0x000000000000018c
        .quad   0x000800120000014d
        .quad   0x000000000000520c
        .quad   0x0000000000000090
        .quad   0x0008001200000071
        .quad   0x00000000000011f8
        .quad   0x0000000000000094
        .quad   0x000800120000002b
        .quad   0x0000000000001030
        .quad   0x00000000000000b8
        .quad   0x00080012000000a4
        .quad   0x0000000000001378
        .quad   0x00000000000000a4
        .quad   0x00080012000000e4
        .quad   0x0000000000003900
        .quad   0x0000000000000080
        .quad   0x000800120000013b
        .quad   0x0000000000005154
        .quad   0x00000000000000b8
        .quad   0x0008001200000177
        .quad   0x000000000000531c
        .quad   0x0000000000000094
        .quad   0x000800120000008f
        .quad   0x000000000000128c
        .quad   0x00000000000000ec
        .quad   0x000800120000015f
        .quad   0x000000000000529c
        .quad   0x0000000000000080
        .quad   0x0008001200000121
        .quad   0x0000000000003b00
        .quad   0x00000000000000a4
        .quad   0x00080012000000d2
        .quad   0x0000000000003870
        .quad   0x0000000000000090
        .quad   0x0008001200000188
        .quad   0x00000000000053b0
        .quad   0x00000000000000ec
        .quad   0x000800120000019c
        .quad   0x000000000000549c
        .quad   0x00000000000000a4
        .quad   0x00080012000000c0
        .quad   0x00000000000037b8
        .quad   0x00000000000000b8
        .quad   0x00080012000000b2
        .quad   0x000000000000141c
        .quad   0x000000000000018c
        .quad   0x00080012000000fc
        .quad   0x0000000000003980
        .quad   0x0000000000000094
        .quad   0x0008001200000051
        .quad   0x0000000000001178
        .quad   0x0000000000000080
        .quad   0x007465736d656d00
        .quad   0x5f6b636174735f5f
        .quad   0x726175675f6b6863
        .quad   0x636174735f5f0064
        .quad   0x61665f6b68635f6b
        .quad   0x6d656b6c6d006c69
        .quad   0x6568635f34323031
        .quad   0x6c6d006b705f6b63
        .quad   0x5f343230316d656b
        .quad   0x6b735f6b63656863
        .quad   0x30316d656b6c6d00
        .quad   0x617079656b5f3432
        .quad   0x6e617265645f7269
        .quad   0x7970636d656d0064
        .quad   0x30316d656b6c6d00
        .quad   0x617079656b5f3432
        .quad   0x6f646e6172007269
        .quad   0x6d0073657479626d
        .quad   0x343230316d656b6c
        .quad   0x7265645f636e655f
        .quad   0x656b6c6d00646e61
        .quad   0x6e655f343230316d
        .quad   0x316d656b6c6d0063
        .quad   0x006365645f343230
        .quad   0x3231356d656b6c6d
        .quad   0x705f6b636568635f
        .quad   0x356d656b6c6d006b
        .quad   0x6b636568635f3231
        .quad   0x656b6c6d006b735f
        .quad   0x79656b5f3231356d
        .quad   0x7265645f72696170
        .quad   0x656b6c6d00646e61
        .quad   0x79656b5f3231356d
        .quad   0x6b6c6d0072696170
        .quad   0x6e655f3231356d65
        .quad   0x646e617265645f63
        .quad   0x31356d656b6c6d00
        .quad   0x6c6d00636e655f32
        .quad   0x645f3231356d656b
        .quad   0x6d656b6c6d006365
        .quad   0x636568635f383637
        .quad   0x6b6c6d006b705f6b
        .quad   0x68635f3836376d65
        .quad   0x6d006b735f6b6365
        .quad   0x5f3836376d656b6c
        .quad   0x5f7269617079656b
        .quad   0x6d00646e61726564
        .quad   0x5f3836376d656b6c
        .quad   0x007269617079656b
        .quad   0x3836376d656b6c6d
        .quad   0x7265645f636e655f
        .quad   0x656b6c6d00646e61
        .quad   0x636e655f3836376d
        .quad   0x36376d656b6c6d00
        .quad   0x696c006365645f38
        .quad   0x732e6d656b6c6d62
        .quad   0x622f706d742f006f
        .quad   0x32762d7972616e69
        .quad   0x69756265722d312e
        .quad   0x37446d76492e646c
        .quad   0x2d6d656b6c6d2f45
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

// The procedure linkage table and the code (0x7f0 to 0x5a6c)
// .plt
        stp     x16, x30, [sp, #-16]!
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4040]
        add     x16, x16, #0xfc8
        br      x17
        nop
        nop
        nop
L0810:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4048]
        add     x16, x16, #0xfd0
        br      x17
L0820:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4056]
        add     x16, x16, #0xfd8
        br      x17
L0830:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4064]
        add     x16, x16, #0xfe0
        br      x17
L0840:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4072]
        add     x16, x16, #0xfe8
        br      x17

// mlk_zeroize (0x1c bytes)
L0850:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0840
        ldp     x19, x30, [sp], #16
        ret

// mlkem1024_gen_matrix (0x134 bytes)
L086c:
        stp     x19, x20, [sp, #-368]!
        mov     x20, x0
        mov     w5, #0x4
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x19, sp, #0x6f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     w22, w2
        stp     x23, x24, [sp, #32]
        stp     x25, x26, [sp, #48]
        str     x30, [sp, #64]
        ldr     x2, [x0]
        str     x2, [sp, #360]
        mov     x2, #0x0
        mov     x0, x19
L08ac:
        ldp     q0, q1, [x1]
        subs    w5, w5, #0x1
        stp     q0, q1, [x0]
        add     x0, x0, #0x40
        b.ne    L08ac
        mov     w23, #0x800
        mov     x24, #0x600
        mov     x25, #0x400
        mov     x26, #0x200
L08d0:
        mov     x1, x19
        mov     w0, w5
        add     w21, w5, #0x4
L08dc:
        ubfx    x3, x0, #2, #8
        and     w2, w0, #0x3
        cbnz    w22, L08f4
        mov     w4, w2
        mov     w2, w3
        mov     w3, w4
L08f4:
        add     w0, w0, #0x1
        strb    w3, [x1, #32]
        strb    w2, [x1, #33]
        add     x1, x1, #0x40
        cmp     w21, w0
        b.ne    L08dc
        add     w3, w5, #0x3
        add     w0, w5, #0x2
        add     w1, w5, #0x1
        lsr     w5, w5, #2
        lsr     w3, w3, #2
        lsr     w0, w0, #2
        lsr     w1, w1, #2
        mov     x4, x19
        umaddl  x0, w0, w23, x25
        umaddl  x3, w3, w23, x24
        umaddl  x1, w1, w23, x26
        add     x2, x20, x0
        add     x3, x20, x3
        add     x0, x20, x5, lsl #11
        add     x1, x20, x1
        bl      L45b8
        cmp     w21, #0x10
        b.eq    L095c
        mov     w5, w21
        b       L08d0
L095c:
        mov     x0, x19
        mov     x1, #0x100
        bl      L0850
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #360]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L0988
        bl      L0830
L0988:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #368
        ret

// mlkem1024_indcpa_keypair_derand (0x230 bytes)
L09a0:
        mov     x12, #0x3d10
        sub     sp, sp, x12
        mov     x3, #0x3c40
        mov     x4, #0x3c00
        mov     x5, #0x3800
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0x9f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        mov     x22, x0
        add     x21, x19, #0x3, lsl #12
        stp     x23, x24, [sp, #48]
        add     x23, x19, x4
        add     x20, x19, #0x2, lsl #12
        stp     x25, x26, [sp, #64]
        add     x25, x19, x3
        mov     w26, #0x4
        stp     x27, x28, [sp, #80]
        add     x27, x19, x5
        add     x24, x23, #0x20
        str     x30, [sp, #96]
        mov     w28, #0x0
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        str     x1, [sp, #112]
        ldp     q0, q1, [x2]
        ldr     x1, [x0]
        str     x1, [sp, #15624]
        mov     x1, #0x0
        mov     x1, x25
        mov     x0, x23
        mov     x2, #0x21
        stp     q0, q1, [x25]
        strb    w26, [x21, #3168]
        bl      L2508
        mov     x1, x23
        mov     x0, x19
        mov     w2, #0x0
        bl      L086c
        mov     w0, #0x3
        strb    w0, [sp]
        mov     x4, x24
        add     x3, x20, #0x600
        add     x2, x20, #0x400
        add     x1, x20, #0x200
        mov     x0, x20
        mov     w7, #0x2
        mov     w6, #0x1
        mov     w5, #0x0
        bl      L1850
        mov     w5, w26
        mov     x4, x24
        add     x3, x21, #0x600
        add     x2, x21, #0x400
        add     x1, x21, #0x200
        mov     w0, #0x7
        strb    w0, [sp]
        mov     w6, #0x5
        mov     w7, #0x6
        mov     x0, x21
        bl      L1850
        mov     x0, x20
        bl      L1698
        mov     x0, x21
        bl      L1698
        mov     x1, x20
        mov     x0, x27
        bl      L178c
        mov     x6, #0x2800
        add     x26, x19, x6
        mov     x1, x19
        mov     x24, x26
L0ac0:
        mov     x0, x26
        mov     x3, x27
        mov     x2, x20
        str     x1, [sp, #120]
        bl      L16e8
        add     w28, w28, #0x1
        ldr     x1, [sp, #120]
        add     x26, x26, #0x200
        add     x1, x1, #0x800
        cmp     w28, #0x4
        b.ne    L0ac0
        mov     x0, x24
        bl      L1828
        mov     x1, x21
        mov     x0, x24
        bl      L17f0
        mov     x0, x24
        bl      L17c8
        mov     x0, x20
        bl      L17c8
        ldr     x0, [sp, #112]
        mov     x1, x20
        bl      L1620
        mov     x0, x22
        mov     x1, x24
        bl      L1620
        add     x22, x22, #0x600
        ldp     q0, q1, [x23]
        mov     x0, x27
        mov     x1, #0x400
        stp     q0, q1, [x22]
        bl      L0850
        mov     x0, x20
        mov     x1, #0x800
        bl      L0850
        mov     x0, x24
        mov     x1, #0x800
        bl      L0850
        mov     x0, x21
        mov     x1, #0x800
        bl      L0850
        mov     x0, x19
        mov     x1, #0x2000
        bl      L0850
        mov     x0, x25
        mov     x1, #0x21
        bl      L0850
        mov     x0, x23
        mov     x1, #0x40
        bl      L0850
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #15624]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L0ba8
        bl      L0830
L0ba8:
        ldp     x19, x20, [sp, #16]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x3d10
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret

// mlkem1024_indcpa_enc (0x2b4 bytes)
L0bd0:
        mov     x12, #0x4ad0
        sub     sp, sp, x12
        stp     x25, x26, [sp, #64]
        mov     x25, x0
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0xaf
        stp     x21, x22, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x20, x2
        stp     x23, x24, [sp, #48]
        mov     x2, #0x4400
        mov     x22, x1
        stp     x27, x28, [sp, #80]
        mov     x1, #0x4600
        add     x26, x19, #0x3, lsl #12
        str     x30, [sp, #96]
        add     x27, x19, x1
        mov     x21, x3
        add     x28, x19, x2
        ldr     x1, [x0]
        str     x1, [sp, #19144]
        mov     x1, #0x0
        mov     x0, x26
        mov     x1, x20
        bl      L165c
        ldr     q0, [x20, #1536]
        mov     x3, #0x4a00
        ldr     q1, [x20, #1552]
        add     x0, x19, x3
        mov     x4, #0x2800
        mov     x1, x22
        add     x22, x19, x4
        add     x24, x19, #0x4, lsl #12
        stp     q0, q1, [x0]
        mov     x0, x27
        bl      L217c
        mov     x5, #0x4a00
        mov     x6, #0x3800
        add     x0, x19, x5
        add     x20, x19, x6
        mov     x1, x0
        mov     w2, #0x1
        str     x0, [sp, #120]
        mov     x0, x19
        bl      L086c
        mov     w0, #0x3
        strb    w0, [sp]
        mov     x4, x21
        add     x3, x20, #0x600
        add     x2, x20, #0x400
        add     x1, x20, #0x200
        mov     x0, x20
        mov     w7, #0x2
        mov     w6, #0x1
        mov     w5, #0x0
        bl      L1850
        mov     w0, #0x7
        strb    w0, [sp]
        mov     x4, x21
        add     x3, x22, #0x600
        mov     w7, #0x6
        mov     w6, #0x5
        mov     w5, #0x4
        add     x2, x22, #0x400
        add     x1, x22, #0x200
        mov     x0, x22
        bl      L1850
        mov     x1, x21
        mov     w2, #0x8
        mov     x0, x28
        bl      L1994
        mov     x0, x20
        add     x21, x19, #0x2, lsl #12
        bl      L1698
        mov     x23, x21
        mov     x1, x20
        mov     x0, x24
        bl      L178c
        mov     x1, x19
        mov     w4, #0x0
L0d18:
        mov     x0, x21
        mov     x3, x24
        mov     x2, x20
        str     x1, [sp, #128]
        str     w4, [sp, #140]
        bl      L16e8
        ldr     x1, [sp, #128]
        add     x21, x21, #0x200
        ldr     w4, [sp, #140]
        add     x1, x1, #0x800
        add     w4, w4, #0x1
        cmp     w4, #0x4
        b.ne    L0d18
        mov     x2, x20
        mov     x3, x24
        mov     x1, x26
        mov     x0, #0x4800
        add     x21, x19, x0
        mov     x0, x21
        bl      L16e8
        mov     x0, x23
        bl      L16c0
        mov     x0, x21
        bl      L3f18
        mov     x1, x22
        mov     x0, x23
        bl      L17f0
        mov     x1, x28
        mov     x0, x21
        bl      L3db8
        mov     x1, x27
        mov     x0, x21
        bl      L3db8
        mov     x0, x23
        bl      L17c8
        mov     x0, x21
        bl      L3d68
        mov     x1, x23
        mov     x0, x25
        bl      L15a8
        mov     x1, x21
        add     x0, x25, #0x580
        bl      L1ce0
        mov     x0, x24
        mov     x1, #0x400
        bl      L0850
        mov     x0, x28
        mov     x1, #0x200
        bl      L0850
        mov     x0, x27
        mov     x1, #0x200
        bl      L0850
        mov     x0, x21
        mov     x1, #0x200
        bl      L0850
        mov     x0, x23
        mov     x1, #0x800
        bl      L0850
        mov     x0, x22
        mov     x1, #0x800
        bl      L0850
        mov     x0, x26
        mov     x1, #0x800
        bl      L0850
        mov     x0, x20
        mov     x1, #0x800
        bl      L0850
        mov     x0, x19
        mov     x1, #0x2000
        bl      L0850
        ldr     x0, [sp, #120]
        mov     x1, #0x20
        bl      L0850
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #19144]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L0e5c
        bl      L0830
L0e5c:
        ldp     x19, x20, [sp, #16]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x4ad0
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret

// mlkem1024_indcpa_dec (0x144 bytes)
L0e84:
        mov     x12, #0x1860
        sub     sp, sp, x12
        stp     x23, x24, [sp, #32]
        mov     x24, x0
        mov     x23, x1
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x5f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     x22, x2
        str     x30, [sp, #48]
        mov     x2, #0x1600
        add     x21, x19, x2
        add     x20, x19, #0x800
        ldr     x2, [x0]
        str     x2, [sp, #6232]
        mov     x2, #0x0
        mov     x0, x20
        bl      L15e4
        add     x1, x23, #0x580
        mov     x0, x21
        bl      L1ee8
        add     x23, x19, #0x1, lsl #12
        mov     x1, x22
        mov     x0, x19
        bl      L165c
        mov     x0, x20
        bl      L1698
        mov     x1, x20
        mov     x0, x23
        bl      L178c
        mov     x3, #0x1400
        mov     x2, x20
        add     x22, x19, x3
        mov     x1, x19
        mov     x3, x23
        mov     x0, x22
        bl      L16e8
        mov     x0, x22
        bl      L3f18
        mov     x1, x22
        mov     x0, x21
        bl      L3ddc
        mov     x0, x21
        bl      L3d68
        mov     x1, x21
        mov     x0, x24
        bl      L21cc
        mov     x0, x23
        mov     x1, #0x400
        bl      L0850
        mov     x0, x22
        mov     x1, #0x200
        bl      L0850
        mov     x0, x21
        mov     x1, #0x200
        bl      L0850
        mov     x0, x19
        mov     x1, #0x800
        bl      L0850
        mov     x0, x20
        mov     x1, #0x800
        bl      L0850
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #6232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L0fa8
        bl      L0830
L0fa8:
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x1860
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        add     sp, sp, x12
        ret

// mlk_ct_memcmp (0x4c bytes)
L0fc8:
        mov     w6, #0x0
        mov     w5, #0x0
        mov     w3, #0x0
L0fd4:
        mov     w7, w6
        cmp     x2, w6, uxtw
        b.hi    L0ff4
        neg     w1, w3
        eor     w1, w5, w1, asr #16
        and     w1, w1, #0xff
        eor     w0, w5, w1
        ret
L0ff4:
        ldrb    w4, [x0, x7]
        add     w6, w6, #0x1
        ldrb    w7, [x1, x7]
        eor     w4, w4, w7
        and     w4, w4, #0xff
        orr     w3, w4, w3
        eor     w5, w4, w5
        b       L0fd4

// mlk_zeroize (0x1c bytes)
L1014:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0840
        ldp     x19, x30, [sp], #16
        ret

// mlkem1024_check_pk (0xb8 bytes)
L1030:
        sub     sp, sp, #0xe40
        stp     x19, x20, [sp]
        mov     x20, x0
        add     x19, sp, #0x3f
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x30, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #3640]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, x20
        bl      L165c
        add     x21, x19, #0x800
        mov     x0, x19
        bl      L17c8
        mov     x1, x19
        mov     x0, x21
        bl      L1620
        mov     x2, #0x600
        mov     x1, x21
        mov     x0, x20
        bl      L0fc8
        tst     w0, #0xff
        mov     x1, x2
        mov     x0, x21
        mov     w20, #0xfffffffc
        csel    w20, wzr, w20, eq
        bl      L1014
        mov     x0, x19
        mov     x1, #0x800
        bl      L1014
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #3640]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L10d4
        bl      L0830
L10d4:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp]
        add     sp, sp, #0xe40
        ret

// mlkem1024_check_sk (0x90 bytes)
L10e8:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        mov     x2, #0x620
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x3f
        and     x19, x19, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #88]
        mov     x1, #0x0
        add     x1, x20, #0x600
        mov     x0, x19
        bl      L247c
        mov     x2, #0x20
        mov     x1, x19
        add     x0, x20, #0xc20
        bl      L0fc8
        tst     w0, #0xff
        mov     x1, x2
        mov     x0, x19
        mov     w20, #0xfffffffb
        csel    w20, wzr, w20, eq
        bl      L1014
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1168
        bl      L0830
L1168:
        ldr     x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #96
        ret

// mlkem1024_keypair_derand (0x80 bytes)
L1178:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x0
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        str     x30, [sp, #32]
        bl      L09a0
        mov     w21, w0
        cbz     w0, L11c8
        mov     x0, x20
        mov     x1, #0x620
        bl      L1014
        mov     x0, x19
        mov     x1, #0xc60
        bl      L1014
L11b4:
        ldr     x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret
L11c8:
        mov     x1, x20
        add     x0, x19, #0x600
        mov     x2, #0x620
        bl      L0810
        add     x0, x19, #0xc20
        mov     x1, x20
        mov     x2, #0x620
        bl      L247c
        ldp     q0, q1, [x22, #32]
        add     x19, x19, #0xc40
        stp     q0, q1, [x19]
        b       L11b4

// mlkem1024_keypair (0x94 bytes)
L11f8:
        stp     x19, x20, [sp, #-128]!
        mov     x20, x0
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x30, [sp, #16]
        add     x19, sp, #0x3f
        mov     x21, x1
        and     x19, x19, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #120]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x40
        bl      L0820
        cbnz    w0, L1274
        mov     x0, x20
        mov     x2, x19
        mov     x1, x21
        bl      L1178
        mov     w20, w0
L1248:
        mov     x0, x19
        mov     x1, #0x40
        bl      L1014
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #120]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L127c
        bl      L0830
L1274:
        mov     w20, #0xfffffffd
        b       L1248
L127c:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #128
        ret

// mlkem1024_enc_derand (0xec bytes)
L128c:
        stp     x19, x20, [sp, #-224]!
        stp     x25, x30, [sp, #48]
        mov     x25, x0
        add     x19, sp, #0x5f
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        mov     x22, x2
        ldr     x1, [x0]
        str     x1, [sp, #216]
        mov     x1, #0x0
        mov     x24, x3
        mov     x0, x2
        add     x21, x19, #0x40
        bl      L1030
        mov     w20, w0
        cbnz    w0, L1328
        ldp     q0, q1, [x24]
        mov     x1, x22
        add     x0, x19, #0x60
        mov     x2, #0x620
        stp     q0, q1, [x21]
        bl      L247c
        mov     x1, x21
        mov     x0, x19
        mov     x2, #0x40
        bl      L2508
        add     x3, x19, #0x20
        mov     x2, x22
        mov     x1, x21
        mov     x0, x25
        bl      L0bd0
        mov     w20, w0
        cbnz    w0, L1328
        ldp     q0, q1, [x19]
        stp     q0, q1, [x23]
L1328:
        mov     x0, x19
        mov     x1, #0x40
        bl      L1014
        mov     x0, x21
        mov     x1, #0x40
        bl      L1014
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #216]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1360
        bl      L0830
L1360:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #224
        ret

// mlkem1024_enc (0xa4 bytes)
L1378:
        stp     x19, x20, [sp, #-112]!
        mov     x20, x0
        .inst   0xd00000e0  // adrp x0, 0x1f000
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
        bl      L0820
        cbnz    w0, L1400
        mov     x0, x20
        mov     x3, x19
        mov     x2, x22
        mov     x1, x21
        bl      L128c
        mov     w20, w0
L13d4:
        mov     x0, x19
        mov     x1, #0x20
        bl      L1014
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #104]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1408
        bl      L0830
L1400:
        mov     w20, #0xfffffffd
        b       L13d4
L1408:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret

// mlkem1024_dec (0x18c bytes)
L141c:
        sub     sp, sp, #0x730
        stp     x23, x24, [sp, #32]
        mov     x23, x0
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x6f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x2
        stp     x25, x26, [sp, #48]
        mov     x25, x1
        add     x22, x19, #0x680
        str     x30, [sp, #64]
        add     x24, x19, #0x640
        ldr     x1, [x0]
        str     x1, [sp, #1832]
        mov     x1, #0x0
        mov     x0, x2
        bl      L10e8
        mov     w20, w0
        cbnz    w0, L1544
        mov     x2, x21
        mov     x1, x25
        mov     x0, x22
        bl      L0e84
        mov     w20, w0
        cbnz    w0, L1544
        ldr     q0, [x21, #3104]
        add     x0, x19, #0x6a0
        ldr     q1, [x21, #3120]
        mov     x1, x22
        mov     x2, #0x40
        stp     q0, q1, [x0]
        mov     x0, x24
        bl      L2508
        add     x3, x19, #0x660
        add     x2, x21, #0x600
        mov     x1, x22
        mov     x0, x19
        bl      L0bd0
        mov     w20, w0
        cbnz    w0, L1544
        mov     x2, #0x620
        mov     x1, x19
        mov     x0, x25
        bl      L0fc8
        ldr     q0, [x21, #3136]
        and     w26, w0, #0xff
        ldr     q1, [x21, #3152]
        mov     x1, x25
        add     x0, x19, #0x20
        neg     w26, w26
        stp     q0, q1, [x19]
        bl      L0810
        mov     x0, x22
        mov     x3, #0x640
        mov     x2, x19
        mov     x1, #0x20
        bl      L23f0
        mov     x3, x22
        mov     x0, #0x0
L1514:
        ldrb    w2, [x24, x0]
        mov     w1, w26
        ldrb    w4, [x3]
        add     x0, x0, #0x1
        eor     w4, w2, w4
        and     w1, w4, w1, asr #16
        eor     w2, w2, w1
        strb    w2, [x3], #1
        cmp     x0, #0x20
        b.ne    L1514
        ldp     q0, q1, [x22]
        stp     q0, q1, [x23]
L1544:
        mov     x0, x19
        mov     x1, #0x640
        bl      L1014
        mov     x0, x24
        mov     x1, #0x40
        bl      L1014
        mov     x0, x22
        mov     x1, #0x40
        bl      L1014
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1832]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1588
        bl      L0830
L1588:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        add     sp, sp, #0x730
        ret

// mlkem1024_polyvec_compress_du (0x3c bytes)
L15a8:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x580
L15bc:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x160
        bl      L1dcc
        add     x20, x20, #0x200
        cmp     x19, x21
        b.ne    L15bc
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mlkem1024_polyvec_decompress_du (0x3c bytes)
L15e4:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x800
L15f8:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x200
        bl      L1fe0
        add     x20, x20, #0x160
        cmp     x19, x21
        b.ne    L15f8
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mlkem1024_polyvec_tobytes (0x3c bytes)
L1620:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x600
L1634:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x180
        bl      L210c
        add     x20, x20, #0x200
        cmp     x19, x21
        b.ne    L1634
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mlkem1024_polyvec_frombytes (0x3c bytes)
L165c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x800
L1670:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x200
        bl      L2144
        add     x20, x20, #0x180
        cmp     x19, x21
        b.ne    L1670
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mlkem1024_polyvec_ntt (0x28 bytes)
L1698:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L3e74
        add     x0, x19, #0x200
        bl      L3e74
        add     x0, x19, #0x400
        bl      L3e74
        add     x0, x19, #0x600
        ldp     x19, x30, [sp], #16
        b       L3e74

// mlkem1024_polyvec_invntt_tomont (0x28 bytes)
L16c0:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L3f18
        add     x0, x19, #0x200
        bl      L3f18
        add     x0, x19, #0x400
        bl      L3f18
        add     x0, x19, #0x600
        ldp     x19, x30, [sp], #16
        b       L3f18

// mlkem1024_polyvec_basemul_acc_montgomery_cached (0xa4 bytes)
L16e8:
        add     x16, x0, #0x2
        mov     x4, #0x0
        mov     w12, #0xfffff301
        mov     w13, #0xfffff2ff
L16f8:
        add     x9, x4, #0x2
        mov     x8, x4
        mov     x5, #0x0
        mov     w7, #0x0
        mov     w6, #0x0
L170c:
        lsl     x11, x5, #8
        ldrsh   w14, [x1, x8]
        ldrsh   w15, [x2, x8]
        add     x5, x5, #0x1
        ldrsh   w10, [x1, x9]
        add     x8, x8, #0x200
        ldrsh   w11, [x3, x11]
        mul     w17, w14, w15
        madd    w11, w11, w10, w17
        mul     w10, w10, w15
        add     w6, w6, w11
        ldrsh   w11, [x2, x9]
        add     x9, x9, #0x200
        madd    w10, w11, w14, w10
        add     w7, w7, w10
        cmp     x5, #0x4
        b.ne    L170c
        mul     w5, w6, w12
        add     x3, x3, #0x2
        sxth    w5, w5
        madd    w5, w5, w13, w6
        asr     w5, w5, #16
        strh    w5, [x0, x4]
        mul     w5, w7, w12
        sxth    w5, w5
        madd    w5, w5, w13, w7
        asr     w5, w5, #16
        strh    w5, [x16, x4]
        add     x4, x4, #0x4
        cmp     x4, #0x200
        b.ne    L16f8
        ret

// mlkem1024_polyvec_mulcache_compute (0x3c bytes)
L178c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x400
L17a0:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x100
        bl      L3e00
        add     x20, x20, #0x200
        cmp     x19, x21
        b.ne    L17a0
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mlkem1024_polyvec_reduce (0x28 bytes)
L17c8:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L3d68
        add     x0, x19, #0x200
        bl      L3d68
        add     x0, x19, #0x400
        bl      L3d68
        add     x0, x19, #0x600
        ldp     x19, x30, [sp], #16
        b       L3d68

// mlkem1024_polyvec_add (0x38 bytes)
L17f0:
        stp     x19, x20, [sp, #-32]!
        mov     x20, x0
        mov     x19, #0x0
        stp     x21, x30, [sp, #16]
        mov     x21, x1
L1804:
        add     x1, x21, x19
        add     x0, x20, x19
        add     x19, x19, #0x200
        bl      L3db8
        cmp     x19, #0x800
        b.ne    L1804
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mlkem1024_polyvec_tomont (0x28 bytes)
L1828:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L3d2c
        add     x0, x19, #0x200
        bl      L3d2c
        add     x0, x19, #0x400
        bl      L3d2c
        add     x0, x19, #0x600
        ldp     x19, x30, [sp], #16
        b       L3d2c

// mlkem1024_poly_getnoise_eta1_4x (0x144 bytes)
L1850:
        sub     sp, sp, #0x380
        stp     x23, x24, [sp, #48]
        mov     x24, x0
        mov     x23, x1
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0x7f
        stp     x21, x22, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        add     x20, x19, #0x200
        stp     x25, x26, [sp, #64]
        mov     x22, x2
        ldrb    w2, [sp, #896]
        stp     x27, x30, [sp, #80]
        add     x26, x19, #0x100
        add     x25, x19, #0x180
        ldp     q0, q1, [x4]
        ldr     x1, [x0]
        str     x1, [sp, #888]
        mov     x1, #0x0
        add     x1, x19, #0x280
        add     x0, x19, #0x240
        add     x4, x19, #0x2c0
        strb    w5, [x20, #32]
        stp     q0, q1, [x20]
        mov     x5, x20
        mov     x21, x3
        stp     q0, q1, [x0]
        mov     x3, x25
        add     x27, x19, #0x80
        stp     q0, q1, [x1]
        stp     q0, q1, [x4]
        strb    w6, [x20, #96]
        mov     x6, x0
        strb    w7, [x20, #160]
        mov     x7, x1
        strb    w2, [x20, #224]
        mov     x2, #0x21
        stp     x4, x2, [sp]
        mov     x2, x26
        mov     x4, #0x80
        mov     x1, x27
        mov     x0, x19
        bl      L2800
        mov     x1, x19
        mov     x0, x24
        bl      L4878
        mov     x1, x27
        mov     x0, x23
        bl      L4878
        mov     x1, x26
        mov     x0, x22
        bl      L4878
        cbz     x21, L1938
        mov     x1, x25
        mov     x0, x21
        bl      L4878
L1938:
        mov     x0, x19
        mov     x2, #0x200
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x100
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #888]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1978
        bl      L0830
L1978:
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x30, [sp, #80]
        add     sp, sp, #0x380
        ret

// mlkem1024_poly_getnoise_eta2 (0xa0 bytes)
L1994:
        stp     x19, x20, [sp, #-240]!
        add     x19, sp, #0x3f
        stp     x21, x30, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        add     x20, x19, #0x80
        mov     x21, x0
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldp     q0, q1, [x1]
        ldr     x3, [x0]
        str     x3, [sp, #232]
        mov     x3, #0x0
        strb    w2, [x20, #32]
        mov     x2, x20
        mov     x3, #0x21
        mov     x0, x19
        mov     x1, #0x80
        stp     q0, q1, [x20]
        bl      L23f0
        mov     x1, x19
        mov     x0, x21
        bl      L4878
        mov     x0, x19
        mov     x2, #0x80
        mov     w1, #0x0
        bl      L0840
        stp     xzr, xzr, [x19, #128]
        stp     xzr, xzr, [x20, #16]
        strb    wzr, [x20, #32]
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1a28
        bl      L0830
L1a28:
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #240
        ret

// mlkem_poly_compress_d4 (0xcc bytes)
L1a34:
        .inst   0xd00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        mov     w6, #0xafb0
        mov     w4, #0x0
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
        add     x5, sp, #0x10
        movk    w6, #0x13, lsl #16
        mov     w7, #0x8000000
L1a60:
        mov     x2, #0x0
        str     xzr, [sp, #16]
L1a68:
        add     w3, w4, w2
        ldrsh   w3, [x1, x3, lsl #1]
        madd    w3, w3, w6, w7
        lsr     w3, w3, #28
        strb    w3, [x2, x5]
        add     x2, x2, #0x1
        cmp     x2, #0x8
        b.ne    L1a68
        ldrb    w3, [sp, #16]
        add     w4, w4, #0x8
        ldrb    w2, [sp, #17]
        add     x0, x0, #0x4
        orr     w2, w3, w2, lsl #4
        ldrb    w3, [sp, #18]
        sturb   w2, [x0, #-4]
        ldrb    w2, [sp, #19]
        orr     w2, w3, w2, lsl #4
        ldrb    w3, [sp, #20]
        sturb   w2, [x0, #-3]
        ldrb    w2, [sp, #21]
        orr     w2, w3, w2, lsl #4
        ldrb    w3, [sp, #22]
        sturb   w2, [x0, #-2]
        ldrb    w2, [sp, #23]
        orr     w2, w3, w2, lsl #4
        sturb   w2, [x0, #-1]
        cmp     w4, #0x100
        b.ne    L1a60
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1af8
        bl      L0830
L1af8:
        ldr     x30, [sp], #32
        ret

// mlkem_poly_compress_d10 (0xc8 bytes)
L1b00:
        .inst   0xd00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        mov     x5, #0xbc00
        mov     w4, #0x0
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
        add     x7, sp, #0x10
        movk    x5, #0x9d7d, lsl #16
        mov     x6, #0x100000000
L1b2c:
        mov     x2, #0x0
L1b30:
        add     w3, w4, w2
        ldrsh   x3, [x1, x3, lsl #1]
        madd    x3, x3, x5, x6
        ubfx    x3, x3, #33, #10
        strh    w3, [x7, x2, lsl #1]
        add     x2, x2, #0x1
        cmp     x2, #0x4
        b.ne    L1b30
        ldrh    w2, [sp, #18]
        add     w4, w4, #0x4
        ldrh    w3, [sp, #16]
        add     x0, x0, #0x5
        sturb   w3, [x0, #-5]
        lsl     w8, w2, #2
        orr     w3, w8, w3, lsr #8
        sturb   w3, [x0, #-4]
        ldrh    w3, [sp, #20]
        lsl     w8, w3, #4
        orr     w2, w8, w2, lsr #6
        sturb   w2, [x0, #-3]
        ldrh    w2, [sp, #22]
        lsl     w8, w2, #6
        lsr     w2, w2, #2
        orr     w3, w8, w3, lsr #4
        sturb   w3, [x0, #-2]
        sturb   w2, [x0, #-1]
        cmp     w4, #0x100
        b.ne    L1b2c
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1bc0
        bl      L0830
L1bc0:
        ldr     x30, [sp], #32
        ret

// mlkem_poly_decompress_d4 (0x4c bytes)
L1bc8:
        mov     x3, #0x0
        mov     w4, #0xd01
L1bd0:
        ldrb    w2, [x1, x3]
        add     x0, x0, #0x4
        and     w2, w2, #0xf
        mul     w2, w2, w4
        add     w2, w2, #0x8
        lsr     w2, w2, #4
        sturh   w2, [x0, #-4]
        ldrb    w2, [x1, x3]
        add     x3, x3, #0x1
        lsr     w2, w2, #4
        mul     w2, w2, w4
        add     w2, w2, #0x8
        lsr     w2, w2, #4
        sturh   w2, [x0, #-2]
        cmp     x3, #0x80
        b.ne    L1bd0
        ret

// mlkem_poly_decompress_d10 (0xcc bytes)
L1c14:
        .inst   0xd00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        mov     w4, #0x0
        mov     w6, #0xd01
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
        add     x5, sp, #0x10
L1c38:
        ldrh    w2, [x1]
        ldrb    w3, [x1, #1]
        and     w2, w2, #0x3ff
        strh    w2, [sp, #16]
        ldrb    w2, [x1, #2]
        lsl     w7, w2, #6
        orr     w3, w7, w3, lsr #2
        and     w3, w3, #0x3ff
        strh    w3, [sp, #18]
        ldrb    w3, [x1, #3]
        lsl     w7, w3, #4
        ubfx    x3, x3, #6, #16
        orr     w2, w7, w2, lsr #4
        and     w2, w2, #0x3ff
        strh    w2, [sp, #20]
        ldrb    w2, [x1, #4]
        orr     w2, w3, w2, lsl #2
        mov     x3, #0x0
        strh    w2, [sp, #22]
L1c84:
        ldrh    w2, [x5, x3, lsl #1]
        add     w7, w4, w3
        add     x3, x3, #0x1
        mul     w2, w2, w6
        add     w2, w2, #0x200
        lsr     w2, w2, #10
        strh    w2, [x0, x7, lsl #1]
        cmp     x3, #0x4
        b.ne    L1c84
        add     w4, w4, #0x4
        add     x1, x1, #0x5
        cmp     w4, #0x100
        b.ne    L1c38
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1cd8
        bl      L0830
L1cd8:
        ldr     x30, [sp], #32
        ret

// mlkem_poly_compress_d5 (0xec bytes)
L1ce0:
        .inst   0xd00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        mov     w8, #0xafc0
        mov     w4, #0x0
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
        add     x7, sp, #0x10
        movk    w8, #0x13, lsl #16
        mov     w9, #0x4000000
L1d0c:
        mov     x2, #0x0
        str     xzr, [sp, #16]
L1d14:
        add     w3, w4, w2
        ldrsh   w3, [x1, x3, lsl #1]
        madd    w3, w3, w8, w9
        lsr     w3, w3, #27
        strb    w3, [x2, x7]
        add     x2, x2, #0x1
        cmp     x2, #0x8
        b.ne    L1d14
        ldrb    w3, [sp, #17]
        add     w4, w4, #0x8
        ldrb    w2, [sp, #16]
        add     x0, x0, #0x5
        ldrb    w5, [sp, #18]
        orr     w2, w2, w3, lsl #5
        sturb   w2, [x0, #-5]
        ldrb    w2, [sp, #19]
        lsl     w6, w2, #7
        orr     w5, w6, w5, lsl #2
        orr     w3, w5, w3, lsr #3
        sturb   w3, [x0, #-4]
        ldrb    w3, [sp, #20]
        lsl     w5, w3, #4
        orr     w2, w5, w2, lsr #1
        sturb   w2, [x0, #-3]
        ldrb    w2, [sp, #22]
        ldrb    w5, [sp, #21]
        lsl     w6, w2, #6
        lsr     w2, w2, #2
        orr     w5, w6, w5, lsl #1
        orr     w3, w5, w3, lsr #4
        sturb   w3, [x0, #-2]
        ldrb    w3, [sp, #23]
        orr     w2, w2, w3, lsl #3
        sturb   w2, [x0, #-1]
        cmp     w4, #0x100
        b.ne    L1d0c
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1dc4
        bl      L0830
L1dc4:
        ldr     x30, [sp], #32
        ret

// mlkem_poly_compress_d11 (0x11c bytes)
L1dcc:
        .inst   0xd00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-48]!
        mov     x6, #0x7800
        mov     w4, #0x0
        movk    x6, #0x3afb, lsl #16
        ldr     x3, [x2]
        str     x3, [sp, #40]
        mov     x3, #0x0
        add     x8, sp, #0x18
        movk    x6, #0x1, lsl #32
        mov     x7, #0x100000000
L1dfc:
        mov     x2, #0x0
L1e00:
        add     w3, w4, w2
        ldrsh   x3, [x1, x3, lsl #1]
        madd    x3, x3, x6, x7
        ubfx    x3, x3, #33, #11
        strh    w3, [x8, x2, lsl #1]
        add     x2, x2, #0x1
        cmp     x2, #0x8
        b.ne    L1e00
        ldrh    w3, [sp, #26]
        add     w4, w4, #0x8
        ldrh    w2, [sp, #24]
        add     x0, x0, #0xb
        sturb   w2, [x0, #-11]
        lsl     w5, w3, #3
        orr     w2, w5, w2, lsr #8
        sturb   w2, [x0, #-10]
        ldrh    w2, [sp, #28]
        lsl     w5, w2, #6
        orr     w3, w5, w3, lsr #5
        ldrh    w5, [sp, #30]
        sturb   w3, [x0, #-9]
        lsr     w3, w2, #2
        sturb   w3, [x0, #-8]
        lsl     w3, w5, #1
        orr     w2, w3, w2, lsr #10
        ldrh    w3, [sp, #32]
        sturb   w2, [x0, #-7]
        lsl     w2, w3, #4
        orr     w5, w2, w5, lsr #7
        ldrh    w2, [sp, #34]
        sturb   w5, [x0, #-6]
        lsl     w5, w2, #7
        orr     w3, w5, w3, lsr #4
        sturb   w3, [x0, #-5]
        lsr     w3, w2, #1
        sturb   w3, [x0, #-4]
        ldrh    w3, [sp, #36]
        lsl     w5, w3, #2
        orr     w2, w5, w2, lsr #9
        sturb   w2, [x0, #-3]
        ldrh    w2, [sp, #38]
        lsl     w5, w2, #5
        lsr     w2, w2, #3
        orr     w3, w5, w3, lsr #6
        sturb   w3, [x0, #-2]
        sturb   w2, [x0, #-1]
        cmp     w4, #0x100
        b.ne    L1dfc
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #40]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1ee0
        bl      L0830
L1ee0:
        ldr     x30, [sp], #48
        ret

// mlkem_poly_decompress_d5 (0xf8 bytes)
L1ee8:
        .inst   0xd00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        mov     w4, #0x0
        mov     w6, #0xd01
        ldr     x3, [x2]
        str     x3, [sp, #24]
        mov     x3, #0x0
        add     x5, sp, #0x10
L1f0c:
        ldrb    w3, [x1]
        and     w2, w3, #0x1f
        strb    w2, [sp, #16]
        ldrb    w2, [x1, #1]
        lsl     w7, w2, #3
        orr     w3, w7, w3, lsr #5
        and     w3, w3, #0x1f
        strb    w3, [sp, #17]
        ubfx    x3, x2, #2, #5
        strb    w3, [sp, #18]
        ldrb    w3, [x1, #2]
        lsl     w7, w3, #1
        orr     w2, w7, w2, lsr #7
        and     w2, w2, #0x1f
        strb    w2, [sp, #19]
        ldrb    w2, [x1, #3]
        lsl     w7, w2, #4
        orr     w3, w7, w3, lsr #4
        and     w3, w3, #0x1f
        strb    w3, [sp, #20]
        ubfx    x3, x2, #1, #5
        strb    w3, [sp, #21]
        ldrb    w3, [x1, #4]
        lsl     w7, w3, #2
        lsr     w3, w3, #3
        orr     w2, w7, w2, lsr #6
        strb    w3, [sp, #23]
        and     w2, w2, #0x1f
        mov     x3, #0x0
        strb    w2, [sp, #22]
L1f84:
        ldrb    w2, [x3, x5]
        add     w7, w4, w3
        add     x3, x3, #0x1
        mul     w2, w2, w6
        add     w2, w2, #0x10
        lsr     w2, w2, #5
        strh    w2, [x0, x7, lsl #1]
        cmp     x3, #0x8
        b.ne    L1f84
        add     w4, w4, #0x8
        add     x1, x1, #0x5
        cmp     w4, #0x100
        b.ne    L1f0c
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L1fd8
        bl      L0830
L1fd8:
        ldr     x30, [sp], #32
        ret

// mlkem_poly_decompress_d11 (0x12c bytes)
L1fe0:
        .inst   0xd00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-48]!
        mov     w4, #0x0
        mov     w6, #0xd01
        ldr     x3, [x2]
        str     x3, [sp, #40]
        mov     x3, #0x0
        add     x5, sp, #0x18
L2004:
        ldrh    w2, [x1]
        ldrb    w3, [x1, #1]
        and     w2, w2, #0x7ff
        strh    w2, [sp, #24]
        ldrb    w2, [x1, #2]
        lsl     w7, w2, #5
        orr     w3, w7, w3, lsr #3
        ldrb    w7, [x1, #3]
        and     w3, w3, #0x7ff
        strh    w3, [sp, #26]
        ldrb    w3, [x1, #4]
        lsl     w8, w3, #10
        orr     w7, w8, w7, lsl #2
        orr     w2, w7, w2, lsr #6
        and     w2, w2, #0x7ff
        strh    w2, [sp, #28]
        ldrb    w2, [x1, #5]
        lsl     w7, w2, #7
        orr     w3, w7, w3, lsr #1
        and     w3, w3, #0x7ff
        strh    w3, [sp, #30]
        ldrb    w3, [x1, #6]
        lsl     w7, w3, #4
        orr     w2, w7, w2, lsr #4
        ldrb    w7, [x1, #7]
        and     w2, w2, #0x7ff
        strh    w2, [sp, #32]
        ldrb    w2, [x1, #8]
        lsl     w8, w2, #9
        orr     w7, w8, w7, lsl #1
        orr     w3, w7, w3, lsr #7
        and     w3, w3, #0x7ff
        strh    w3, [sp, #34]
        ldrb    w3, [x1, #9]
        lsl     w7, w3, #6
        ubfx    x3, x3, #5, #16
        orr     w2, w7, w2, lsr #2
        and     w2, w2, #0x7ff
        strh    w2, [sp, #36]
        ldrb    w2, [x1, #10]
        orr     w2, w3, w2, lsl #3
        mov     x3, #0x0
        strh    w2, [sp, #38]
L20b0:
        ldrh    w2, [x5, x3, lsl #1]
        add     w7, w4, w3
        add     x3, x3, #0x1
        mul     w2, w2, w6
        add     w2, w2, #0x400
        lsr     w2, w2, #11
        strh    w2, [x0, x7, lsl #1]
        cmp     x3, #0x8
        b.ne    L20b0
        add     w4, w4, #0x8
        add     x1, x1, #0xb
        cmp     w4, #0x100
        b.ne    L2004
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #40]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2104
        bl      L0830
L2104:
        ldr     x30, [sp], #48
        ret

// mlkem_poly_tobytes (0x38 bytes)
L210c:
        add     x4, x0, #0x180
L2110:
        ldrsh   w2, [x1]
        add     x0, x0, #0x3
        ldrh    w3, [x1, #2]
        add     x1, x1, #0x4
        sturb   w2, [x0, #-3]
        ubfx    x2, x2, #8, #8
        orr     w2, w2, w3, lsl #4
        lsr     w3, w3, #4
        sturb   w2, [x0, #-2]
        sturb   w3, [x0, #-1]
        cmp     x4, x0
        b.ne    L2110
        ret

// mlkem_poly_frombytes (0x38 bytes)
L2144:
        add     x5, x1, #0x180
L2148:
        ldrb    w2, [x1, #1]
        add     x0, x0, #0x4
        ldrb    w3, [x1, #2]
        ldrb    w6, [x1], #3
        ubfiz   w4, w2, #8, #4
        lsl     w3, w3, #4
        orr     w4, w4, w6
        orr     w2, w3, w2, lsr #4
        sturh   w4, [x0, #-4]
        sturh   w2, [x0, #-2]
        cmp     x5, x1
        b.ne    L2148
        ret

// mlkem_poly_frommsg (0x50 bytes)
L217c:
        mov     x4, #0x0
        mov     w6, #0x1
        mov     w7, #0x681
L2188:
        lsl     w5, w4, #3
        mov     w3, #0x0
L2190:
        lsl     w2, w6, w3
        ldrb    w8, [x1, x4]
        and     w2, w2, #0xff
        and     w2, w2, w8
        neg     w2, w2
        add     w8, w5, w3
        and     w2, w7, w2, asr #16
        add     w3, w3, #0x1
        strh    w2, [x0, x8, lsl #1]
        cmp     w3, #0x8
        b.ne    L2190
        add     x4, x4, #0x1
        cmp     x4, #0x20
        b.ne    L2188
        ret

// mlkem_poly_tomsg (0x58 bytes)
L21cc:
        mov     w5, #0xafb8
        mov     x3, #0x0
        movk    w5, #0x13, lsl #16
        mov     w6, #0x40000000
L21dc:
        lsl     w8, w3, #3
        mov     w4, #0x0
        strb    wzr, [x0, x3]
L21e8:
        add     w2, w8, w4
        ldrb    w7, [x0, x3]
        ldrsh   w2, [x1, x2, lsl #1]
        madd    w2, w2, w5, w6
        lsr     w2, w2, #31
        lsl     w2, w2, w4
        add     w4, w4, #0x1
        orr     w2, w2, w7
        strb    w2, [x0, x3]
        cmp     w4, #0x8
        b.ne    L21e8
        add     x3, x3, #0x1
        cmp     x3, #0x20
        b.ne    L21dc
        ret

// mlk_keccak_absorb_once (0xec bytes)
L2224:
        stp     x19, x20, [sp, #-80]!
        mov     x20, x0
        mov     x19, x3
        stp     x23, x24, [sp, #32]
        mov     w23, w1
        mov     w1, #0x0
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        mov     x21, x23
        mov     x2, #0xc8
        str     x30, [sp, #48]
        strb    w4, [sp, #79]
        bl      L0840
L2258:
        cmp     x23, x19
        b.ls    L22c0
        sub     w21, w21, #0x1
        mov     w24, w19
        add     x23, sp, #0x4f
        cbz     x19, L22e8
        mov     w3, w19
        mov     x1, x22
        mov     x0, x20
        mov     w2, #0x0
        bl      L29cc
        cmp     x19, w21, uxtw
        b.ne    L22e8
        ldrb    w0, [sp, #79]
        mov     w2, w19
        mov     w3, #0x1
        orr     w0, w0, #0xffffff80
        strb    w0, [sp, #79]
L22a0:
        mov     x1, x23
        mov     x0, x20
        bl      L29cc
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #80
        ret
L22c0:
        mov     x1, x22
        mov     w3, w21
        mov     w2, #0x0
        mov     x0, x20
        bl      L29cc
        sub     x19, x19, x23
        mov     x0, x20
        add     x22, x22, x23
        bl      L2af8
        b       L2258
L22e8:
        mov     w2, w24
        mov     x0, x20
        mov     w3, #0x1
        mov     x1, x23
        bl      L29cc
        mov     w0, #0xffffff80
        mov     w2, w21
        mov     w3, #0x1
        strb    w0, [sp, #79]
        b       L22a0

// mlk_keccak_squeeze_once (0x60 bytes)
L2310:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x0
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        mov     w22, w3
        stp     x23, x30, [sp, #32]
L232c:
        cbnz    x19, L2340
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L2340:
        mov     x0, x21
        bl      L2af8
        cmp     x22, x19
        mov     x1, x20
        csel    x23, x22, x19, ls
        mov     x0, x21
        mov     w3, w23
        mov     w2, #0x0
        add     x20, x20, x23
        sub     x19, x19, x23
        bl      L29a8
        b       L232c

// mlkem_shake128_absorb_once (0x14 bytes)
L2370:
        mov     x3, x2
        mov     w4, #0x1f
        mov     x2, x1
        mov     w1, #0xa8
        b       L2224

// mlkem_shake128_squeezeblocks (0x4c bytes)
L2384:
        stp     x19, x20, [sp, #-32]!
        mov     x20, x0
        mov     x19, x1
        stp     x21, x30, [sp, #16]
        mov     x21, x2
L2398:
        cbnz    x19, L23a8
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
L23a8:
        mov     x0, x21
        bl      L2af8
        mov     x1, x20
        mov     x0, x21
        mov     w3, #0xa8
        mov     w2, #0x0
        add     x20, x20, #0xa8
        sub     x19, x19, #0x1
        bl      L29a8
        b       L2398

// mlkem_shake128_init (0x4 bytes)
L23d0:
        ret

// mlkem_shake128_release (0x1c bytes)
L23d4:
        stp     x19, x30, [sp, #-16]!
        mov     x2, #0xe0
        mov     x19, x0
        mov     w1, #0x0
        bl      L0840
        ldp     x19, x30, [sp], #16
        ret

// mlkem_shake256 (0x8c bytes)
L23f0:
        stp     x19, x20, [sp, #-288]!
        mov     x20, x0
        mov     w4, #0x1f
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x30, [sp, #16]
        add     x19, sp, #0x3f
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x1
        ldr     x1, [x0]
        str     x1, [sp, #280]
        mov     x1, #0x0
        mov     x0, x19
        mov     w1, #0x88
        bl      L2224
        mov     w3, #0x88
        mov     x2, x19
        mov     x1, x21
        mov     x0, x20
        bl      L2310
        mov     x0, x19
        mov     x2, #0xe0
        mov     w1, #0x0
        bl      L0840
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #280]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2470
        bl      L0830
L2470:
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #288
        ret

// mlkem_sha3_256 (0x8c bytes)
L247c:
        stp     x19, x20, [sp, #-240]!
        mov     x20, x0
        mov     w4, #0x6
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x20
        ldr     x3, [x0]
        str     x3, [sp, #232]
        mov     x3, #0x0
        mov     x0, x19
        mov     x3, x2
        mov     x2, x1
        mov     w1, #0x88
        bl      L2224
        mov     w3, #0x88
        mov     x2, x19
        mov     x0, x20
        mov     x1, #0x20
        bl      L2310
        mov     x0, x19
        mov     x2, #0xc8
        mov     w1, #0x0
        bl      L0840
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L24fc
        bl      L0830
L24fc:
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #240
        ret

// mlkem_sha3_512 (0x8c bytes)
L2508:
        stp     x19, x20, [sp, #-240]!
        mov     x20, x0
        mov     w4, #0x6
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x20
        ldr     x3, [x0]
        str     x3, [sp, #232]
        mov     x3, #0x0
        mov     x0, x19
        mov     x3, x2
        mov     x2, x1
        mov     w1, #0x48
        bl      L2224
        mov     w3, #0x48
        mov     x2, x19
        mov     x0, x20
        mov     x1, #0x40
        bl      L2310
        mov     x0, x19
        mov     x2, #0xc8
        mov     w1, #0x0
        bl      L0840
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2588
        bl      L0830
L2588:
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #240
        ret

// mlk_zeroize (0x1c bytes)
L2594:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0840
        ldp     x19, x30, [sp], #16
        ret

// mlk_keccak_squeezeblocks_x4 (0x88 bytes)
L25b0:
        stp     x19, x20, [sp, #-80]!
        mov     x20, x4
        mov     x19, #0x0
        stp     x27, x30, [sp, #64]
        mov     w27, w6
        stp     x21, x22, [sp, #16]
        mov     x21, x5
        mov     x22, x27
        stp     x23, x24, [sp, #32]
        mov     x23, x0
        mov     x24, x1
        stp     x25, x26, [sp, #48]
        mov     x25, x2
        mov     x26, x3
L25e8:
        cbnz    x20, L2604
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #80
        ret
L2604:
        mov     x0, x21
        bl      L30ec
        add     x4, x26, x19
        add     x3, x25, x19
        add     x2, x24, x19
        add     x1, x23, x19
        mov     w6, w22
        mov     x0, x21
        mov     w5, #0x0
        add     x19, x19, x27
        sub     x20, x20, #0x1
        bl      L29f8
        b       L25e8

// mlk_keccak_absorb_once_x4.constprop.0 (0x150 bytes)
L2638:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        mov     x19, x6
        .inst   0xb00000e0  // adrp x0, 0x1f000
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
L268c:
        add     x4, x27, x22
        add     x3, x26, x22
        add     x2, x25, x22
        add     x1, x24, x22
        add     x22, x22, x23
        cmp     x19, x23
        b.cs    L271c
        mov     w23, w19
        sub     w21, w21, #0x1
        add     x22, sp, #0x57
        cbz     x19, L273c
        mov     w6, w19
        mov     x0, x20
        mov     w5, #0x0
        bl      L2a78
        cmp     x19, w21, uxtw
        b.ne    L273c
        ldrb    w0, [sp, #87]
        mov     w5, w19
        mov     w6, #0x1
        orr     w0, w0, #0xffffff80
        strb    w0, [sp, #87]
L26e4:
        mov     x2, x22
        mov     x1, x22
        mov     x0, x20
        mov     x4, x22
        mov     x3, x22
        bl      L2a78
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2770
        bl      L0830
L271c:
        mov     w6, w21
        mov     w5, #0x0
        mov     x0, x20
        bl      L2a78
        mov     x0, x20
        sub     x19, x19, x23
        bl      L30ec
        b       L268c
L273c:
        mov     w5, w23
        mov     x0, x20
        mov     w6, #0x1
        mov     x4, x22
        mov     x3, x22
        mov     x2, x22
        mov     x1, x22
        bl      L2a78
        mov     w0, #0xffffff80
        mov     w5, w21
        mov     w6, #0x1
        strb    w0, [sp, #87]
        b       L26e4
L2770:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #96
        ret

// mlkem_shake128x4_absorb_once (0x64 bytes)
L2788:
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
        bl      L0840
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
        b       L2638

// mlkem_shake128x4_squeezeblocks (0x8 bytes)
L27ec:
        mov     w6, #0xa8
        b       L25b0

// mlkem_shake128x4_init (0x4 bytes)
L27f4:
        ret

// mlkem_shake128x4_release (0x8 bytes)
L27f8:
        mov     x1, #0x320
        b       L2594

// mlkem_shake256x4 (0x1a8 bytes)
L2800:
        sub     sp, sp, #0x5d0
        stp     x23, x24, [sp, #32]
        mov     x24, x0
        mov     x23, x1
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        mov     x19, x4
        stp     x21, x22, [sp, #16]
        mov     x22, #0x88
        add     x21, sp, #0x8f
        stp     x25, x26, [sp, #48]
        and     x21, x21, #0xffffffffffffffe0
        mov     x25, x5
        stp     x27, x28, [sp, #64]
        mov     x26, x6
        mov     x27, x7
        str     x30, [sp, #80]
        stp     x2, x3, [sp, #96]
        mov     x2, #0x320
        ldr     x28, [sp, #1488]
        ldr     x1, [x0]
        str     x1, [sp, #1480]
        mov     x1, #0x0
        udiv    x20, x4, x22
        mov     x0, x21
        bl      L0840
        ldr     x6, [sp, #1496]
        mov     x5, x28
        mov     x4, x27
        mov     x3, x26
        mov     x2, x25
        mov     w1, w22
        mov     x0, x21
        bl      L2638
        ldp     x2, x3, [sp, #96]
        mov     x4, x20
        mul     x20, x20, x22
        mov     w6, w22
        mov     x5, x21
        mov     x1, x23
        mov     x0, x24
        add     x25, sp, #0x540
        add     x26, sp, #0x4b8
        add     x27, sp, #0x430
        bl      L25b0
        add     x28, sp, #0x3a8
        subs    x19, x19, x20
        b.eq    L292c
        mov     w6, w22
        mov     x5, x21
        mov     x3, x25
        mov     x4, #0x1
        mov     x2, x26
        mov     x1, x27
        mov     x0, x28
        bl      L25b0
        mov     x2, x19
        mov     x1, x28
        add     x0, x24, x20
        bl      L0810
        mov     x2, x19
        mov     x1, x27
        add     x0, x23, x20
        bl      L0810
        ldr     x0, [sp, #96]
        mov     x2, x19
        mov     x1, x26
        add     x0, x0, x20
        bl      L0810
        ldr     x0, [sp, #104]
        mov     x2, x19
        mov     x1, x25
        add     x0, x0, x20
        bl      L0810
L292c:
        mov     x0, x21
        mov     x1, #0x320
        bl      L2594
        mov     x0, x28
        mov     x1, #0x88
        bl      L2594
        mov     x0, x27
        mov     x1, #0x88
        bl      L2594
        mov     x0, x26
        mov     x1, #0x88
        bl      L2594
        mov     x0, x25
        mov     x1, #0x88
        bl      L2594
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1480]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L2988
        bl      L0830
L2988:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x5d0
        ret

// mlkem_keccakf1600_extract_bytes (0x24 bytes)
L29a8:
        add     x2, x0, w2, uxtw
        mov     x4, #0x0
L29b0:
        cmp     w3, w4
        b.hi    L29bc
        ret
L29bc:
        ldrb    w0, [x2, x4]
        strb    w0, [x1, x4]
        add     x4, x4, #0x1
        b       L29b0

// mlkem_keccakf1600_xor_bytes (0x2c bytes)
L29cc:
        add     x2, x0, w2, uxtw
        mov     x0, #0x0
L29d4:
        cmp     w3, w0
        b.hi    L29e0
        ret
L29e0:
        ldrb    w5, [x1, x0]
        add     x0, x0, #0x1
        ldrb    w4, [x2]
        eor     w4, w4, w5
        strb    w4, [x2], #1
        b       L29d4

// mlkem_keccakf1600x4_extract_bytes (0x80 bytes)
L29f8:
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
        bl      L29a8
        mov     w3, w20
        mov     w2, w19
        mov     x1, x24
        add     x0, x21, #0xc8
        bl      L29a8
        mov     w3, w20
        mov     w2, w19
        mov     x1, x23
        add     x0, x21, #0x190
        bl      L29a8
        ldp     x23, x24, [sp, #32]
        mov     w3, w20
        ldr     x30, [sp, #48]
        mov     w2, w19
        mov     x1, x22
        add     x0, x21, #0x258
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        b       L29a8

// mlkem_keccakf1600x4_xor_bytes (0x80 bytes)
L2a78:
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
        bl      L29cc
        mov     w3, w20
        mov     w2, w19
        mov     x1, x24
        add     x0, x21, #0xc8
        bl      L29cc
        mov     w3, w20
        mov     w2, w19
        mov     x1, x23
        add     x0, x21, #0x190
        bl      L29cc
        ldp     x23, x24, [sp, #32]
        mov     w3, w20
        ldr     x30, [sp, #48]
        mov     w2, w19
        mov     x1, x22
        add     x0, x21, #0x258
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        b       L29cc

// mlkem_keccakf1600_permute (0x5f4 bytes)
L2af8:
        stp     x19, x20, [sp, #-224]!
        .inst   0xf0000002  // adrp x2, 0x5000
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
        add     x24, x2, #0xa80
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
L2b70:
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
        b.ne    L2b70
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

// mlkem_keccakf1600x4_permute (0x28 bytes)
L30ec:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L2af8
        add     x0, x19, #0xc8
        bl      L2af8
        add     x0, x19, #0x190
        bl      L2af8
        add     x0, x19, #0x258
        ldp     x19, x30, [sp], #16
        b       L2af8

// mlk_zeroize (0x1c bytes)
L3114:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0840
        ldp     x19, x30, [sp], #16
        ret

// mlkem512_gen_matrix (0xac bytes)
L3130:
        stp     x19, x30, [sp, #-304]!
        .inst   0x900000e3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        add     x19, sp, #0x2f
        and     x19, x19, #0xffffffffffffffe0
        ldr     x4, [x3]
        str     x4, [sp, #296]
        mov     x4, #0x0
        mov     x3, x19
L3154:
        ldp     q0, q1, [x1]
        add     w4, w4, #0x1
        stp     q0, q1, [x3]
        add     x3, x3, #0x40
        cmp     w4, #0x4
        b.ne    L3154
        cmp     w2, #0x0
        add     x3, x0, #0x600
        cset    w2, ne
        cset    w1, eq
        mov     x4, x19
        strb    w2, [x19, #97]
        strb    w2, [x19, #160]
        add     x2, x0, #0x400
        strb    w1, [x19, #96]
        strb    w1, [x19, #161]
        mov     w1, #0x101
        strh    wzr, [x19, #32]
        strh    w1, [x19, #224]
        add     x1, x0, #0x200
        bl      L45b8
        mov     x0, x19
        mov     x1, #0x100
        bl      L3114
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L31d4
        bl      L0830
L31d4:
        ldp     x19, x30, [sp], #304
        ret

// mlkem512_indcpa_keypair_derand (0x1e0 bytes)
L31dc:
        mov     x12, #0x16f0
        sub     sp, sp, x12
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0x7f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        add     x22, x19, #0x1, lsl #12
        add     x20, x19, #0x800
        stp     x23, x24, [sp, #48]
        mov     x24, x0
        mov     w23, #0x2
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x25, x26, [sp, #64]
        stp     x27, x30, [sp, #80]
        mov     x27, x1
        ldp     q0, q1, [x2]
        ldr     x1, [x0]
        str     x1, [sp, #5864]
        mov     x1, #0x0
        mov     x0, #0x1640
        add     x25, x19, x0
        mov     x1, #0x1600
        add     x21, x19, x1
        mov     x0, x21
        mov     x1, x25
        stp     q0, q1, [x25]
        mov     x2, #0x21
        strb    w23, [x22, #1632]
        bl      L2508
        mov     x1, x21
        mov     x0, x19
        mov     w2, #0x0
        bl      L3130
        mov     w7, w23
        add     x4, x21, #0x20
        add     x3, x22, #0x200
        mov     x2, x22
        add     x1, x19, #0xa00
        mov     w0, #0x3
        strb    w0, [sp]
        mov     w6, #0x1
        mov     w5, #0x0
        mov     x0, x20
        bl      L421c
        add     x23, x19, #0xc00
        mov     x0, x20
        bl      L40cc
        mov     x0, x22
        bl      L40cc
        mov     x2, #0x1400
        add     x26, x19, x2
        mov     x1, x20
        mov     x0, x26
        bl      L419c
        mov     x3, x26
        mov     x2, x20
        mov     x1, x19
        mov     x0, x23
        bl      L40fc
        mov     x2, x20
        mov     x3, x26
        add     x1, x19, #0x400
        add     x0, x19, #0xe00
        bl      L40fc
        mov     x0, x23
        bl      L4204
        mov     x1, x22
        mov     x0, x23
        bl      L41dc
        mov     x0, x23
        bl      L41c4
        mov     x0, x20
        bl      L41c4
        mov     x1, x20
        mov     x0, x27
        bl      L407c
        mov     x1, x23
        mov     x0, x24
        bl      L407c
        ldp     q0, q1, [x21]
        mov     x0, x26
        mov     x1, #0x200
        stp     q0, q1, [x24, #768]
        bl      L3114
        mov     x0, x20
        mov     x1, #0x400
        bl      L3114
        mov     x0, x23
        mov     x1, #0x400
        bl      L3114
        mov     x0, x22
        mov     x1, #0x400
        bl      L3114
        mov     x0, x19
        mov     x1, #0x800
        bl      L3114
        mov     x0, x25
        mov     x1, #0x21
        bl      L3114
        mov     x0, x21
        mov     x1, #0x40
        bl      L3114
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #5864]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3398
        bl      L0830
L3398:
        ldp     x19, x20, [sp, #16]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x16f0
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x30, [sp, #80]
        add     sp, sp, x12
        ret

// mlkem512_indcpa_enc (0x260 bytes)
L33bc:
        mov     x12, #0x20c0
        sub     sp, sp, x12
        mov     x4, #0x1800
        str     x0, [sp, #120]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0x9f
        stp     x21, x22, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x20, x2
        stp     x23, x24, [sp, #48]
        mov     x21, x3
        mov     x22, x1
        stp     x25, x26, [sp, #64]
        mov     x3, #0x1a00
        mov     x1, #0x1c00
        stp     x27, x28, [sp, #80]
        add     x25, x19, #0x1, lsl #12
        add     x27, x19, x1
        str     x30, [sp, #96]
        add     x23, x19, x4
        add     x28, x19, x3
        add     x24, x19, #0x2, lsl #12
        ldr     x1, [x0]
        str     x1, [sp, #8376]
        mov     x1, #0x0
        mov     x0, x25
        mov     x1, x2
        bl      L40a4
        ldp     q0, q1, [x20, #768]
        mov     x1, x22
        mov     x0, x27
        add     x26, x19, #0xc00
        add     x22, x19, #0x800
        stp     q0, q1, [x24]
        bl      L217c
        mov     x1, x24
        mov     x0, x19
        mov     w2, #0x1
        bl      L3130
        mov     w0, #0x3
        strb    w0, [sp]
        mov     x5, #0x1400
        add     x20, x19, x5
        mov     x4, x21
        mov     w7, #0x2
        mov     w5, #0x0
        mov     w6, #0x1
        add     x3, x19, #0xe00
        mov     x2, x26
        add     x1, x20, #0x200
        mov     x0, x20
        bl      L43f4
        mov     x1, x21
        mov     w2, #0x4
        mov     x0, x28
        bl      L4358
        mov     x0, x20
        bl      L40cc
        mov     x1, x20
        mov     x0, x23
        bl      L419c
        mov     x3, x23
        mov     x2, x20
        mov     x1, x19
        mov     x0, x22
        bl      L40fc
        mov     x3, x23
        mov     x2, x20
        add     x1, x19, #0x400
        add     x0, x19, #0xa00
        bl      L40fc
        mov     x2, x20
        mov     x6, #0x1e00
        mov     x3, x23
        mov     x1, x25
        add     x21, x19, x6
        mov     x0, x21
        bl      L40fc
        mov     x0, x22
        bl      L40e4
        mov     x0, x21
        bl      L3f18
        mov     x1, x26
        mov     x0, x22
        bl      L41dc
        mov     x1, x28
        mov     x0, x21
        bl      L3db8
        mov     x1, x27
        mov     x0, x21
        bl      L3db8
        mov     x0, x22
        bl      L41c4
        mov     x0, x21
        bl      L3d68
        ldr     x0, [sp, #120]
        mov     x1, x22
        bl      L402c
        ldr     x0, [sp, #120]
        mov     x1, x21
        add     x0, x0, #0x280
        bl      L1a34
        mov     x0, x23
        mov     x1, #0x200
        bl      L3114
        mov     x0, x28
        mov     x1, #0x200
        bl      L3114
        mov     x0, x27
        mov     x1, #0x200
        bl      L3114
        mov     x0, x21
        mov     x1, #0x200
        bl      L3114
        mov     x0, x22
        mov     x1, #0x400
        bl      L3114
        mov     x0, x26
        mov     x1, #0x400
        bl      L3114
        mov     x0, x25
        mov     x1, #0x400
        bl      L3114
        mov     x0, x20
        mov     x1, #0x400
        bl      L3114
        mov     x0, x19
        mov     x1, #0x800
        bl      L3114
        mov     x0, x24
        mov     x1, #0x20
        bl      L3114
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #8376]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L35f4
        bl      L0830
L35f4:
        ldp     x19, x20, [sp, #16]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x20c0
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret

// mlkem512_indcpa_dec (0x134 bytes)
L361c:
        sub     sp, sp, #0xe60
        stp     x23, x24, [sp, #32]
        mov     x24, x0
        mov     x23, x1
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x5f
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        and     x19, x19, #0xffffffffffffffe0
        str     x30, [sp, #48]
        add     x20, x19, #0x400
        add     x21, x19, #0xc00
        ldr     x2, [x0]
        str     x2, [sp, #3672]
        mov     x2, #0x0
        mov     x0, x20
        bl      L4054
        add     x1, x23, #0x280
        mov     x0, x21
        bl      L1bc8
        add     x23, x19, #0x800
        mov     x1, x22
        mov     x0, x19
        bl      L40a4
        add     x22, x19, #0xa00
        mov     x0, x20
        bl      L40cc
        mov     x1, x20
        mov     x0, x23
        bl      L419c
        mov     x2, x20
        mov     x3, x23
        mov     x1, x19
        mov     x0, x22
        bl      L40fc
        mov     x0, x22
        bl      L3f18
        mov     x1, x22
        mov     x0, x21
        bl      L3ddc
        mov     x0, x21
        bl      L3d68
        mov     x1, x21
        mov     x0, x24
        bl      L21cc
        mov     x0, x23
        mov     x1, #0x200
        bl      L3114
        mov     x0, x22
        mov     x1, #0x200
        bl      L3114
        mov     x0, x21
        mov     x1, #0x200
        bl      L3114
        mov     x0, x19
        mov     x1, #0x400
        bl      L3114
        mov     x0, x20
        mov     x1, #0x400
        bl      L3114
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #3672]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3734
        bl      L0830
L3734:
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        add     sp, sp, #0xe60
        ret

// mlk_ct_memcmp (0x4c bytes)
L3750:
        mov     w6, #0x0
        mov     w5, #0x0
        mov     w3, #0x0
L375c:
        mov     w7, w6
        cmp     x2, w6, uxtw
        b.hi    L377c
        neg     w1, w3
        eor     w1, w5, w1, asr #16
        and     w1, w1, #0xff
        eor     w0, w5, w1
        ret
L377c:
        ldrb    w4, [x0, x7]
        add     w6, w6, #0x1
        ldrb    w7, [x1, x7]
        eor     w4, w4, w7
        and     w4, w4, #0xff
        orr     w3, w4, w3
        eor     w5, w4, w5
        b       L375c

// mlk_zeroize (0x1c bytes)
L379c:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0840
        ldp     x19, x30, [sp], #16
        ret

// mlkem512_check_pk (0xb8 bytes)
L37b8:
        sub     sp, sp, #0x740
        stp     x19, x20, [sp]
        mov     x20, x0
        add     x19, sp, #0x3f
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x30, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #1848]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, x20
        bl      L40a4
        add     x21, x19, #0x400
        mov     x0, x19
        bl      L41c4
        mov     x1, x19
        mov     x0, x21
        bl      L407c
        mov     x2, #0x300
        mov     x1, x21
        mov     x0, x20
        bl      L3750
        tst     w0, #0xff
        mov     x1, x2
        mov     x0, x21
        mov     w20, #0xfffffffc
        csel    w20, wzr, w20, eq
        bl      L379c
        mov     x0, x19
        mov     x1, #0x400
        bl      L379c
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1848]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L385c
        bl      L0830
L385c:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp]
        add     sp, sp, #0x740
        ret

// mlkem512_check_sk (0x90 bytes)
L3870:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        mov     x2, #0x320
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x3f
        and     x19, x19, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #88]
        mov     x1, #0x0
        add     x1, x20, #0x300
        mov     x0, x19
        bl      L247c
        mov     x2, #0x20
        mov     x1, x19
        add     x0, x20, #0x620
        bl      L3750
        tst     w0, #0xff
        mov     x1, x2
        mov     x0, x19
        mov     w20, #0xfffffffb
        csel    w20, wzr, w20, eq
        bl      L379c
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L38f0
        bl      L0830
L38f0:
        ldr     x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #96
        ret

// mlkem512_keypair_derand (0x80 bytes)
L3900:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x0
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        str     x30, [sp, #32]
        bl      L31dc
        mov     w21, w0
        cbz     w0, L3950
        mov     x0, x20
        mov     x1, #0x320
        bl      L379c
        mov     x0, x19
        mov     x1, #0x660
        bl      L379c
L393c:
        ldr     x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret
L3950:
        mov     x1, x20
        add     x0, x19, #0x300
        mov     x2, #0x320
        bl      L0810
        add     x0, x19, #0x620
        mov     x1, x20
        mov     x2, #0x320
        bl      L247c
        ldp     q0, q1, [x22, #32]
        add     x19, x19, #0x640
        stp     q0, q1, [x19]
        b       L393c

// mlkem512_keypair (0x94 bytes)
L3980:
        stp     x19, x20, [sp, #-128]!
        mov     x20, x0
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x30, [sp, #16]
        add     x19, sp, #0x3f
        mov     x21, x1
        and     x19, x19, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #120]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x40
        bl      L0820
        cbnz    w0, L39fc
        mov     x0, x20
        mov     x2, x19
        mov     x1, x21
        bl      L3900
        mov     w20, w0
L39d0:
        mov     x0, x19
        mov     x1, #0x40
        bl      L379c
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #120]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3a04
        bl      L0830
L39fc:
        mov     w20, #0xfffffffd
        b       L39d0
L3a04:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #128
        ret

// mlkem512_enc_derand (0xec bytes)
L3a14:
        stp     x19, x20, [sp, #-224]!
        stp     x25, x30, [sp, #48]
        mov     x25, x0
        add     x19, sp, #0x5f
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        mov     x22, x2
        ldr     x1, [x0]
        str     x1, [sp, #216]
        mov     x1, #0x0
        mov     x24, x3
        mov     x0, x2
        add     x21, x19, #0x40
        bl      L37b8
        mov     w20, w0
        cbnz    w0, L3ab0
        ldp     q0, q1, [x24]
        mov     x1, x22
        add     x0, x19, #0x60
        mov     x2, #0x320
        stp     q0, q1, [x21]
        bl      L247c
        mov     x1, x21
        mov     x0, x19
        mov     x2, #0x40
        bl      L2508
        add     x3, x19, #0x20
        mov     x2, x22
        mov     x1, x21
        mov     x0, x25
        bl      L33bc
        mov     w20, w0
        cbnz    w0, L3ab0
        ldp     q0, q1, [x19]
        stp     q0, q1, [x23]
L3ab0:
        mov     x0, x19
        mov     x1, #0x40
        bl      L379c
        mov     x0, x21
        mov     x1, #0x40
        bl      L379c
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #216]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3ae8
        bl      L0830
L3ae8:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #224
        ret

// mlkem512_enc (0xa4 bytes)
L3b00:
        stp     x19, x20, [sp, #-112]!
        mov     x20, x0
        .inst   0x900000e0  // adrp x0, 0x1f000
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
        bl      L0820
        cbnz    w0, L3b88
        mov     x0, x20
        mov     x3, x19
        mov     x2, x22
        mov     x1, x21
        bl      L3a14
        mov     w20, w0
L3b5c:
        mov     x0, x19
        mov     x1, #0x20
        bl      L379c
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #104]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3b90
        bl      L0830
L3b88:
        mov     w20, #0xfffffffd
        b       L3b5c
L3b90:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret

// mlkem512_dec (0x188 bytes)
L3ba4:
        sub     sp, sp, #0x410
        stp     x23, x24, [sp, #32]
        mov     x23, x0
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x6f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x2
        stp     x25, x26, [sp, #48]
        mov     x25, x1
        add     x22, x19, #0x360
        str     x30, [sp, #64]
        add     x24, x19, #0x320
        ldr     x1, [x0]
        str     x1, [sp, #1032]
        mov     x1, #0x0
        mov     x0, x2
        bl      L3870
        mov     w20, w0
        cbnz    w0, L3cc8
        mov     x2, x21
        mov     x1, x25
        mov     x0, x22
        bl      L361c
        mov     w20, w0
        cbnz    w0, L3cc8
        ldr     q0, [x21, #1568]
        mov     x1, x22
        ldr     q1, [x21, #1584]
        mov     x0, x24
        mov     x2, #0x40
        stp     q0, q1, [x19, #896]
        bl      L2508
        add     x3, x19, #0x340
        add     x2, x21, #0x300
        mov     x1, x22
        mov     x0, x19
        bl      L33bc
        mov     w20, w0
        cbnz    w0, L3cc8
        mov     x2, #0x300
        mov     x1, x19
        mov     x0, x25
        bl      L3750
        ldr     q0, [x21, #1600]
        and     w26, w0, #0xff
        ldr     q1, [x21, #1616]
        mov     x1, x25
        add     x0, x19, #0x20
        neg     w26, w26
        stp     q0, q1, [x19]
        bl      L0810
        mov     x0, x22
        mov     x3, #0x320
        mov     x2, x19
        mov     x1, #0x20
        bl      L23f0
        mov     x3, x22
        mov     x0, #0x0
L3c98:
        ldrb    w2, [x24, x0]
        mov     w1, w26
        ldrb    w4, [x3]
        add     x0, x0, #0x1
        eor     w4, w2, w4
        and     w1, w4, w1, asr #16
        eor     w2, w2, w1
        strb    w2, [x3], #1
        cmp     x0, #0x20
        b.ne    L3c98
        ldp     q0, q1, [x22]
        stp     q0, q1, [x23]
L3cc8:
        mov     x0, x19
        mov     x1, #0x320
        bl      L379c
        mov     x0, x24
        mov     x1, #0x40
        bl      L379c
        mov     x0, x22
        mov     x1, #0x40
        bl      L379c
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1032]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L3d0c
        bl      L0830
L3d0c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        add     sp, sp, #0x410
        ret

// mlkem_poly_tomont (0x3c bytes)
L3d2c:
        mov     x2, #0x0
        mov     w6, #0x549
        mov     w5, #0xfffff301
        mov     w4, #0xfffff2ff
L3d3c:
        ldrsh   w3, [x0, x2, lsl #1]
        mul     w3, w3, w6
        mul     w1, w3, w5
        sxth    w1, w1
        madd    w1, w1, w4, w3
        asr     w1, w1, #16
        strh    w1, [x0, x2, lsl #1]
        add     x2, x2, #0x1
        cmp     x2, #0x100
        b.ne    L3d3c
        ret

// mlkem_poly_reduce (0x50 bytes)
L3d68:
        mov     x3, #0x0
        mov     w7, #0x4ebf
        mov     w6, #0x2000000
        mov     w5, #0xfffff2ff
L3d78:
        ldrsh   w2, [x0, x3, lsl #1]
        madd    w1, w2, w7, w6
        asr     w1, w1, #26
        madd    w1, w1, w5, w2
        sxth    w1, w1
        mov     w2, w1
        neg     w2, w2, lsr #16
        add     w4, w1, #0xd01
        eor     w4, w1, w4
        and     w2, w4, w2, asr #16
        eor     w1, w1, w2
        strh    w1, [x0, x3, lsl #1]
        add     x3, x3, #0x1
        cmp     x3, #0x100
        b.ne    L3d78
        ret

// mlkem_poly_add (0x24 bytes)
L3db8:
        mov     x2, #0x0
L3dbc:
        ldrh    w3, [x0, x2]
        ldrh    w4, [x1, x2]
        add     w3, w3, w4
        strh    w3, [x0, x2]
        add     x2, x2, #0x2
        cmp     x2, #0x200
        b.ne    L3dbc
        ret

// mlkem_poly_sub (0x24 bytes)
L3ddc:
        mov     x2, #0x0
L3de0:
        ldrh    w3, [x0, x2]
        ldrh    w4, [x1, x2]
        sub     w3, w3, w4
        strh    w3, [x0, x2]
        add     x2, x2, #0x2
        cmp     x2, #0x200
        b.ne    L3de0
        ret

// mlkem_poly_mulcache_compute (0x74 bytes)
L3e00:
        add     x4, x1, #0x2
        .inst   0xd0000005  // adrp x5, 0x5000
        add     x1, x1, #0x202
        add     x5, x5, #0xb40
        mov     w8, #0xfffff301
        mov     w7, #0xfffff2ff
L3e18:
        ldrsh   w3, [x5, #128]
        add     x4, x4, #0x8
        ldursh  w6, [x4, #-8]
        add     x5, x5, #0x2
        add     x0, x0, #0x4
        mul     w6, w6, w3
        neg     w3, w3
        sxth    w3, w3
        mul     w2, w6, w8
        sxth    w2, w2
        madd    w2, w2, w7, w6
        asr     w2, w2, #16
        sturh   w2, [x0, #-4]
        ldursh  w2, [x4, #-4]
        mul     w3, w2, w3
        mul     w2, w3, w8
        sxth    w2, w2
        madd    w2, w2, w7, w3
        asr     w2, w2, #16
        sturh   w2, [x0, #-2]
        cmp     x1, x4
        b.ne    L3e18
        ret

// mlkem_poly_ntt (0xa4 bytes)
L3e74:
        mov     w2, #0x1
        .inst   0xd0000008  // adrp x8, 0x5000
        mov     w11, w2
        add     x8, x8, #0xb40
        mov     w12, #0x100
        mov     w13, #0xfffff301
        mov     w14, #0xfffff2ff
L3e90:
        sub     w6, w2, #0x1
        lsr     w3, w12, w2
        lsl     w10, w3, #1
        mov     w5, #0x0
        lsl     w6, w11, w6
L3ea4:
        mov     w1, w6
        add     w6, w6, #0x1
        ldrsh   w15, [x8, w1, uxtw #1]
        cmp     w5, w3
        b.cs    L3ef8
        mov     w4, w5
        add     x9, x0, w3, uxtw #1
L3ec0:
        ldrsh   w7, [x9]
        mul     w7, w7, w15
        mul     w1, w7, w13
        sxth    w1, w1
        madd    w1, w1, w14, w7
        ldrh    w7, [x0, x4, lsl #1]
        sub     w7, w7, w1, asr #16
        strh    w7, [x9], #2
        ldrh    w7, [x0, x4, lsl #1]
        add     w1, w7, w1, asr #16
        strh    w1, [x0, x4, lsl #1]
        add     x4, x4, #0x1
        cmp     w3, w4
        b.hi    L3ec0
L3ef8:
        add     w5, w5, w10
        add     w3, w3, w10
        cmp     w5, #0xff
        b.ls    L3ea4
        add     w2, w2, #0x1
        cmp     w2, #0x8
        b.ne    L3e90
        ret

// mlkem_poly_invntt_tomont (0xf8 bytes)
L3f18:
        mov     x2, #0x0
        mov     w6, #0x5a1
        mov     w5, #0xfffff301
        mov     w4, #0xfffff2ff
L3f28:
        ldrsh   w3, [x0, x2, lsl #1]
        mul     w3, w3, w6
        mul     w1, w3, w5
        sxth    w1, w1
        madd    w1, w1, w4, w3
        asr     w1, w1, #16
        strh    w1, [x0, x2, lsl #1]
        add     x2, x2, #0x1
        cmp     x2, #0x100
        b.ne    L3f28
        .inst   0xd000000a  // adrp x10, 0x5000
        mov     w4, w2
        add     x10, x10, #0xb40
        mov     w5, #0x7
        mov     w13, #0x1
        mov     w14, #0x4ebf
        mov     w15, #0x2000000
        mov     w11, #0xfffff2ff
        mov     w16, #0xfffff301
L3f74:
        lsr     w3, w4, w5
        mov     w6, #0x0
        lsl     w7, w13, w5
        lsl     w12, w3, #1
        sub     w7, w7, #0x1
L3f88:
        mov     w1, w7
        sub     w7, w7, #0x1
        ldrsh   w17, [x10, w1, uxtw #1]
        cmp     w6, w3
        b.cs    L3ff4
        mov     w8, w6
        add     x9, x0, w3, uxtw #1
L3fa4:
        ldrsh   w18, [x0, x8, lsl #1]
        ldrh    w1, [x9]
        add     w1, w18, w1
        sxth    w1, w1
        madd    w2, w1, w14, w15
        asr     w2, w2, #26
        madd    w1, w2, w11, w1
        strh    w1, [x0, x8, lsl #1]
        add     x8, x8, #0x1
        ldrh    w1, [x9]
        sub     w1, w1, w18
        sxth    w1, w1
        mul     w1, w1, w17
        mul     w2, w1, w16
        sxth    w2, w2
        madd    w1, w2, w11, w1
        asr     w1, w1, #16
        strh    w1, [x9], #2
        cmp     w3, w8
        b.hi    L3fa4
L3ff4:
        add     w6, w6, w12
        add     w3, w3, w12
        cmp     w6, #0xff
        b.ls    L3f88
        subs    w5, w5, #0x1
        b.ne    L3f74
        ret

// mlk_zeroize (0x1c bytes)
L4010:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0840
        ldp     x19, x30, [sp], #16
        ret

// mlkem512_polyvec_compress_du (0x28 bytes)
L402c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L1b00
        ldr     x30, [sp, #16]
        add     x1, x20, #0x200
        add     x0, x19, #0x140
        ldp     x19, x20, [sp], #32
        b       L1b00

// mlkem512_polyvec_decompress_du (0x28 bytes)
L4054:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L1c14
        ldr     x30, [sp, #16]
        add     x1, x20, #0x140
        add     x0, x19, #0x200
        ldp     x19, x20, [sp], #32
        b       L1c14

// mlkem512_polyvec_tobytes (0x28 bytes)
L407c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L210c
        ldr     x30, [sp, #16]
        add     x1, x20, #0x200
        add     x0, x19, #0x180
        ldp     x19, x20, [sp], #32
        b       L210c

// mlkem512_polyvec_frombytes (0x28 bytes)
L40a4:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L2144
        ldr     x30, [sp, #16]
        add     x1, x20, #0x180
        add     x0, x19, #0x200
        ldp     x19, x20, [sp], #32
        b       L2144

// mlkem512_polyvec_ntt (0x18 bytes)
L40cc:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L3e74
        add     x0, x19, #0x200
        ldp     x19, x30, [sp], #16
        b       L3e74

// mlkem512_polyvec_invntt_tomont (0x18 bytes)
L40e4:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L3f18
        add     x0, x19, #0x200
        ldp     x19, x30, [sp], #16
        b       L3f18

// mlkem512_polyvec_basemul_acc_montgomery_cached (0xa0 bytes)
L40fc:
        add     x11, x1, #0x200
        mov     w9, #0xfffff301
        mov     w8, #0xfffff2ff
L4108:
        ldrsh   w10, [x1]
        add     x1, x1, #0x4
        ldrsh   w4, [x2]
        add     x3, x3, #0x2
        ldursh  w12, [x1, #-2]
        add     x2, x2, #0x4
        ldursh  w6, [x3, #-2]
        add     x0, x0, #0x4
        ldrsh   w13, [x1, #508]
        ldrsh   w14, [x2, #508]
        mul     w5, w4, w10
        ldrsh   w7, [x1, #510]
        mul     w4, w4, w12
        madd    w6, w6, w12, w5
        ldrsh   w5, [x3, #254]
        mul     w15, w13, w14
        madd    w5, w5, w7, w15
        mul     w7, w7, w14
        add     w6, w6, w5
        ldrsh   w5, [x2, #510]
        madd    w5, w5, w13, w7
        ldursh  w7, [x2, #-2]
        madd    w4, w7, w10, w4
        add     w5, w5, w4
        mul     w4, w6, w9
        sxth    w4, w4
        madd    w4, w4, w8, w6
        asr     w4, w4, #16
        sturh   w4, [x0, #-4]
        mul     w4, w5, w9
        sxth    w4, w4
        madd    w4, w4, w8, w5
        asr     w4, w4, #16
        sturh   w4, [x0, #-2]
        cmp     x11, x1
        b.ne    L4108
        ret

// mlkem512_polyvec_mulcache_compute (0x28 bytes)
L419c:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L3e00
        ldr     x30, [sp, #16]
        add     x1, x20, #0x200
        add     x0, x19, #0x100
        ldp     x19, x20, [sp], #32
        b       L3e00

// mlkem512_polyvec_reduce (0x18 bytes)
L41c4:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L3d68
        add     x0, x19, #0x200
        ldp     x19, x30, [sp], #16
        b       L3d68

// mlkem512_polyvec_add (0x28 bytes)
L41dc:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L3db8
        ldr     x30, [sp, #16]
        add     x1, x20, #0x200
        add     x0, x19, #0x200
        ldp     x19, x20, [sp], #32
        b       L3db8

// mlkem512_polyvec_tomont (0x18 bytes)
L4204:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L3d2c
        add     x0, x19, #0x200
        ldp     x19, x30, [sp], #16
        b       L3d2c

// mlkem512_poly_getnoise_eta1_4x (0x13c bytes)
L421c:
        sub     sp, sp, #0x480
        stp     x23, x24, [sp, #48]
        mov     x24, x0
        mov     x23, x1
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0x7f
        stp     x21, x22, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        add     x20, x19, #0x300
        stp     x25, x26, [sp, #64]
        mov     x22, x2
        ldrb    w2, [sp, #1152]
        stp     x27, x30, [sp, #80]
        add     x26, x19, #0x180
        add     x25, x19, #0x240
        ldp     q0, q1, [x4]
        ldr     x1, [x0]
        str     x1, [sp, #1144]
        mov     x1, #0x0
        add     x1, x19, #0x380
        add     x0, x19, #0x340
        add     x4, x19, #0x3c0
        strb    w5, [x20, #32]
        stp     q0, q1, [x20]
        mov     x5, x20
        mov     x21, x3
        stp     q0, q1, [x0]
        mov     x3, x25
        add     x27, x19, #0xc0
        stp     q0, q1, [x1]
        stp     q0, q1, [x4]
        strb    w6, [x20, #96]
        mov     x6, x0
        strb    w7, [x20, #160]
        mov     x7, x1
        strb    w2, [x20, #224]
        mov     x2, #0x21
        stp     x4, x2, [sp]
        mov     x2, x26
        mov     x4, #0xc0
        mov     x1, x27
        mov     x0, x19
        bl      L2800
        mov     x1, x19
        mov     x0, x24
        bl      L48d4
        mov     x1, x27
        mov     x0, x23
        bl      L48d4
        mov     x1, x26
        mov     x0, x22
        bl      L48d4
        cbz     x21, L4304
        mov     x1, x25
        mov     x0, x21
        bl      L48d4
L4304:
        mov     x0, x19
        mov     x1, #0x300
        bl      L4010
        mov     x0, x20
        mov     x1, #0x100
        bl      L4010
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1144]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L433c
        bl      L0830
L433c:
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x30, [sp, #80]
        add     sp, sp, #0x480
        ret

// mlkem512_poly_getnoise_eta2 (0x9c bytes)
L4358:
        stp     x19, x20, [sp, #-240]!
        add     x19, sp, #0x3f
        stp     x21, x30, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        add     x20, x19, #0x80
        mov     x21, x0
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldp     q0, q1, [x1]
        ldr     x3, [x0]
        str     x3, [sp, #232]
        mov     x3, #0x0
        strb    w2, [x20, #32]
        mov     x2, x20
        mov     x3, #0x21
        mov     x0, x19
        mov     x1, #0x80
        stp     q0, q1, [x20]
        bl      L23f0
        mov     x1, x19
        mov     x0, x21
        bl      L4878
        mov     x0, x19
        mov     x1, #0x80
        bl      L4010
        mov     x0, x20
        mov     x1, #0x21
        bl      L4010
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L43e8
        bl      L0830
L43e8:
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #240
        ret

// mlkem512_poly_getnoise_eta1122_4x (0x138 bytes)
L43f4:
        sub     sp, sp, #0x480
        stp     x23, x24, [sp, #48]
        mov     x24, x0
        mov     x23, x1
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0x7f
        stp     x21, x22, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        add     x20, x19, #0x300
        stp     x25, x26, [sp, #64]
        mov     x22, x2
        ldrb    w2, [sp, #1152]
        stp     x27, x30, [sp, #80]
        add     x25, x19, #0x240
        add     x26, x19, #0x180
        ldp     q0, q1, [x4]
        ldr     x1, [x0]
        str     x1, [sp, #1144]
        mov     x1, #0x0
        add     x1, x19, #0x380
        add     x0, x19, #0x340
        add     x4, x19, #0x3c0
        strb    w5, [x20, #32]
        stp     q0, q1, [x20]
        mov     x5, x20
        mov     x21, x3
        stp     q0, q1, [x0]
        mov     x3, x25
        add     x27, x19, #0xc0
        stp     q0, q1, [x1]
        stp     q0, q1, [x4]
        strb    w6, [x20, #96]
        mov     x6, x0
        strb    w7, [x20, #160]
        mov     x7, x1
        strb    w2, [x20, #224]
        mov     x2, #0x21
        stp     x4, x2, [sp]
        mov     x2, x26
        mov     x4, #0xc0
        mov     x1, x27
        mov     x0, x19
        bl      L2800
        mov     x1, x19
        mov     x0, x24
        bl      L48d4
        mov     x1, x27
        mov     x0, x23
        bl      L48d4
        mov     x1, x26
        mov     x0, x22
        bl      L4878
        mov     x1, x25
        mov     x0, x21
        bl      L4878
        mov     x0, x19
        mov     x1, #0x300
        bl      L4010
        mov     x0, x20
        mov     x1, #0x100
        bl      L4010
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1144]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4510
        bl      L0830
L4510:
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x30, [sp, #80]
        add     sp, sp, #0x480
        ret

// mlk_rej_uniform_c.constprop.0 (0x8c bytes)
L452c:
        mov     x6, x0
        mov     w7, #0x3
        mov     w0, w1
        sub     w7, w7, w2
        mov     w8, #0xd00
L4540:
        cmp     w0, #0xff
        b.ls    L457c
L4548:
        ret
L454c:
        ldrb    w1, [x2, #1]
        add     x2, x2, #0x3
        ldurb   w4, [x2, #-3]
        ldurb   w5, [x2, #-1]
        orr     w4, w4, w1, lsl #8
        lsr     w1, w1, #4
        and     w4, w4, #0xfff
        orr     w5, w1, w5, lsl #4
        cmp     w4, #0xd00
        b.le    L458c
        cmp     w5, #0xd00
        b.le    L45b0
L457c:
        add     w1, w7, w2
        cmp     w3, w1
        b.cs    L454c
        b       L4548
L458c:
        add     w1, w0, #0x1
        strh    w4, [x6, w0, uxtw #1]
        cmp     w1, #0xff
        ccmp    w5, w8, #0x0, ls
        b.gt    L45a8
L45a0:
        strh    w5, [x6, w1, uxtw #1]
        add     w1, w1, #0x1
L45a8:
        mov     w0, w1
        b       L4540
L45b0:
        mov     w1, w0
        b       L45a0

// mlkem_poly_rej_uniform_x4 (0x1d4 bytes)
L45b8:
        sub     sp, sp, #0xbc0
        stp     x0, x1, [sp, #104]
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x9f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     x20, x4
        stp     x23, x24, [sp, #32]
        add     x23, x19, #0x800
        mov     x24, x2
        stp     x25, x26, [sp, #48]
        mov     x25, x3
        add     x26, x19, #0x600
        stp     x27, x28, [sp, #64]
        add     x27, x19, #0x400
        add     x28, x19, #0x200
        str     x30, [sp, #80]
        ldr     x1, [x0]
        str     x1, [sp, #3000]
        mov     x1, #0x0
        mov     x0, x23
        bl      L27f4
        add     x4, x20, #0xc0
        add     x3, x20, #0x80
        add     x2, x20, #0x40
        mov     x1, x20
        mov     x0, x23
        mov     x5, #0x22
        bl      L2788
        mov     x5, x23
        mov     x4, #0x3
        mov     x3, x26
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        bl      L27ec
        ldr     x0, [sp, #104]
        mov     w3, #0x1f8
        mov     x2, x19
        mov     w1, #0x0
        bl      L452c
        mov     w21, w0
        ldr     x0, [sp, #112]
        mov     x2, x28
        mov     w1, #0x0
        bl      L452c
        mov     w22, w0
        mov     x2, x27
        mov     w1, #0x0
        mov     x0, x24
        bl      L452c
        mov     x2, x26
        mov     w20, w0
        mov     w1, #0x0
L4698:
        mov     x0, x25
        bl      L452c
        mov     w6, w0
        cmp     w21, #0xff
        b.ls    L46fc
        cmp     w22, #0xff
        b.ls    L46fc
        cmp     w20, #0xff
        b.ls    L46fc
        cmp     w0, #0xff
        b.ls    L46fc
        mov     x0, x23
        bl      L27f8
        mov     x0, x19
        mov     x2, #0x800
        mov     w1, #0x0
        bl      L0840
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #3000]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L476c
        bl      L0830
L46fc:
        mov     x5, x23
        mov     x4, #0x1
        mov     x3, x26
        mov     x2, x27
        mov     x1, x28
        mov     x0, x19
        str     w6, [sp, #124]
        bl      L27ec
        ldr     x0, [sp, #104]
        mov     w1, w21
        mov     w3, #0xa8
        mov     x2, x19
        bl      L452c
        mov     w21, w0
        ldr     x0, [sp, #112]
        mov     w1, w22
        mov     x2, x28
        bl      L452c
        mov     w22, w0
        mov     w1, w20
        mov     x2, x27
        mov     x0, x24
        bl      L452c
        ldr     w6, [sp, #124]
        mov     w20, w0
        mov     x2, x26
        mov     w1, w6
        b       L4698
L476c:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0xbc0
        ret

// mlkem_poly_rej_uniform (0xec bytes)
L478c:
        sub     sp, sp, #0x330
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        mov     x20, x1
        str     x30, [sp, #32]
        add     x19, sp, #0x4f
        and     x19, x19, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #808]
        mov     x1, #0x0
        add     x21, x19, #0x200
        mov     x0, x21
        bl      L23d0
        mov     x1, x20
        mov     x0, x21
        mov     x2, #0x22
        bl      L2370
        mov     x2, x21
        mov     x1, #0x3
        mov     x0, x19
        bl      L2384
        mov     x2, x19
        mov     w3, #0x1f8
        mov     w1, #0x0
L47f8:
        mov     x0, x22
        bl      L452c
        mov     w20, w0
        cmp     w0, #0xff
        b.ls    L4844
        mov     x0, x21
        bl      L23d4
        mov     x0, x19
        mov     x2, #0x1f8
        mov     w1, #0x0
        bl      L0840
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #808]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4864
        bl      L0830
L4844:
        mov     x2, x21
        mov     x1, #0x1
        mov     x0, x19
        bl      L2384
        mov     x2, x19
        mov     w1, w20
        mov     w3, #0xa8
        b       L47f8
L4864:
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        add     sp, sp, #0x330
        ret

// mlkem_poly_cbd2 (0x5c bytes)
L4878:
        mov     x3, #0x0
L487c:
        ldr     w2, [x1, x3, lsl #2]
        lsl     w7, w3, #3
        and     w4, w2, #0x55555555
        lsr     w2, w2, #1
        and     w2, w2, #0x55555555
        add     w2, w2, w4
        mov     w4, #0x0
L4898:
        add     w6, w4, #0x2
        lsr     w5, w2, w4
        and     w5, w5, #0x3
        add     w4, w4, #0x4
        lsr     w6, w2, w6
        and     w6, w6, #0x3
        sub     w5, w5, w6
        strh    w5, [x0, w7, uxtw #1]
        add     w7, w7, #0x1
        cmp     w4, #0x20
        b.ne    L4898
        add     x3, x3, #0x1
        cmp     x3, #0x20
        b.ne    L487c
        ret

// mlkem_poly_cbd3 (0x80 bytes)
L48d4:
        mov     w7, #0x9249
        mov     w6, #0x0
        movk    w7, #0x24, lsl #16
L48e0:
        ldrb    w3, [x1, #2]
        mov     w8, w6
        ldrb    w2, [x1, #1]
        ldrb    w4, [x1]
        lsl     w3, w3, #16
        orr     w2, w3, w2, lsl #8
        orr     w2, w2, w4
        and     w4, w2, w7
        and     w3, w7, w2, lsr #1
        and     w2, w7, w2, lsr #2
        add     w2, w3, w2
        mov     w3, #0x0
        add     w2, w2, w4
L4914:
        add     w5, w3, #0x3
        lsr     w4, w2, w3
        and     w4, w4, #0x7
        add     w3, w3, #0x6
        lsr     w5, w2, w5
        and     w5, w5, #0x7
        sub     w4, w4, w5
        strh    w4, [x0, w8, uxtw #1]
        add     w8, w8, #0x1
        cmp     w3, #0x18
        b.ne    L4914
        add     w6, w6, #0x4
        add     x1, x1, #0x3
        cmp     w6, #0x100
        b.ne    L48e0
        ret

// mlk_zeroize (0x1c bytes)
L4954:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0840
        ldp     x19, x30, [sp], #16
        ret

// mlkem768_gen_matrix (0x154 bytes)
L4970:
        stp     x19, x20, [sp, #-336]!
        mov     x20, x0
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        add     x19, sp, #0x4f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     w21, w2
        stp     x23, x30, [sp, #32]
        ldr     x2, [x0]
        str     x2, [sp, #328]
        mov     x2, #0x0
        mov     x0, x19
        mov     w2, #0x4
L49a8:
        ldp     q0, q1, [x1]
        subs    w2, w2, #0x1
        stp     q0, q1, [x0]
        add     x0, x0, #0x40
        b.ne    L49a8
        cbnz    w21, L4a98
        mov     w1, #0x1
        mov     w2, w1
        mov     w0, #0x0
        mov     w3, #0x0
        mov     w22, #0x2
        mov     w23, #0x0
L49d8:
        mov     x4, x19
        strh    wzr, [x19, #32]
        strb    w1, [x19, #96]
        add     x1, x20, #0x200
        strb    w0, [x19, #97]
        mov     x0, x20
        strb    w22, [x19, #160]
        strb    w23, [x19, #161]
        strb    w3, [x19, #224]
        add     x3, x20, #0x600
        strb    w2, [x19, #225]
        add     x2, x20, #0x400
        bl      L45b8
        strb    w23, [x19, #160]
        cmp     w21, #0x0
        mov     w2, #0x2
        mov     w0, #0x101
        mov     x4, x19
        add     x3, x20, #0xe00
        strh    w0, [x19, #32]
        mov     w0, #0x1
        csel    w1, w2, w0, eq
        csel    w0, w0, w2, eq
        add     x2, x20, #0xc00
        strb    w1, [x19, #96]
        strb    w0, [x19, #97]
        strb    w22, [x19, #161]
        strb    w0, [x19, #224]
        add     x0, x20, #0x800
        strb    w1, [x19, #225]
        add     x1, x20, #0xa00
        bl      L45b8
        mov     w0, #0x202
        mov     x1, x19
        strh    w0, [x19, #32]
        add     x0, x20, #0x1, lsl #12
        bl      L478c
        mov     x0, x19
        mov     x1, #0x100
        bl      L4954
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #328]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4ab4
        bl      L0830
L4a98:
        mov     w0, #0x1
        mov     w1, #0x0
        mov     w3, w0
        mov     w2, #0x0
        mov     w22, #0x0
        mov     w23, #0x2
        b       L49d8
L4ab4:
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #336
        ret

// mlkem768_indcpa_keypair_derand (0x238 bytes)
L4ac4:
        mov     x12, #0x2810
        sub     sp, sp, x12
        mov     x3, #0x2740
        mov     x4, #0x2700
        mov     x5, #0x1200
        mov     x6, #0x1e00
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0x9f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        mov     x21, x0
        add     x22, x19, x4
        stp     x23, x24, [sp, #48]
        add     x24, x19, #0x2, lsl #12
        add     x20, x19, x5
        stp     x25, x26, [sp, #64]
        add     x25, x19, x3
        add     x23, x19, x6
        stp     x27, x28, [sp, #80]
        mov     w27, #0x3
        mov     w28, #0xffffffff
        str     x30, [sp, #96]
        add     x26, x22, #0x20
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        str     x1, [sp, #112]
        ldp     q0, q1, [x2]
        ldr     x1, [x0]
        str     x1, [sp, #10248]
        mov     x1, #0x0
        mov     x1, x25
        mov     x0, x22
        mov     x2, #0x21
        stp     q0, q1, [x25]
        strb    w27, [x24, #1888]
        bl      L2508
        mov     x1, x22
        mov     x0, x19
        mov     w2, #0x0
        bl      L4970
        strb    w28, [sp]
        mov     x4, x26
        add     x2, x20, #0x400
        add     x1, x20, #0x200
        mov     x0, x20
        mov     w7, #0x2
        mov     w6, #0x1
        mov     w5, #0x0
        mov     x3, #0x0
        bl      L5928
        mov     w5, w27
        mov     x4, x26
        mov     x1, x24
        add     x2, x23, #0x400
        strb    w28, [sp]
        mov     w7, #0x5
        mov     w6, #0x4
        mov     x3, #0x0
        mov     x0, x23
        bl      L5928
        mov     x0, x20
        bl      L579c
        mov     x0, x23
        bl      L579c
        mov     x7, #0x2400
        add     x27, x19, x7
        mov     x1, x20
        mov     x0, x27
        bl      L5880
        mov     w28, #0x0
        mov     x8, #0x1800
        add     x26, x19, x8
        mov     x1, x19
        mov     x24, x26
L4bec:
        mov     x0, x26
        mov     x3, x27
        mov     x2, x20
        str     x1, [sp, #120]
        bl      L57dc
        add     w28, w28, #0x1
        ldr     x1, [sp, #120]
        add     x26, x26, #0x200
        add     x1, x1, #0x600
        cmp     w28, #0x3
        b.ne    L4bec
        mov     x0, x24
        bl      L5908
        mov     x1, x23
        mov     x0, x24
        bl      L58d4
        mov     x0, x24
        bl      L58b4
        mov     x0, x20
        bl      L58b4
        ldr     x0, [sp, #112]
        mov     x1, x20
        bl      L5734
        mov     x0, x21
        mov     x1, x24
        bl      L5734
        add     x21, x21, #0x480
        ldp     q0, q1, [x22]
        mov     x0, x27
        mov     x1, #0x300
        stp     q0, q1, [x21]
        bl      L4954
        mov     x0, x20
        mov     x1, #0x600
        bl      L4954
        mov     x0, x24
        mov     x1, #0x600
        bl      L4954
        mov     x0, x23
        mov     x1, #0x600
        bl      L4954
        mov     x0, x19
        mov     x1, #0x1200
        bl      L4954
        mov     x0, x25
        mov     x1, #0x21
        bl      L4954
        mov     x0, x22
        mov     x1, #0x40
        bl      L4954
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #10248]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4cd4
        bl      L0830
L4cd4:
        ldp     x19, x20, [sp, #16]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x2810
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret

// mlkem768_indcpa_enc (0x2b0 bytes)
L4cfc:
        mov     x12, #0x33d0
        sub     sp, sp, x12
        mov     x4, #0x2a00
        stp     x25, x26, [sp, #64]
        mov     x25, x0
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0xaf
        stp     x21, x22, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        mov     x20, x2
        stp     x23, x24, [sp, #48]
        mov     x21, x3
        mov     x2, #0x2f00
        stp     x27, x28, [sp, #80]
        mov     x3, #0x2d00
        mov     x22, x1
        str     x30, [sp, #96]
        mov     x1, #0x1e00
        add     x26, x19, x1
        add     x28, x19, x3
        ldr     x1, [x0]
        str     x1, [sp, #13256]
        mov     x1, #0x0
        add     x24, x19, x4
        add     x27, x19, x2
        mov     x1, x20
        mov     x0, x26
        bl      L5768
        ldr     q0, [x20, #1152]
        mov     x5, #0x3300
        ldr     q1, [x20, #1168]
        add     x0, x19, x5
        mov     x6, #0x1800
        mov     x1, x22
        add     x22, x19, x6
        stp     q0, q1, [x0]
        mov     x0, x27
        bl      L217c
        mov     x8, #0x2400
        mov     x7, #0x3300
        add     x0, x19, x7
        add     x20, x19, x8
        mov     x1, x0
        mov     w2, #0x1
        str     x0, [sp, #120]
        mov     x0, x19
        bl      L4970
        mov     w0, #0xffffffff
        strb    w0, [sp]
        mov     x4, x21
        add     x2, x20, #0x400
        add     x1, x20, #0x200
        mov     x0, x20
        mov     w7, #0x2
        mov     w6, #0x1
        mov     w5, #0x0
        mov     x3, #0x0
        bl      L5928
        mov     x4, x21
        mov     x3, x28
        add     x2, x22, #0x400
        add     x1, x22, #0x200
        mov     w0, #0x6
        strb    w0, [sp]
        mov     w7, #0x5
        mov     w6, #0x4
        mov     w5, #0x3
        mov     x0, x22
        bl      L5928
        mov     x0, x20
        bl      L579c
        mov     x1, x20
        mov     x0, x24
        bl      L5880
        mov     x9, #0x1200
        add     x21, x19, x9
        mov     x1, x19
        mov     x23, x21
        mov     w4, #0x0
L4e40:
        mov     x0, x21
        mov     x3, x24
        mov     x2, x20
        str     x1, [sp, #128]
        str     w4, [sp, #140]
        bl      L57dc
        ldr     x1, [sp, #128]
        add     x21, x21, #0x200
        ldr     w4, [sp, #140]
        add     x1, x1, #0x600
        add     w4, w4, #0x1
        cmp     w4, #0x3
        b.ne    L4e40
        mov     x2, x20
        mov     x3, x24
        mov     x1, x26
        mov     x0, #0x3100
        add     x21, x19, x0
        mov     x0, x21
        bl      L57dc
        mov     x0, x23
        bl      L57bc
        mov     x0, x21
        bl      L3f18
        mov     x1, x22
        mov     x0, x23
        bl      L58d4
        mov     x1, x28
        mov     x0, x21
        bl      L3db8
        mov     x1, x27
        mov     x0, x21
        bl      L3db8
        mov     x0, x23
        bl      L58b4
        mov     x0, x21
        bl      L3d68
        mov     x1, x23
        mov     x0, x25
        bl      L56cc
        mov     x1, x21
        add     x0, x25, #0x3c0
        bl      L1a34
        mov     x0, x24
        mov     x1, #0x300
        bl      L4954
        mov     x0, x28
        mov     x1, #0x200
        bl      L4954
        mov     x0, x27
        mov     x1, #0x200
        bl      L4954
        mov     x0, x21
        mov     x1, #0x200
        bl      L4954
        mov     x0, x23
        mov     x1, #0x600
        bl      L4954
        mov     x0, x22
        mov     x1, #0x600
        bl      L4954
        mov     x0, x26
        mov     x1, #0x600
        bl      L4954
        mov     x0, x20
        mov     x1, #0x600
        bl      L4954
        mov     x0, x19
        mov     x1, #0x1200
        bl      L4954
        ldr     x0, [sp, #120]
        mov     x1, #0x20
        bl      L4954
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #13256]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L4f84
        bl      L0830
L4f84:
        ldp     x19, x20, [sp, #16]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x33d0
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret

// mlkem768_indcpa_dec (0x140 bytes)
L4fac:
        mov     x12, #0x1360
        sub     sp, sp, x12
        stp     x23, x24, [sp, #32]
        mov     x24, x0
        mov     x23, x1
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x5f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     x22, x2
        str     x30, [sp, #48]
        mov     x2, #0x1100
        add     x21, x19, x2
        add     x20, x19, #0x600
        ldr     x2, [x0]
        str     x2, [sp, #4952]
        mov     x2, #0x0
        mov     x0, x20
        bl      L5700
        add     x1, x23, #0x3c0
        mov     x0, x21
        bl      L1bc8
        add     x23, x19, #0xc00
        mov     x1, x22
        mov     x0, x19
        bl      L5768
        add     x22, x19, #0xf00
        mov     x0, x20
        bl      L579c
        mov     x1, x20
        mov     x0, x23
        bl      L5880
        mov     x2, x20
        mov     x3, x23
        mov     x1, x19
        mov     x0, x22
        bl      L57dc
        mov     x0, x22
        bl      L3f18
        mov     x1, x22
        mov     x0, x21
        bl      L3ddc
        mov     x0, x21
        bl      L3d68
        mov     x1, x21
        mov     x0, x24
        bl      L21cc
        mov     x0, x23
        mov     x1, #0x300
        bl      L4954
        mov     x0, x22
        mov     x1, #0x200
        bl      L4954
        mov     x0, x21
        mov     x1, #0x200
        bl      L4954
        mov     x0, x19
        mov     x1, #0x600
        bl      L4954
        mov     x0, x20
        mov     x1, #0x600
        bl      L4954
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4952]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L50cc
        bl      L0830
L50cc:
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x1360
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        add     sp, sp, x12
        ret

// mlk_ct_memcmp (0x4c bytes)
L50ec:
        mov     w6, #0x0
        mov     w5, #0x0
        mov     w3, #0x0
L50f8:
        mov     w7, w6
        cmp     x2, w6, uxtw
        b.hi    L5118
        neg     w1, w3
        eor     w1, w5, w1, asr #16
        and     w1, w1, #0xff
        eor     w0, w5, w1
        ret
L5118:
        ldrb    w4, [x0, x7]
        add     w6, w6, #0x1
        ldrb    w7, [x1, x7]
        eor     w4, w4, w7
        and     w4, w4, #0xff
        orr     w3, w4, w3
        eor     w5, w4, w5
        b       L50f8

// mlk_zeroize (0x1c bytes)
L5138:
        stp     x19, x30, [sp, #-16]!
        mov     x2, x1
        mov     x19, x0
        mov     w1, #0x0
        bl      L0840
        ldp     x19, x30, [sp], #16
        ret

// mlkem768_check_pk (0xb8 bytes)
L5154:
        sub     sp, sp, #0xac0
        stp     x19, x20, [sp]
        mov     x20, x0
        add     x19, sp, #0x3f
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x30, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #2744]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, x20
        bl      L5768
        add     x21, x19, #0x600
        mov     x0, x19
        bl      L58b4
        mov     x1, x19
        mov     x0, x21
        bl      L5734
        mov     x2, #0x480
        mov     x1, x21
        mov     x0, x20
        bl      L50ec
        tst     w0, #0xff
        mov     x1, x2
        mov     x0, x21
        mov     w20, #0xfffffffc
        csel    w20, wzr, w20, eq
        bl      L5138
        mov     x0, x19
        mov     x1, #0x600
        bl      L5138
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #2744]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L51f8
        bl      L0830
L51f8:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp]
        add     sp, sp, #0xac0
        ret

// mlkem768_check_sk (0x90 bytes)
L520c:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        mov     x2, #0x4a0
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x3f
        and     x19, x19, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #88]
        mov     x1, #0x0
        add     x1, x20, #0x480
        mov     x0, x19
        bl      L247c
        mov     x2, #0x20
        mov     x1, x19
        add     x0, x20, #0x920
        bl      L50ec
        tst     w0, #0xff
        mov     x1, x2
        mov     x0, x19
        mov     w20, #0xfffffffb
        csel    w20, wzr, w20, eq
        bl      L5138
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L528c
        bl      L0830
L528c:
        ldr     x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #96
        ret

// mlkem768_keypair_derand (0x80 bytes)
L529c:
        stp     x19, x20, [sp, #-48]!
        mov     x20, x0
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        str     x30, [sp, #32]
        bl      L4ac4
        mov     w21, w0
        cbz     w0, L52ec
        mov     x0, x20
        mov     x1, #0x4a0
        bl      L5138
        mov     x0, x19
        mov     x1, #0x960
        bl      L5138
L52d8:
        ldr     x30, [sp, #32]
        mov     w0, w21
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #48
        ret
L52ec:
        mov     x1, x20
        add     x0, x19, #0x480
        mov     x2, #0x4a0
        bl      L0810
        add     x0, x19, #0x920
        mov     x1, x20
        mov     x2, #0x4a0
        bl      L247c
        ldp     q0, q1, [x22, #32]
        add     x19, x19, #0x940
        stp     q0, q1, [x19]
        b       L52d8

// mlkem768_keypair (0x94 bytes)
L531c:
        stp     x19, x20, [sp, #-128]!
        mov     x20, x0
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x30, [sp, #16]
        add     x19, sp, #0x3f
        mov     x21, x1
        and     x19, x19, #0xffffffffffffffe0
        ldr     x1, [x0]
        str     x1, [sp, #120]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x40
        bl      L0820
        cbnz    w0, L5398
        mov     x0, x20
        mov     x2, x19
        mov     x1, x21
        bl      L529c
        mov     w20, w0
L536c:
        mov     x0, x19
        mov     x1, #0x40
        bl      L5138
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #120]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L53a0
        bl      L0830
L5398:
        mov     w20, #0xfffffffd
        b       L536c
L53a0:
        ldp     x21, x30, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp], #128
        ret

// mlkem768_enc_derand (0xec bytes)
L53b0:
        stp     x19, x20, [sp, #-224]!
        stp     x25, x30, [sp, #48]
        mov     x25, x0
        add     x19, sp, #0x5f
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        mov     x22, x2
        ldr     x1, [x0]
        str     x1, [sp, #216]
        mov     x1, #0x0
        mov     x24, x3
        mov     x0, x2
        add     x21, x19, #0x40
        bl      L5154
        mov     w20, w0
        cbnz    w0, L544c
        ldp     q0, q1, [x24]
        mov     x1, x22
        add     x0, x19, #0x60
        mov     x2, #0x4a0
        stp     q0, q1, [x21]
        bl      L247c
        mov     x1, x21
        mov     x0, x19
        mov     x2, #0x40
        bl      L2508
        add     x3, x19, #0x20
        mov     x2, x22
        mov     x1, x21
        mov     x0, x25
        bl      L4cfc
        mov     w20, w0
        cbnz    w0, L544c
        ldp     q0, q1, [x19]
        stp     q0, q1, [x23]
L544c:
        mov     x0, x19
        mov     x1, #0x40
        bl      L5138
        mov     x0, x21
        mov     x1, #0x40
        bl      L5138
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #216]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L5484
        bl      L0830
L5484:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #224
        ret

// mlkem768_enc (0xa4 bytes)
L549c:
        stp     x19, x20, [sp, #-112]!
        mov     x20, x0
        .inst   0xd00000c0  // adrp x0, 0x1f000
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
        bl      L0820
        cbnz    w0, L5524
        mov     x0, x20
        mov     x3, x19
        mov     x2, x22
        mov     x1, x21
        bl      L53b0
        mov     w20, w0
L54f8:
        mov     x0, x19
        mov     x1, #0x20
        bl      L5138
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #104]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L552c
        bl      L0830
L5524:
        mov     w20, #0xfffffffd
        b       L54f8
L552c:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret

// mlkem768_dec (0x18c bytes)
L5540:
        sub     sp, sp, #0x550
        stp     x23, x24, [sp, #32]
        mov     x23, x0
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x6f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x2
        stp     x25, x26, [sp, #48]
        mov     x25, x1
        add     x22, x19, #0x4a0
        str     x30, [sp, #64]
        add     x24, x19, #0x460
        ldr     x1, [x0]
        str     x1, [sp, #1352]
        mov     x1, #0x0
        mov     x0, x2
        bl      L520c
        mov     w20, w0
        cbnz    w0, L5668
        mov     x2, x21
        mov     x1, x25
        mov     x0, x22
        bl      L4fac
        mov     w20, w0
        cbnz    w0, L5668
        ldr     q0, [x21, #2336]
        add     x0, x19, #0x4c0
        ldr     q1, [x21, #2352]
        mov     x1, x22
        mov     x2, #0x40
        stp     q0, q1, [x0]
        mov     x0, x24
        bl      L2508
        add     x3, x19, #0x480
        add     x2, x21, #0x480
        mov     x1, x22
        mov     x0, x19
        bl      L4cfc
        mov     w20, w0
        cbnz    w0, L5668
        mov     x2, #0x440
        mov     x1, x19
        mov     x0, x25
        bl      L50ec
        ldr     q0, [x21, #2368]
        and     w26, w0, #0xff
        ldr     q1, [x21, #2384]
        mov     x1, x25
        add     x0, x19, #0x20
        neg     w26, w26
        stp     q0, q1, [x19]
        bl      L0810
        mov     x0, x22
        mov     x3, #0x460
        mov     x2, x19
        mov     x1, #0x20
        bl      L23f0
        mov     x3, x22
        mov     x0, #0x0
L5638:
        ldrb    w2, [x24, x0]
        mov     w1, w26
        ldrb    w4, [x3]
        add     x0, x0, #0x1
        eor     w4, w2, w4
        and     w1, w4, w1, asr #16
        eor     w2, w2, w1
        strb    w2, [x3], #1
        cmp     x0, #0x20
        b.ne    L5638
        ldp     q0, q1, [x22]
        stp     q0, q1, [x23]
L5668:
        mov     x0, x19
        mov     x1, #0x460
        bl      L5138
        mov     x0, x24
        mov     x1, #0x40
        bl      L5138
        mov     x0, x22
        mov     x1, #0x40
        bl      L5138
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1352]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L56ac
        bl      L0830
L56ac:
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        add     sp, sp, #0x550
        ret

// mlkem768_polyvec_compress_du (0x34 bytes)
L56cc:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L1b00
        add     x1, x20, #0x200
        add     x0, x19, #0x140
        bl      L1b00
        ldr     x30, [sp, #16]
        add     x1, x20, #0x400
        add     x0, x19, #0x280
        ldp     x19, x20, [sp], #32
        b       L1b00

// mlkem768_polyvec_decompress_du (0x34 bytes)
L5700:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L1c14
        add     x1, x20, #0x140
        add     x0, x19, #0x200
        bl      L1c14
        ldr     x30, [sp, #16]
        add     x1, x20, #0x280
        add     x0, x19, #0x400
        ldp     x19, x20, [sp], #32
        b       L1c14

// mlkem768_polyvec_tobytes (0x34 bytes)
L5734:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L210c
        add     x1, x20, #0x200
        add     x0, x19, #0x180
        bl      L210c
        ldr     x30, [sp, #16]
        add     x1, x20, #0x400
        add     x0, x19, #0x300
        ldp     x19, x20, [sp], #32
        b       L210c

// mlkem768_polyvec_frombytes (0x34 bytes)
L5768:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L2144
        add     x1, x20, #0x180
        add     x0, x19, #0x200
        bl      L2144
        ldr     x30, [sp, #16]
        add     x1, x20, #0x300
        add     x0, x19, #0x400
        ldp     x19, x20, [sp], #32
        b       L2144

// mlkem768_polyvec_ntt (0x20 bytes)
L579c:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L3e74
        add     x0, x19, #0x200
        bl      L3e74
        add     x0, x19, #0x400
        ldp     x19, x30, [sp], #16
        b       L3e74

// mlkem768_polyvec_invntt_tomont (0x20 bytes)
L57bc:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L3f18
        add     x0, x19, #0x200
        bl      L3f18
        add     x0, x19, #0x400
        ldp     x19, x30, [sp], #16
        b       L3f18

// mlkem768_polyvec_basemul_acc_montgomery_cached (0xa4 bytes)
L57dc:
        add     x16, x0, #0x2
        mov     x4, #0x0
        mov     w12, #0xfffff301
        mov     w13, #0xfffff2ff
L57ec:
        add     x9, x4, #0x2
        mov     x8, x4
        mov     x5, #0x0
        mov     w7, #0x0
        mov     w6, #0x0
L5800:
        lsl     x11, x5, #8
        ldrsh   w14, [x1, x8]
        ldrsh   w15, [x2, x8]
        add     x5, x5, #0x1
        ldrsh   w10, [x1, x9]
        add     x8, x8, #0x200
        ldrsh   w11, [x3, x11]
        mul     w17, w14, w15
        madd    w11, w11, w10, w17
        mul     w10, w10, w15
        add     w6, w6, w11
        ldrsh   w11, [x2, x9]
        add     x9, x9, #0x200
        madd    w10, w11, w14, w10
        add     w7, w7, w10
        cmp     x5, #0x3
        b.ne    L5800
        mul     w5, w6, w12
        add     x3, x3, #0x2
        sxth    w5, w5
        madd    w5, w5, w13, w6
        asr     w5, w5, #16
        strh    w5, [x0, x4]
        mul     w5, w7, w12
        sxth    w5, w5
        madd    w5, w5, w13, w7
        asr     w5, w5, #16
        strh    w5, [x16, x4]
        add     x4, x4, #0x4
        cmp     x4, #0x200
        b.ne    L57ec
        ret

// mlkem768_polyvec_mulcache_compute (0x34 bytes)
L5880:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L3e00
        add     x1, x20, #0x200
        add     x0, x19, #0x100
        bl      L3e00
        ldr     x30, [sp, #16]
        add     x1, x20, #0x400
        add     x0, x19, #0x200
        ldp     x19, x20, [sp], #32
        b       L3e00

// mlkem768_polyvec_reduce (0x20 bytes)
L58b4:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L3d68
        add     x0, x19, #0x200
        bl      L3d68
        add     x0, x19, #0x400
        ldp     x19, x30, [sp], #16
        b       L3d68

// mlkem768_polyvec_add (0x34 bytes)
L58d4:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L3db8
        add     x1, x20, #0x200
        add     x0, x19, #0x200
        bl      L3db8
        ldr     x30, [sp, #16]
        add     x1, x20, #0x400
        add     x0, x19, #0x400
        ldp     x19, x20, [sp], #32
        b       L3db8

// mlkem768_polyvec_tomont (0x20 bytes)
L5908:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L3d2c
        add     x0, x19, #0x200
        bl      L3d2c
        add     x0, x19, #0x400
        ldp     x19, x30, [sp], #16
        b       L3d2c

// mlkem768_poly_getnoise_eta1_4x (0x144 bytes)
L5928:
        sub     sp, sp, #0x380
        stp     x23, x24, [sp, #48]
        mov     x24, x0
        mov     x23, x1
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0x7f
        stp     x21, x22, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        add     x20, x19, #0x200
        stp     x25, x26, [sp, #64]
        mov     x22, x2
        ldrb    w2, [sp, #896]
        stp     x27, x30, [sp, #80]
        add     x26, x19, #0x100
        add     x25, x19, #0x180
        ldp     q0, q1, [x4]
        ldr     x1, [x0]
        str     x1, [sp, #888]
        mov     x1, #0x0
        add     x1, x19, #0x280
        add     x0, x19, #0x240
        add     x4, x19, #0x2c0
        strb    w5, [x20, #32]
        stp     q0, q1, [x20]
        mov     x5, x20
        mov     x21, x3
        stp     q0, q1, [x0]
        mov     x3, x25
        add     x27, x19, #0x80
        stp     q0, q1, [x1]
        stp     q0, q1, [x4]
        strb    w6, [x20, #96]
        mov     x6, x0
        strb    w7, [x20, #160]
        mov     x7, x1
        strb    w2, [x20, #224]
        mov     x2, #0x21
        stp     x4, x2, [sp]
        mov     x2, x26
        mov     x4, #0x80
        mov     x1, x27
        mov     x0, x19
        bl      L2800
        mov     x1, x19
        mov     x0, x24
        bl      L4878
        mov     x1, x27
        mov     x0, x23
        bl      L4878
        mov     x1, x26
        mov     x0, x22
        bl      L4878
        cbz     x21, L5a10
        mov     x1, x25
        mov     x0, x21
        bl      L4878
L5a10:
        mov     x0, x19
        mov     x2, #0x200
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x100
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #888]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.eq    L5a50
        bl      L0830
L5a50:
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x30, [sp, #80]
        add     sp, sp, #0x380
        ret

// Padding (0x5a6c to 0x5a80)

        .long   0x00000000
        .long   0x00000000
        .long   0x00000000
        .long   0x00000000
        .long   0x00000000

// The read-only data (0x5a80 to 0x5c40)

// mlk_KeccakF_RoundConstants (0xc0 bytes)
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
// mlk_zetas (0x100 bytes)
        .quad   0xfa13fe99fd0afbec
        .quad   0x00ca011f058e05d5
        .quad   0x00b60629026eff55
        .quad   0x05bcfa3efb4e03c2
        .quad   0x017f0108fad3023d
        .quad   0xff7ef9be05b2fcc3
        .quad   0x026002dc03f9fd57
        .quad   0xf9ddff33019bf9fa
        .quad   0x03f7fdd8028c04c7
        .quad   0xf9f8fee605d3faf3
        .quad   0xfd66fec0fff80204
        .quad   0x05bd007efb76f9ae
        .quad   0x033efef1ffa6fcab
        .quad   0xfc49ff09fa73006b
        .quad   0xfd2bfa1c03c1fe72
        .quad   0xfb0502a5fbd701c0
        .quad   0x034b022b01aefbb1
        .quad   0x0069060e0367fb1d
        .quad   0xff1500b1024b01a6
        .quad   0x06750626fe34fedd
        .quad   0xff6d0487030aff0a
        .quad   0x045ffda605cbfcf7
        .quad   0x015dfc980284f9ca
        .quad   0xffb5ff64014901a2
        .quad   0x0262025b04490331
        .quad   0x0180fa47fafb052a
        .quad   0xfac904c2ff78fb41
        .quad   0xf985fb5d00dcfc96
        .quad   0x031afb02fa06fb5f
        .quad   0x01defc9afcaafa1a
        .quad   0x03df03e4feccff94
        .quad   0x065c05f2fa4c03be

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
