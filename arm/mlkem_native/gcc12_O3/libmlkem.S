// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// The code and read-only data of mlkem-native's libmlkem.so (gcc 12, -O3)
//
// This is a transcription of the binary
// binaries/multilevel/gcc12/O3/libmlkem.so from the binary branch of
// mlkem-native (see README.md), as loaded at an address that is a multiple
// of 4096: the start of its first segment, from address 0 up to the end of
// the read-only data. The ELF header and dynamic linking information at the
// start are given as data, as are the padding and the read-only data at the
// end, while the procedure linkage table and the code are given as
// instructions. The ADRP instructions, which compute addresses of pages
// relative to that of the instruction, are given as words. The labels are
// named after the addresses in the binary.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_libmlkem_gcc12_O3)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_libmlkem_gcc12_O3)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_libmlkem_gcc12_O3):

// ELF header and dynamic linking information (0x0 to 0x7f0)

        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x0000000100b70003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x000000000002dfd0
        .quad   0x0038004000000000
        .quad   0x0019001a00400005
        .quad   0x0000000500000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000009fa4
        .quad   0x0000000000009fa4
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
        .quad   0x0000001000000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000100000006a
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000083
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000013
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000024
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000800120000012e
        .quad   0x0000000000005400
        .quad   0x000000000000020c
        .quad   0x000800120000003e
        .quad   0x00000000000011c0
        .quad   0x00000000000000e8
        .quad   0x000800120000010d
        .quad   0x0000000000005280
        .quad   0x00000000000000e0
        .quad   0x00080012000001a9
        .quad   0x00000000000081d0
        .quad   0x000000000000020c
        .quad   0x000800120000014d
        .quad   0x0000000000007e40
        .quad   0x00000000000000e8
        .quad   0x0008001200000071
        .quad   0x0000000000001344
        .quad   0x000000000000008c
        .quad   0x000800120000002b
        .quad   0x0000000000001080
        .quad   0x0000000000000138
        .quad   0x00080012000000a4
        .quad   0x00000000000014b0
        .quad   0x0000000000000098
        .quad   0x00080012000000e4
        .quad   0x0000000000005160
        .quad   0x0000000000000094
        .quad   0x000800120000013b
        .quad   0x0000000000007d00
        .quad   0x0000000000000138
        .quad   0x0008001200000177
        .quad   0x0000000000007fc4
        .quad   0x000000000000008c
        .quad   0x000800120000008f
        .quad   0x00000000000013d0
        .quad   0x00000000000000e0
        .quad   0x000800120000015f
        .quad   0x0000000000007f30
        .quad   0x0000000000000094
        .quad   0x0008001200000121
        .quad   0x0000000000005360
        .quad   0x0000000000000098
        .quad   0x00080012000000d2
        .quad   0x0000000000005070
        .quad   0x00000000000000e8
        .quad   0x0008001200000188
        .quad   0x0000000000008050
        .quad   0x00000000000000e0
        .quad   0x000800120000019c
        .quad   0x0000000000008130
        .quad   0x0000000000000098
        .quad   0x00080012000000c0
        .quad   0x0000000000004f30
        .quad   0x0000000000000138
        .quad   0x00080012000000b2
        .quad   0x0000000000001550
        .quad   0x000000000000020c
        .quad   0x00080012000000fc
        .quad   0x00000000000051f4
        .quad   0x000000000000008c
        .quad   0x0008001200000051
        .quad   0x00000000000012b0
        .quad   0x0000000000000094
        .quad   0x6b636174735f5f00
        .quad   0x6175675f6b68635f
        .quad   0x6174735f5f006472
        .quad   0x665f6b68635f6b63
        .quad   0x736d656d006c6961
        .quad   0x6d656b6c6d007465
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
        .quad   0x6c61636f6c2f006f
        .quad   0x65622f656d6f682f
        .quad   0x722f6e6168706b63
        .quad   0x6b6c6d2f736f7065
        .quad   0x766974616e2d6d65
        .quad   0x622d6b7361742d65
        .quad   0x756f2f7972616e69
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

// The procedure linkage table and the code (0x7f0 to 0x890c)
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

// mlkem1024_gen_matrix (0x1bc bytes)
L0850:
        stp     x19, x20, [sp, #-368]!
        mov     x20, x0
        .inst   0xf00000e4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        add     x19, sp, #0x6f
        stp     x21, x22, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     x3, x19
        stp     x23, x24, [sp, #32]
        add     x0, x19, #0x100
        stp     x25, x26, [sp, #48]
        str     x30, [sp, #64]
        ldr     x5, [x4]
        str     x5, [sp, #360]
        mov     x5, #0x0
L088c:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x3]
        add     x3, x3, #0x40
        cmp     x0, x3
        b.ne    L088c
        mov     w21, #0x0
        mov     w25, #0x1
        mov     w24, #0x2
        mov     w23, #0x3
        mov     w26, #0x800
        mov     x22, #0x600
        cbnz    w2, L098c
L08bc:
        add     w5, w21, #0x3
        add     w6, w21, #0x2
        add     w7, w21, #0x1
        mov     x2, #0x400
        lsr     w5, w5, #2
        lsr     w6, w6, #2
        lsr     w7, w7, #2
        mov     x1, #0x200
        lsr     w8, w21, #2
        mov     x4, x19
        umaddl  x3, w5, w26, x22
        add     w21, w21, #0x4
        umaddl  x2, w6, w26, x2
        ubfiz   x0, x8, #11, #30
        umaddl  x1, w7, w26, x1
        add     x3, x20, x3
        add     x2, x20, x2
        add     x0, x20, x0
        add     x1, x20, x1
        strb    wzr, [x19, #32]
        strb    w8, [x19, #33]
        strb    w25, [x19, #96]
        strb    w7, [x19, #97]
        strb    w24, [x19, #160]
        strb    w6, [x19, #161]
        strb    w23, [x19, #224]
        strb    w5, [x19, #225]
        bl      L68a0
        cmp     w21, #0x10
        b.ne    L08bc
L0934:
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        stp     q0, q0, [x19, #192]
        stp     q0, q0, [x19, #224]
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #360]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L0a08
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #368
        ret
L098c:
        add     w5, w21, #0x3
        add     w6, w21, #0x2
        add     w7, w21, #0x1
        mov     x2, #0x400
        lsr     w5, w5, #2
        lsr     w6, w6, #2
        lsr     w7, w7, #2
        mov     x1, #0x200
        lsr     w8, w21, #2
        mov     x4, x19
        umaddl  x3, w5, w26, x22
        add     w21, w21, #0x4
        umaddl  x2, w6, w26, x2
        ubfiz   x0, x8, #11, #30
        umaddl  x1, w7, w26, x1
        add     x3, x20, x3
        add     x2, x20, x2
        add     x0, x20, x0
        add     x1, x20, x1
        strb    w8, [x19, #32]
        strb    wzr, [x19, #33]
        strb    w7, [x19, #96]
        strb    w25, [x19, #97]
        strb    w6, [x19, #160]
        strb    w24, [x19, #161]
        strb    w5, [x19, #224]
        strb    w23, [x19, #225]
        bl      L68a0
        cmp     w21, #0x10
        b.ne    L098c
        b       L0934
L0a08:
        bl      L0830
        nop

// mlkem1024_indcpa_keypair_derand (0x238 bytes)
L0a10:
        mov     x12, #0x3d10
        sub     sp, sp, x12
        mov     x3, #0x3c40
        mov     x4, #0x3c00
        mov     x5, #0x3800
        stp     x19, x20, [sp, #16]
        mov     w19, #0x4
        stp     x21, x22, [sp, #32]
        add     x21, sp, #0x9f
        and     x21, x21, #0xffffffffffffffe0
        stp     x23, x24, [sp, #48]
        add     x24, x21, x3
        add     x23, x21, #0x3, lsl #12
        stp     x25, x26, [sp, #64]
        add     x22, x21, x4
        add     x26, x21, x5
        stp     x27, x28, [sp, #80]
        mov     x27, x0
        add     x20, x21, #0x2, lsl #12
        str     x30, [sp, #96]
        add     x25, x22, #0x20
        str     x1, [sp, #120]
        mov     x1, x24
        ldp     q0, q1, [x2]
        mov     x28, x21
        .inst   0xf00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        ldr     x0, [x2]
        str     x0, [sp, #15624]
        mov     x0, #0x0
        stp     q0, q1, [x24]
        mov     x0, x22
        mov     x2, #0x21
        strb    w19, [x23, #3168]
        bl      L37d0
        mov     x1, x22
        mov     x0, x21
        mov     w2, #0x0
        bl      L0850
        mov     w0, #0x3
        strb    w0, [sp]
        mov     x4, x25
        add     x3, x20, #0x600
        add     x2, x20, #0x400
        add     x1, x20, #0x200
        mov     x0, x20
        mov     w7, #0x2
        mov     w6, #0x1
        mov     w5, #0x0
        bl      L1c30
        mov     x4, x25
        mov     w5, w19
        add     x1, x23, #0x200
        add     x3, x23, #0x600
        add     x2, x23, #0x400
        mov     x6, #0x2800
        mov     w0, #0x7
        strb    w0, [sp]
        mov     w7, #0x6
        add     x25, x21, x6
        mov     w6, #0x5
        mov     x0, x23
        bl      L1c30
        mov     x19, x25
        mov     x0, x20
        bl      L1860
        mov     x0, x23
        bl      L1860
        mov     x1, x20
        mov     x0, x26
        bl      L1b50
L0b2c:
        mov     x1, x28
        mov     x0, x19
        mov     x3, x26
        mov     x2, x20
        add     x19, x19, #0x200
        bl      L18c0
        add     x28, x28, #0x800
        cmp     x19, x23
        b.ne    L0b2c
        mov     x0, x25
        bl      L1c00
        mov     x1, x19
        mov     x0, x25
        bl      L1bc0
        mov     x0, x25
        bl      L1b90
        mov     x0, x20
        bl      L1b90
        ldr     x0, [sp, #120]
        mov     x1, x20
        bl      L17e0
        mov     x1, x25
        mov     x0, x27
        bl      L17e0
        add     x27, x27, #0x600
        ldp     q0, q1, [x22]
        mov     x0, x26
        mov     x2, #0x400
        mov     w1, #0x0
        stp     q0, q1, [x27]
        bl      L0840
        mov     x2, #0x800
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x25
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x2000
        mov     x0, x21
        mov     w1, #0x0
        bl      L0840
        stp     xzr, xzr, [x24]
        stp     xzr, xzr, [x24, #16]
        strb    wzr, [x24, #32]
        movi    v0.4s, #0x0
        stp     q0, q0, [x22]
        stp     q0, q0, [x22, #32]
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #15624]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L0c44
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
L0c44:
        bl      L0830
        nop
        nop

// mlkem1024_indcpa_enc (0x2c8 bytes)
L0c50:
        mov     x12, #0x4ad0
        sub     sp, sp, x12
        mov     x5, #0x4400
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0xaf
        and     x19, x19, #0xffffffffffffffe0
        mov     x20, x2
        add     x4, x19, #0x3, lsl #12
        .inst   0xf00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x21, x22, [sp, #32]
        mov     x21, x3
        stp     x23, x24, [sp, #48]
        mov     x3, #0x2800
        add     x24, x19, x3
        stp     x25, x26, [sp, #64]
        mov     x22, x1
        mov     x1, x20
        stp     x27, x28, [sp, #80]
        add     x28, x19, x5
        add     x23, x19, #0x4, lsl #12
        str     x30, [sp, #96]
        mov     x26, x19
        stp     x0, x4, [sp, #120]
        mov     x0, x4
        ldr     x3, [x2]
        str     x3, [sp, #19144]
        mov     x3, #0x0
        bl      L1820
        ldr     q0, [x20, #1536]
        mov     x6, #0x4a00
        ldr     q1, [x20, #1552]
        add     x2, x19, x6
        mov     x8, #0x3800
        mov     x7, #0x4600
        add     x20, x19, x8
        add     x0, x19, x7
        mov     x1, x22
        mov     x25, x2
        stp     q0, q1, [x2]
        str     x0, [sp, #136]
        bl      L2db0
        mov     x1, x25
        mov     x0, x19
        mov     w2, #0x1
        bl      L0850
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
        bl      L1c30
        mov     w0, #0x7
        strb    w0, [sp]
        mov     x4, x21
        add     x3, x24, #0x600
        mov     w7, #0x6
        mov     w6, #0x5
        mov     w5, #0x4
        add     x2, x24, #0x400
        add     x1, x24, #0x200
        mov     x0, x24
        bl      L1c30
        mov     x1, x21
        mov     w2, #0x8
        mov     x0, x28
        bl      L1d90
        add     x21, x19, #0x2, lsl #12
        mov     x0, x20
        bl      L1860
        mov     x27, x21
        add     x22, x21, #0x800
        mov     x1, x20
        mov     x0, x23
        bl      L1b50
L0d90:
        mov     x1, x26
        mov     x0, x27
        mov     x3, x23
        mov     x2, x20
        add     x27, x27, #0x200
        bl      L18c0
        add     x26, x26, #0x800
        cmp     x27, x22
        b.ne    L0d90
        ldr     x27, [sp, #128]
        mov     x3, x23
        mov     x2, x20
        mov     x0, #0x4800
        mov     x1, x27
        add     x22, x19, x0
        mov     x0, x22
        bl      L18c0
        mov     x0, x21
        bl      L1890
        mov     x0, x22
        bl      L5e30
        mov     x1, x24
        mov     x0, x21
        bl      L1bc0
        mov     x1, x28
        mov     x0, x22
        bl      L56b0
        ldr     x26, [sp, #136]
        mov     x0, x22
        mov     x1, x26
        bl      L56b0
        mov     x0, x21
        bl      L1b90
        mov     x0, x22
        bl      L5660
        ldr     x0, [sp, #120]
        mov     x1, x21
        bl      L1760
        ldr     x0, [sp, #120]
        mov     x1, x22
        add     x0, x0, #0x580
        bl      L2440
        mov     x0, x23
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x28
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x26
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x22
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x21
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x24
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x27
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x2000
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        stp     xzr, xzr, [x25]
        stp     xzr, xzr, [x25, #16]
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #19144]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L0f14
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
L0f14:
        bl      L0830
        nop
        nop

// mlkem1024_indcpa_dec (0x158 bytes)
L0f20:
        mov     x12, #0x1860
        sub     sp, sp, x12
        .inst   0xf00000e3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x5f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        mov     x2, #0x1600
        stp     x23, x24, [sp, #32]
        add     x21, x19, x2
        add     x20, x19, #0x800
        str     x30, [sp, #48]
        mov     x24, x0
        mov     x23, x1
        mov     x0, x20
        ldr     x2, [x3]
        str     x2, [sp, #6232]
        mov     x2, #0x0
        bl      L17a0
        add     x1, x23, #0x580
        mov     x0, x21
        bl      L2610
        add     x23, x19, #0x1, lsl #12
        mov     x1, x22
        mov     x0, x19
        bl      L1820
        mov     x0, x20
        bl      L1860
        mov     x3, #0x1400
        mov     x1, x20
        add     x22, x19, x3
        mov     x0, x23
        bl      L1b50
        mov     x3, x23
        mov     x2, x20
        mov     x1, x19
        mov     x0, x22
        bl      L18c0
        mov     x0, x22
        bl      L5e30
        mov     x1, x22
        mov     x0, x21
        bl      L56e0
        mov     x0, x21
        bl      L5660
        mov     x1, x21
        mov     x0, x24
        bl      L2ed0
        mov     x0, x23
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x22
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x21
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #6232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L1074
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x1860
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        add     sp, sp, x12
        ret
L1074:
        bl      L0830
        nop
        nop

// mlkem1024_check_pk (0x138 bytes)
L1080:
        sub     sp, sp, #0xe40
        mov     x1, x0
        .inst   0xd00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x19, x20, [sp]
        add     x20, sp, #0x3f
        and     x20, x20, #0xffffffffffffffe0
        stp     x21, x30, [sp, #16]
        mov     x19, x0
        mov     x0, x20
        ldr     x3, [x2]
        str     x3, [sp, #3640]
        mov     x3, #0x0
        add     x21, x20, #0x800
        bl      L1820
        mov     x0, x20
        bl      L1b90
        mov     x0, x21
        mov     x1, x20
        bl      L17e0
        movi    v2.4s, #0x0
        mov     x0, x19
        mov     x2, x21
        add     x1, x20, #0xe00
        mov     v3.16b, v2.16b
        nop
L10e8:
        ldr     q0, [x0], #16
        ldr     q1, [x2], #16
        eor     v0.16b, v0.16b, v1.16b
        orr     v3.16b, v3.16b, v0.16b
        eor     v2.16b, v2.16b, v0.16b
        cmp     x1, x2
        b.ne    L10e8
        movi    v1.4s, #0x0
        ext     v4.16b, v3.16b, v1.16b, #8
        ext     v0.16b, v2.16b, v1.16b, #8
        orr     v3.16b, v4.16b, v3.16b
        eor     v2.16b, v0.16b, v2.16b
        ext     v4.16b, v3.16b, v1.16b, #4
        ext     v0.16b, v2.16b, v1.16b, #4
        orr     v4.16b, v4.16b, v3.16b
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
        neg     w0, w0
        eor     w0, w1, w0, asr #16
        cmp     w1, w0, uxtb
        mov     x2, #0x600
        mov     x0, x21
        mov     w1, #0x0
        mov     w19, #0xfffffffc
        csel    w19, wzr, w19, eq
        bl      L0840
        mov     x2, #0x800
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #3640]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L11b4
        ldp     x21, x30, [sp, #16]
        mov     w0, w19
        ldp     x19, x20, [sp]
        add     sp, sp, #0xe40
        ret
L11b4:
        bl      L0830
        nop
        nop

// mlkem1024_check_sk (0xe8 bytes)
L11c0:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        add     x1, x0, #0x600
        .inst   0xd00000e3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x3f
        mov     x2, #0x620
        ldr     x4, [x3]
        str     x4, [sp, #88]
        mov     x4, #0x0
        and     x19, x19, #0xffffffffffffffe0
        mov     x0, x19
        bl      L3730
        ldp     q1, q3, [x19]
        ldr     q0, [x20, #3104]
        ldr     q2, [x20, #3120]
        eor     v0.16b, v0.16b, v1.16b
        movi    v1.4s, #0x0
        eor     v2.16b, v2.16b, v3.16b
        orr     v4.16b, v0.16b, v2.16b
        eor     v0.16b, v0.16b, v2.16b
        ext     v3.16b, v4.16b, v1.16b, #8
        ext     v2.16b, v0.16b, v1.16b, #8
        orr     v3.16b, v3.16b, v4.16b
        eor     v2.16b, v2.16b, v0.16b
        ext     v4.16b, v3.16b, v1.16b, #4
        ext     v0.16b, v2.16b, v1.16b, #4
        orr     v4.16b, v4.16b, v3.16b
        eor     v0.16b, v0.16b, v2.16b
        ext     v3.16b, v4.16b, v1.16b, #2
        ext     v2.16b, v0.16b, v1.16b, #2
        orr     v3.16b, v3.16b, v4.16b
        eor     v2.16b, v2.16b, v0.16b
        ext     v0.16b, v3.16b, v1.16b, #1
        ext     v1.16b, v2.16b, v1.16b, #1
        orr     v0.16b, v0.16b, v3.16b
        eor     v1.16b, v1.16b, v2.16b
        umov    w1, v0.b[0]
        umov    w2, v1.b[0]
        neg     w1, w1
        eor     w1, w2, w1, asr #16
        cmp     w2, w1, uxtb
        mov     w0, #0xfffffffb
        csel    w0, wzr, w0, eq
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xd00000e1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #88]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L12a4
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #96
        ret
L12a4:
        bl      L0830
        nop
        nop

// mlkem1024_keypair_derand (0x94 bytes)
L12b0:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        mov     x21, x0
        str     x30, [sp, #32]
        bl      L0a10
        mov     x2, #0x620
        mov     w20, w0
        cbnz    w0, L1314
        mov     x1, x21
        add     x0, x19, #0x600
        bl      L0810
        mov     x1, x21
        add     x0, x19, #0xc20
        mov     x2, #0x620
        bl      L3730
        ldp     q0, q1, [x22, #32]
        add     x19, x19, #0xc40
        mov     w0, w20
        stp     q0, q1, [x19]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L1314:
        mov     x0, x21
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0xc60
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mlkem1024_keypair (0x8c bytes)
L1344:
        stp     x19, x20, [sp, #-128]!
        mov     x20, x0
        .inst   0xd00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x21, x30, [sp, #16]
        add     x19, sp, #0x3f
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x1
        ldr     x1, [x2]
        str     x1, [sp, #120]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x40
        bl      L0820
        cbnz    w0, L13c4
        mov     x1, x21
        mov     x0, x20
        mov     x2, x19
        bl      L12b0
L1390:
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xd00000e1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #120]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L13cc
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #128
        ret
L13c4:
        mov     w0, #0xfffffffd
        b       L1390
L13cc:
        bl      L0830

// mlkem1024_enc_derand (0xe0 bytes)
L13d0:
        stp     x19, x20, [sp, #-224]!
        .inst   0xd00000e4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x5f
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        and     x19, x19, #0xffffffffffffffe0
        str     x30, [sp, #48]
        mov     x24, x0
        mov     x21, x2
        mov     x22, x3
        ldr     x1, [x4]
        str     x1, [sp, #216]
        mov     x1, #0x0
        mov     x0, x2
        add     x20, x19, #0x40
        bl      L1080
        cbz     w0, L1460
L141c:
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        .inst   0xd00000e1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #216]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L14ac
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #224
        ret
L1460:
        ldp     q0, q1, [x22]
        mov     x1, x21
        add     x0, x19, #0x60
        mov     x2, #0x620
        stp     q0, q1, [x20]
        bl      L3730
        mov     x1, x20
        mov     x0, x19
        mov     x2, #0x40
        bl      L37d0
        mov     x2, x21
        mov     x0, x24
        add     x3, x19, #0x20
        mov     x1, x20
        bl      L0c50
        cbnz    w0, L141c
        ldp     q0, q1, [x19]
        stp     q0, q1, [x23]
        b       L141c
L14ac:
        bl      L0830

// mlkem1024_enc (0x98 bytes)
L14b0:
        stp     x19, x20, [sp, #-112]!
        mov     x20, x0
        .inst   0xd00000e3  // adrp x3, 0x1f000
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
        bl      L0820
        cbnz    w0, L153c
        mov     x2, x22
        mov     x1, x21
        mov     x0, x20
        mov     x3, x19
        bl      L13d0
L1508:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xd00000e1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #104]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L1544
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret
L153c:
        mov     w0, #0xfffffffd
        b       L1508
L1544:
        bl      L0830
        nop
        nop

// mlkem1024_dec (0x20c bytes)
L1550:
        sub     sp, sp, #0x720
        .inst   0xd00000e3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x5f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        stp     x23, x24, [sp, #32]
        mov     x23, x0
        mov     x24, x2
        stp     x25, x30, [sp, #48]
        mov     x25, x1
        mov     x0, x2
        ldr     x1, [x3]
        str     x1, [sp, #1816]
        mov     x1, #0x0
        bl      L11c0
        cbz     w0, L1600
        mov     w20, w0
        add     x22, x19, #0x680
        add     x21, x19, #0x640
L15a4:
        mov     x0, x19
        mov     x2, #0x640
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x22]
        stp     q0, q0, [x22, #32]
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1816]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L1758
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        add     sp, sp, #0x720
        ret
L1600:
        add     x22, x19, #0x680
        mov     x2, x24
        mov     x0, x22
        mov     x1, x25
        add     x21, x19, #0x640
        bl      L0f20
        mov     w20, w0
        cbnz    w0, L15a4
        ldr     q0, [x24, #3104]
        add     x3, x19, #0x6a0
        ldr     q1, [x24, #3120]
        mov     x1, x22
        mov     x0, x21
        mov     x2, #0x40
        stp     q0, q1, [x3]
        bl      L37d0
        add     x3, x19, #0x660
        add     x2, x24, #0x600
        mov     x1, x22
        mov     x0, x19
        bl      L0c50
        mov     w20, w0
        cbnz    w0, L15a4
        movi    v2.4s, #0x0
        mov     x0, x19
        mov     x1, x25
        add     x2, x19, #0x620
        mov     v3.16b, v2.16b
L1670:
        ldr     q0, [x1], #16
        ldr     q1, [x0], #16
        eor     v0.16b, v0.16b, v1.16b
        orr     v3.16b, v3.16b, v0.16b
        eor     v2.16b, v2.16b, v0.16b
        cmp     x0, x2
        b.ne    L1670
        movi    v1.4s, #0x0
        ext     v4.16b, v3.16b, v1.16b, #8
        ext     v0.16b, v2.16b, v1.16b, #8
        orr     v3.16b, v4.16b, v3.16b
        eor     v2.16b, v0.16b, v2.16b
        ext     v4.16b, v3.16b, v1.16b, #4
        ext     v0.16b, v2.16b, v1.16b, #4
        orr     v4.16b, v4.16b, v3.16b
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
        neg     w0, w0
        eor     w0, w1, w0, asr #16
        ldr     q0, [x24, #3136]
        and     w0, w0, #0xff
        ldr     q1, [x24, #3152]
        mov     x2, #0x620
        eor     w24, w0, w1
        mov     x1, x25
        add     x0, x19, #0x20
        stp     q0, q1, [x19]
        bl      L0810
        mov     x0, x23
        mov     x2, x19
        mov     x3, #0x640
        mov     x1, #0x20
        bl      L3650
        neg     w4, w24
        sub     x23, x23, #0x1
        mov     x0, #0x1
        nop
L1728:
        add     x2, x21, x0
        mov     w1, w4
        ldurb   w2, [x2, #-1]
        ldrb    w3, [x23, x0]
        eor     w3, w2, w3
        and     w1, w3, w1, asr #16
        eor     w2, w2, w1
        strb    w2, [x23, x0]
        add     x0, x0, #0x1
        cmp     x0, #0x21
        b.ne    L1728
        b       L15a4
L1758:
        bl      L0830
        nop

// mlkem1024_polyvec_compress_du (0x3c bytes)
L1760:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x580
L1774:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x160
        bl      L2504
        add     x20, x20, #0x200
        cmp     x19, x21
        b.ne    L1774
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop

// mlkem1024_polyvec_decompress_du (0x3c bytes)
L17a0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x30, [sp, #16]
        add     x21, x1, #0x580
L17b4:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x160
        bl      L2724
        add     x20, x20, #0x200
        cmp     x19, x21
        b.ne    L17b4
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop

// mlkem1024_polyvec_tobytes (0x3c bytes)
L17e0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x600
L17f4:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x180
        bl      L2870
        add     x20, x20, #0x200
        cmp     x19, x21
        b.ne    L17f4
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop

// mlkem1024_polyvec_frombytes (0x3c bytes)
L1820:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x30, [sp, #16]
        add     x21, x1, #0x600
L1834:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x180
        bl      L2aa4
        add     x20, x20, #0x200
        cmp     x19, x21
        b.ne    L1834
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop

// mlkem1024_polyvec_ntt (0x28 bytes)
L1860:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L5b30
        add     x0, x19, #0x200
        bl      L5b30
        add     x0, x19, #0x400
        bl      L5b30
        add     x0, x19, #0x600
        ldp     x19, x30, [sp], #16
        b       L5b30
        nop
        nop

// mlkem1024_polyvec_invntt_tomont (0x28 bytes)
L1890:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L5e30
        add     x0, x19, #0x200
        bl      L5e30
        add     x0, x19, #0x400
        bl      L5e30
        add     x0, x19, #0x600
        ldp     x19, x30, [sp], #16
        b       L5e30
        nop
        nop

// mlkem1024_polyvec_basemul_acc_montgomery_cached (0x288 bytes)
L18c0:
        stp     x19, x20, [sp, #-128]!
        mov     x7, x0
        add     x0, x0, #0x200
        str     x30, [sp, #32]
        cmp     x3, x0
        mov     x6, x3
        add     x3, x3, #0x400
        mov     x0, x1
        ccmp    x7, x3, #0x2, cc
        mov     x1, x2
        b.cc    L1a40
        .inst   0xf0000022  // adrp x2, 0x8000
        add     x8, x6, #0x200
        mvni    v6.8h, #0xd, lsl #8
        stp     d8, d9, [sp, #48]
        ldr     q7, [x2, #2336]
        mov     x2, x0
        add     x0, x6, #0x100
        stp     d10, d11, [sp, #64]
        stp     d12, d13, [sp, #80]
        stp     d14, d15, [sp, #96]
        nop
L1918:
        add     x4, x2, #0x200
        add     x3, x1, #0x200
        add     x6, x2, #0x400
        ld2     {v30.8h-v31.8h}, [x2]
        add     x5, x1, #0x400
        ld2     {v24.8h-v25.8h}, [x4]
        add     x4, x2, #0x600
        ld2     {v10.8h-v11.8h}, [x3]
        add     x3, x1, #0x600
        ld2     {v12.8h-v13.8h}, [x1]
        add     x2, x2, #0x20
        smull2  v2.4s, v10.8h, v24.8h
        str     q10, [sp, #112]
        add     x1, x1, #0x20
        smull   v3.4s, v10.4h, v24.4h
        smull2  v1.4s, v13.8h, v30.8h
        smull   v0.4s, v13.4h, v30.4h
        ld2     {v18.8h-v19.8h}, [x6]
        ld2     {v26.8h-v27.8h}, [x5]
        smlal2  v2.4s, v12.8h, v30.8h
        smlal   v3.4s, v12.4h, v30.4h
        smlal2  v1.4s, v12.8h, v31.8h
        smlal   v0.4s, v12.4h, v31.4h
        ld2     {v4.8h-v5.8h}, [x4]
        ld2     {v20.8h-v21.8h}, [x3]
        smlal2  v2.4s, v18.8h, v26.8h
        smlal   v3.4s, v18.4h, v26.4h
        smlal2  v1.4s, v11.8h, v24.8h
        smlal   v0.4s, v11.4h, v24.4h
        ldur    q13, [x0, #-256]
        add     x0, x0, #0x10
        smlal2  v2.4s, v4.8h, v20.8h
        smlal   v3.4s, v4.4h, v20.4h
        smlal2  v1.4s, v10.8h, v25.8h
        smlal   v0.4s, v10.4h, v25.4h
        ldur    q8, [x0, #-16]
        smlal2  v1.4s, v18.8h, v27.8h
        smlal   v0.4s, v18.4h, v27.4h
        smlal2  v2.4s, v13.8h, v31.8h
        smlal   v3.4s, v13.4h, v31.4h
        ldr     q10, [x0, #240]
        smlal2  v2.4s, v8.8h, v25.8h
        smlal   v3.4s, v8.4h, v25.4h
        smlal2  v1.4s, v19.8h, v26.8h
        smlal   v0.4s, v19.4h, v26.4h
        ldr     q8, [x0, #496]
        smlal2  v1.4s, v4.8h, v21.8h
        smlal   v0.4s, v4.4h, v21.4h
        smlal2  v2.4s, v19.8h, v10.8h
        smlal   v3.4s, v19.4h, v10.4h
        smlal2  v1.4s, v5.8h, v20.8h
        smlal   v0.4s, v5.4h, v20.4h
        smlal2  v2.4s, v5.8h, v8.8h
        smlal   v3.4s, v5.4h, v8.4h
        uzp1    v4.8h, v0.8h, v1.8h
        uzp1    v8.8h, v3.8h, v2.8h
        mul     v4.8h, v4.8h, v7.8h
        mul     v5.8h, v8.8h, v7.8h
        smlal   v0.4s, v4.4h, v6.4h
        smlal2  v1.4s, v4.8h, v6.8h
        smlal   v3.4s, v5.4h, v6.4h
        smlal2  v2.4s, v5.8h, v6.8h
        uzp2    v17.8h, v0.8h, v1.8h
        uzp2    v16.8h, v3.8h, v2.8h
        st2     {v16.8h-v17.8h}, [x7], #32
        cmp     x0, x8
        b.ne    L1918
        ldr     x30, [sp, #32]
        ldp     d8, d9, [sp, #48]
        ldp     d10, d11, [sp, #64]
        ldp     d12, d13, [sp, #80]
        ldp     d14, d15, [sp, #96]
        ldp     x19, x20, [sp], #128
        ret
L1a40:
        add     x10, x0, #0x200
        mov     w9, #0xfffff301
        mov     w8, #0xfffff2ff
        stp     x21, x22, [sp, #16]
L1a50:
        ldrsh   w13, [x0, #2]
        ldrsh   w4, [x1]
        add     x0, x0, #0x4
        ldursh  w21, [x0, #-4]
        add     x6, x6, #0x2
        ldrsh   w2, [x1, #512]
        add     x7, x7, #0x4
        ldrsh   w12, [x0, #510]
        add     x1, x1, #0x4
        ldrsh   w11, [x0, #508]
        mul     w19, w4, w13
        ldursh  w3, [x6, #-2]
        mul     w14, w4, w21
        ldrsh   w20, [x0, #1022]
        ldrsh   w4, [x1, #1020]
        mul     w5, w2, w12
        ldrsh   w17, [x0, #1020]
        mul     w16, w2, w11
        ldrsh   w15, [x6, #254]
        madd    w3, w3, w13, w14
        ldrsh   w2, [x1, #510]
        ldursh  w14, [x1, #-2]
        ldrsh   w30, [x0, #1534]
        mul     w22, w4, w17
        ldrsh   w18, [x0, #1532]
        madd    w15, w15, w12, w16
        ldrsh   w13, [x6, #510]
        mul     w16, w4, w20
        ldrsh   w12, [x1, #1022]
        madd    w2, w2, w11, w5
        ldrsh   w4, [x1, #1532]
        madd    w14, w14, w21, w19
        ldrsh   w5, [x1, #1534]
        add     w3, w3, w15
        ldrsh   w11, [x6, #766]
        madd    w13, w13, w20, w22
        madd    w12, w12, w17, w16
        add     w2, w2, w14
        mul     w15, w4, w18
        add     w3, w3, w13
        mul     w4, w4, w30
        add     w2, w2, w12
        madd    w4, w5, w18, w4
        madd    w11, w11, w30, w15
        add     w2, w2, w4
        add     w3, w3, w11
        mul     w4, w2, w9
        mul     w5, w3, w9
        sxth    w4, w4
        sxth    w5, w5
        madd    w2, w4, w8, w2
        madd    w3, w5, w8, w3
        asr     w2, w2, #16
        sturh   w2, [x7, #-2]
        asr     w3, w3, #16
        sturh   w3, [x7, #-4]
        cmp     x0, x10
        b.ne    L1a50
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #128
        ret
        nop
        nop

// mlkem1024_polyvec_mulcache_compute (0x3c bytes)
L1b50:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x400
L1b64:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x100
        bl      L5710
        add     x20, x20, #0x200
        cmp     x19, x21
        b.ne    L1b64
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop

// mlkem1024_polyvec_reduce (0x28 bytes)
L1b90:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L5660
        add     x0, x19, #0x200
        bl      L5660
        add     x0, x19, #0x400
        bl      L5660
        add     x0, x19, #0x600
        ldp     x19, x30, [sp], #16
        b       L5660
        nop
        nop

// mlkem1024_polyvec_add (0x38 bytes)
L1bc0:
        stp     x19, x20, [sp, #-32]!
        mov     x20, x1
        mov     x19, #0x0
        stp     x21, x30, [sp, #16]
        mov     x21, x0
L1bd4:
        add     x1, x20, x19
        add     x0, x21, x19
        add     x19, x19, #0x200
        bl      L56b0
        cmp     x19, #0x800
        b.ne    L1bd4
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop
        nop

// mlkem1024_polyvec_tomont (0x28 bytes)
L1c00:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L5610
        add     x0, x19, #0x200
        bl      L5610
        add     x0, x19, #0x400
        bl      L5610
        add     x0, x19, #0x600
        ldp     x19, x30, [sp], #16
        b       L5610
        nop
        nop

// mlkem1024_poly_getnoise_eta1_4x (0x158 bytes)
L1c30:
        sub     sp, sp, #0x380
        stp     x19, x20, [sp, #16]
        add     x20, sp, #0x7f
        and     x20, x20, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        add     x10, x20, #0x240
        add     x9, x20, #0x280
        stp     x23, x24, [sp, #48]
        add     x19, x20, #0x200
        mov     x22, x2
        stp     x25, x26, [sp, #64]
        add     x8, x20, #0x2c0
        add     x25, x20, #0x100
        stp     x27, x30, [sp, #80]
        add     x27, x20, #0x180
        mov     x21, x3
        ldp     q0, q1, [x4]
        mov     x3, x27
        .inst   0xd00000e4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        mov     x24, x0
        mov     x23, x1
        mov     x0, x20
        ldr     x2, [x4]
        str     x2, [sp, #888]
        mov     x2, #0x0
        stp     q0, q1, [x9]
        mov     x2, x25
        stp     q0, q1, [x10]
        mov     x4, #0x80
        add     x26, x20, x4
        strb    w5, [x19, #32]
        mov     x5, x19
        strb    w6, [x19, #96]
        mov     x6, x10
        strb    w7, [x19, #160]
        mov     x7, x9
        mov     x9, #0x21
        stp     x8, x9, [sp]
        ldrb    w9, [sp, #896]
        stp     q0, q1, [x8]
        mov     x1, x26
        strb    w9, [x19, #224]
        stp     q0, q1, [x19]
        bl      L3b80
        mov     x1, x20
        mov     x0, x24
        bl      L6fe0
        mov     x1, x26
        mov     x0, x23
        bl      L6fe0
        mov     x1, x25
        mov     x0, x22
        bl      L6fe0
        cbz     x21, L1d18
        mov     x1, x27
        mov     x0, x21
        bl      L6fe0
L1d18:
        mov     x0, x20
        mov     x2, #0x200
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        stp     q0, q0, [x19, #192]
        stp     q0, q0, [x19, #224]
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #888]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L1d84
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x30, [sp, #80]
        add     sp, sp, #0x380
        ret
L1d84:
        bl      L0830
        nop
        nop

// mlkem1024_poly_getnoise_eta2 (0xa4 bytes)
L1d90:
        stp     x19, x20, [sp, #-240]!
        mov     x3, #0x21
        add     x19, sp, #0x3f
        stp     x21, x30, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        .inst   0xd00000e4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        add     x20, x19, #0x80
        ldp     q0, q1, [x1]
        mov     x21, x0
        ldr     x0, [x4]
        str     x0, [sp, #232]
        mov     x0, #0x0
        strb    w2, [x20, #32]
        mov     x2, x20
        mov     x0, x19
        mov     x1, #0x80
        stp     q0, q1, [x20]
        bl      L3650
        mov     x1, x19
        mov     x0, x21
        bl      L6fe0
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     xzr, xzr, [x19, #128]
        stp     xzr, xzr, [x20, #16]
        strb    wzr, [x20, #32]
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L1e30
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #240
        ret
L1e30:
        bl      L0830
        nop
        nop
        nop

// mlkem_poly_compress_d4 (0x190 bytes)
L1e40:
        mov     x2, x0
        mov     x0, x1
        add     x1, x2, #0x80
        add     x11, x0, #0x200
        cmp     x0, x1
        ccmp    x2, x11, #0x2, cc
        b.cc    L1f3c
        movi    v1.4s, #0x8, lsl #24
        .inst   0xf0000021  // adrp x1, 0x8000
        ldr     q2, [x1, #2352]
        mov     x1, x2
        nop
L1e70:
        ldp     q4, q0, [x0]
        ldp     q3, q6, [x0, #32]
        add     x0, x0, #0x40
        uzp2    v5.8h, v4.8h, v0.8h
        mov     v18.16b, v1.16b
        uzp1    v4.8h, v4.8h, v0.8h
        uzp2    v0.8h, v3.8h, v6.8h
        uzp1    v3.8h, v3.8h, v6.8h
        sxtl2   v6.4s, v5.8h
        sxtl    v16.4s, v5.4h
        sxtl    v7.4s, v0.4h
        sxtl2   v5.4s, v0.8h
        mla     v18.4s, v6.4s, v2.4s
        mov     v17.16b, v1.16b
        mov     v0.16b, v1.16b
        mov     v6.16b, v1.16b
        ushr    v18.4s, v18.4s, #28
        mla     v17.4s, v5.4s, v2.4s
        mla     v0.4s, v16.4s, v2.4s
        sxtl2   v5.4s, v4.8h
        sxtl    v16.4s, v4.4h
        mla     v6.4s, v7.4s, v2.4s
        sxtl2   v4.4s, v3.8h
        sxtl    v7.4s, v3.4h
        mov     v3.16b, v1.16b
        ushr    v0.4s, v0.4s, #28
        ushr    v6.4s, v6.4s, #28
        ushr    v17.4s, v17.4s, #28
        mla     v3.4s, v16.4s, v2.4s
        mov     v16.16b, v1.16b
        uzp1    v0.8h, v0.8h, v18.8h
        uzp1    v6.8h, v6.8h, v17.8h
        ushr    v3.4s, v3.4s, #28
        mla     v16.4s, v5.4s, v2.4s
        mov     v5.16b, v1.16b
        uzp1    v0.16b, v0.16b, v6.16b
        ushr    v16.4s, v16.4s, #28
        mla     v5.4s, v7.4s, v2.4s
        mov     v7.16b, v1.16b
        shl     v0.16b, v0.16b, #4
        uzp1    v3.8h, v3.8h, v16.8h
        mla     v7.4s, v4.4s, v2.4s
        ushr    v4.4s, v5.4s, #28
        ushr    v5.4s, v7.4s, #28
        uzp1    v4.8h, v4.8h, v5.8h
        uzp1    v3.16b, v3.16b, v4.16b
        orr     v0.16b, v0.16b, v3.16b
        str     q0, [x1], #16
        cmp     x11, x0
        b.ne    L1e70
        ret
L1f3c:
        mov     w3, #0xafb0
        mov     x1, x2
        movk    w3, #0x13, lsl #16
        mov     w2, #0x8000000
        nop
L1f50:
        ldrsh   w6, [x0, #6]
        add     x1, x1, #0x4
        ldrsh   w5, [x0, #10]
        ldrsh   w4, [x0, #14]
        ldrsh   w7, [x0, #2]
        ldrsh   w12, [x0, #4]
        madd    w6, w6, w3, w2
        ldrsh   w10, [x0, #8]
        madd    w5, w5, w3, w2
        ldrsh   w9, [x0, #12]
        madd    w4, w4, w3, w2
        ldrsh   w8, [x0], #16
        madd    w7, w7, w3, w2
        madd    w12, w12, w3, w2
        lsr     w6, w6, #28
        madd    w10, w10, w3, w2
        lsr     w5, w5, #28
        madd    w9, w9, w3, w2
        lsr     w4, w4, #28
        madd    w8, w8, w3, w2
        lsr     w7, w7, #28
        extr    w6, w6, w12, #28
        extr    w5, w5, w10, #28
        extr    w4, w4, w9, #28
        sturb   w6, [x1, #-3]
        extr    w7, w7, w8, #28
        sturb   w7, [x1, #-4]
        sturb   w5, [x1, #-2]
        sturb   w4, [x1, #-1]
        cmp     x0, x11
        b.ne    L1f50
        ret

// mlkem_poly_compress_d10 (0x8c bytes)
L1fd0:
        mov     x7, #0xbc00
        mov     x3, x0
        mov     x5, x1
        add     x11, x0, #0x140
        movk    x7, #0x9d7d, lsl #16
        mov     x6, #0x100000000
L1fe8:
        ldrsh   x2, [x5, #2]
        add     x3, x3, #0x5
        ldrsh   x1, [x5, #4]
        add     x5, x5, #0x8
        ldursh  x0, [x5, #-2]
        ldursh  x4, [x5, #-8]
        madd    x2, x2, x7, x6
        madd    x1, x1, x7, x6
        madd    x0, x0, x7, x6
        madd    x4, x4, x7, x6
        ubfx    x2, x2, #33, #10
        ubfx    x1, x1, #33, #10
        ubfx    x0, x0, #33, #10
        lsl     w8, w2, #2
        ubfx    x4, x4, #33, #10
        lsl     w10, w1, #4
        lsl     w9, w0, #6
        orr     w2, w10, w2, lsr #6
        orr     w8, w8, w4, lsr #8
        orr     w1, w9, w1, lsr #4
        lsr     w0, w0, #2
        sturb   w4, [x3, #-5]
        sturb   w8, [x3, #-4]
        sturb   w2, [x3, #-3]
        sturb   w1, [x3, #-2]
        sturb   w0, [x3, #-1]
        cmp     x11, x3
        b.ne    L1fe8
        ret
        nop

// mlkem_poly_decompress_d4 (0x348 bytes)
L2060:
        add     x4, x0, #0x200
        add     x2, x1, #0x80
        cmp     x1, x4
        ccmp    x0, x2, #0x2, cc
        b.cc    L235c
        ldr     q7, [x1]
        .inst   0xd0000022  // adrp x2, 0x8000
        movi    v0.8h, #0x8
        add     x15, x0, #0x40
        movi    v6.16b, #0xf
        add     x14, x0, #0x60
        ushr    v16.16b, v7.16b, #4
        add     x13, x0, #0x80
        ldr     q1, [x2, #2368]
        add     x12, x0, #0xa0
        and     v7.16b, v7.16b, v6.16b
        add     x11, x0, #0xc0
        uxtl    v19.8h, v16.8b
        add     x10, x0, #0xe0
        mov     v17.16b, v0.16b
        add     x9, x0, #0x100
        uxtl2   v16.8h, v16.16b
        add     x8, x0, #0x120
        uxtl    v18.8h, v7.8b
        add     x7, x0, #0x140
        uxtl2   v7.8h, v7.16b
        add     x6, x0, #0x160
        mla     v17.8h, v19.8h, v1.8h
        add     x5, x0, #0x180
        mov     v19.16b, v0.16b
        add     x4, x0, #0x1a0
        add     x3, x0, #0x1c0
        add     x2, x0, #0x1e0
        ushr    v5.8h, v17.8h, #4
        mla     v19.8h, v18.8h, v1.8h
        mov     v18.16b, v0.16b
        ushr    v4.8h, v19.8h, #4
        mla     v18.8h, v7.8h, v1.8h
        mov     v7.16b, v0.16b
        mov     v19.16b, v0.16b
        st2     {v4.8h-v5.8h}, [x0], #32
        mla     v7.8h, v16.8h, v1.8h
        ushr    v2.8h, v18.8h, #4
        mov     v18.16b, v0.16b
        ushr    v3.8h, v7.8h, #4
        st2     {v2.8h-v3.8h}, [x0]
        ldr     q7, [x1, #16]
        and     v16.16b, v7.16b, v6.16b
        ushr    v7.16b, v7.16b, #4
        uxtl    v17.8h, v16.8b
        uxtl2   v16.8h, v16.16b
        uxtl    v20.8h, v7.8b
        uxtl2   v7.8h, v7.16b
        mla     v19.8h, v17.8h, v1.8h
        mov     v17.16b, v0.16b
        mla     v18.8h, v16.8h, v1.8h
        mov     v16.16b, v0.16b
        ushr    v4.8h, v19.8h, #4
        mla     v17.8h, v20.8h, v1.8h
        ushr    v2.8h, v18.8h, #4
        mla     v16.8h, v7.8h, v1.8h
        mov     v19.16b, v0.16b
        ushr    v5.8h, v17.8h, #4
        mov     v18.16b, v0.16b
        ushr    v3.8h, v16.8h, #4
        st2     {v4.8h-v5.8h}, [x15]
        st2     {v2.8h-v3.8h}, [x14]
        ldr     q7, [x1, #32]
        and     v16.16b, v7.16b, v6.16b
        ushr    v7.16b, v7.16b, #4
        uxtl    v17.8h, v16.8b
        uxtl2   v16.8h, v16.16b
        uxtl    v20.8h, v7.8b
        uxtl2   v7.8h, v7.16b
        mla     v19.8h, v17.8h, v1.8h
        mov     v17.16b, v0.16b
        mla     v18.8h, v16.8h, v1.8h
        mov     v16.16b, v0.16b
        ushr    v4.8h, v19.8h, #4
        mla     v17.8h, v20.8h, v1.8h
        ushr    v2.8h, v18.8h, #4
        mla     v16.8h, v7.8h, v1.8h
        mov     v19.16b, v0.16b
        ushr    v5.8h, v17.8h, #4
        mov     v18.16b, v0.16b
        ushr    v3.8h, v16.8h, #4
        st2     {v4.8h-v5.8h}, [x13]
        st2     {v2.8h-v3.8h}, [x12]
        ldr     q7, [x1, #48]
        and     v16.16b, v7.16b, v6.16b
        ushr    v7.16b, v7.16b, #4
        uxtl    v17.8h, v16.8b
        uxtl2   v16.8h, v16.16b
        uxtl    v20.8h, v7.8b
        uxtl2   v7.8h, v7.16b
        mla     v19.8h, v17.8h, v1.8h
        mov     v17.16b, v0.16b
        mla     v18.8h, v16.8h, v1.8h
        mov     v16.16b, v0.16b
        ushr    v4.8h, v19.8h, #4
        mla     v17.8h, v20.8h, v1.8h
        ushr    v2.8h, v18.8h, #4
        mla     v16.8h, v7.8h, v1.8h
        mov     v19.16b, v0.16b
        ushr    v5.8h, v17.8h, #4
        mov     v18.16b, v0.16b
        ushr    v3.8h, v16.8h, #4
        st2     {v4.8h-v5.8h}, [x11]
        st2     {v2.8h-v3.8h}, [x10]
        ldr     q7, [x1, #64]
        and     v16.16b, v7.16b, v6.16b
        ushr    v7.16b, v7.16b, #4
        uxtl    v17.8h, v16.8b
        uxtl2   v16.8h, v16.16b
        uxtl    v20.8h, v7.8b
        uxtl2   v7.8h, v7.16b
        mla     v19.8h, v17.8h, v1.8h
        mov     v17.16b, v0.16b
        mla     v18.8h, v16.8h, v1.8h
        mov     v16.16b, v0.16b
        ushr    v4.8h, v19.8h, #4
        mla     v17.8h, v20.8h, v1.8h
        ushr    v2.8h, v18.8h, #4
        mla     v16.8h, v7.8h, v1.8h
        mov     v19.16b, v0.16b
        ushr    v5.8h, v17.8h, #4
        mov     v18.16b, v0.16b
        ushr    v3.8h, v16.8h, #4
        st2     {v4.8h-v5.8h}, [x9]
        st2     {v2.8h-v3.8h}, [x8]
        ldr     q7, [x1, #80]
        and     v16.16b, v7.16b, v6.16b
        ushr    v7.16b, v7.16b, #4
        uxtl    v17.8h, v16.8b
        uxtl2   v16.8h, v16.16b
        uxtl    v20.8h, v7.8b
        uxtl2   v7.8h, v7.16b
        mla     v19.8h, v17.8h, v1.8h
        mov     v17.16b, v0.16b
        mla     v18.8h, v16.8h, v1.8h
        mov     v16.16b, v0.16b
        ushr    v4.8h, v19.8h, #4
        mla     v17.8h, v20.8h, v1.8h
        ushr    v2.8h, v18.8h, #4
        mla     v16.8h, v7.8h, v1.8h
        mov     v19.16b, v0.16b
        ushr    v5.8h, v17.8h, #4
        mov     v18.16b, v0.16b
        ushr    v3.8h, v16.8h, #4
        st2     {v4.8h-v5.8h}, [x7]
        st2     {v2.8h-v3.8h}, [x6]
        ldr     q7, [x1, #96]
        and     v16.16b, v7.16b, v6.16b
        ushr    v7.16b, v7.16b, #4
        uxtl    v17.8h, v16.8b
        uxtl2   v16.8h, v16.16b
        uxtl    v20.8h, v7.8b
        uxtl2   v7.8h, v7.16b
        mla     v19.8h, v17.8h, v1.8h
        mov     v17.16b, v0.16b
        mla     v18.8h, v16.8h, v1.8h
        mov     v16.16b, v0.16b
        ushr    v4.8h, v19.8h, #4
        mla     v17.8h, v20.8h, v1.8h
        ushr    v2.8h, v18.8h, #4
        mla     v16.8h, v7.8h, v1.8h
        ushr    v5.8h, v17.8h, #4
        mov     v17.16b, v0.16b
        ushr    v3.8h, v16.8h, #4
        st2     {v4.8h-v5.8h}, [x5]
        st2     {v2.8h-v3.8h}, [x4]
        ldr     q7, [x1, #112]
        and     v6.16b, v7.16b, v6.16b
        ushr    v7.16b, v7.16b, #4
        uxtl    v16.8h, v6.8b
        uxtl2   v6.8h, v6.16b
        uxtl    v18.8h, v7.8b
        uxtl2   v7.8h, v7.16b
        mla     v17.8h, v16.8h, v1.8h
        mov     v16.16b, v0.16b
        ushr    v4.8h, v17.8h, #4
        mla     v16.8h, v6.8h, v1.8h
        mov     v6.16b, v0.16b
        mla     v0.8h, v7.8h, v1.8h
        ushr    v2.8h, v16.8h, #4
        mla     v6.8h, v18.8h, v1.8h
        ushr    v3.8h, v0.8h, #4
        ushr    v5.8h, v6.8h, #4
        st2     {v4.8h-v5.8h}, [x3]
        st2     {v2.8h-v3.8h}, [x2]
        ret
L235c:
        mov     x2, x1
        mov     x1, x0
        mov     w3, #0xd01
L2368:
        ldrb    w0, [x2]
        add     x1, x1, #0x4
        and     w0, w0, #0xf
        mul     w0, w0, w3
        add     w0, w0, #0x8
        lsr     w0, w0, #4
        sturh   w0, [x1, #-4]
        ldrb    w0, [x2], #1
        lsr     w0, w0, #4
        mul     w0, w0, w3
        add     w0, w0, #0x8
        lsr     w0, w0, #4
        sturh   w0, [x1, #-2]
        cmp     x4, x1
        b.ne    L2368
        ret
        nop
        nop

// mlkem_poly_decompress_d10 (0x8c bytes)
L23b0:
        movi    v1.4s, #0x2, lsl #8
        mov     x2, x1
        mov     x7, x0
        add     x9, x1, #0x140
        mov     w6, #0xd01
        nop
L23c8:
        ldrb    w1, [x2, #2]
        add     x2, x2, #0x5
        ldurb   w3, [x2, #-4]
        ldurh   w0, [x2, #-5]
        lsl     w4, w1, #6
        ldurb   w5, [x2, #-2]
        orr     w3, w4, w3, lsr #2
        and     w0, w0, #0x3ff
        and     w3, w3, #0x3ff
        ldurb   w4, [x2, #-1]
        lsl     w8, w5, #4
        lsr     w5, w5, #6
        mul     w0, w0, w6
        orr     w1, w8, w1, lsr #4
        fmov    s0, w0
        mul     w0, w3, w6
        and     w1, w1, #0x3ff
        orr     w3, w5, w4, lsl #2
        mov     v0.s[1], w0
        mul     w1, w1, w6
        mul     w0, w3, w6
        mov     v0.s[2], w1
        mov     v0.s[3], w0
        add     v0.4s, v0.4s, v1.4s
        shrn    v0.4h, v0.4s, #10
        str     d0, [x7], #8
        cmp     x2, x9
        b.ne    L23c8
        ret
        nop

// mlkem_poly_compress_d5 (0xc4 bytes)
L2440:
        mov     w9, #0xafc0
        mov     x7, x0
        mov     x2, x1
        add     x10, x0, #0xa0
        movk    w9, #0x13, lsl #16
        mov     w8, #0x4000000
L2458:
        ldrsh   w1, [x2, #4]
        add     x7, x7, #0x5
        ldrsh   w0, [x2, #10]
        ldrsh   w5, [x2, #2]
        ldrsh   w6, [x2, #8]
        ldrsh   w11, [x2, #14]
        madd    w1, w1, w9, w8
        ldrsh   w4, [x2, #6]
        madd    w0, w0, w9, w8
        ldrsh   w3, [x2, #12]
        madd    w5, w5, w9, w8
        ldrsh   w12, [x2], #16
        madd    w6, w6, w9, w8
        madd    w11, w11, w9, w8
        lsr     w1, w1, #27
        madd    w4, w4, w9, w8
        lsr     w0, w0, #27
        madd    w3, w3, w9, w8
        lsr     w5, w5, #27
        lsr     w6, w6, #27
        madd    w12, w12, w9, w8
        lsr     w11, w11, #27
        lsr     w4, w4, #27
        lsr     w3, w3, #27
        lsl     w1, w1, #2
        lsl     w0, w0, #1
        orr     w1, w1, w5, lsr #3
        orr     w0, w0, w6, lsr #4
        lsl     w11, w11, #3
        lsl     w6, w6, #4
        orr     w1, w1, w4, lsl #7
        orr     w0, w0, w3, lsl #6
        orr     w4, w6, w4, lsr #1
        orr     w3, w11, w3, lsr #2
        extr    w5, w5, w12, #27
        sturb   w5, [x7, #-5]
        sturb   w1, [x7, #-4]
        sturb   w4, [x7, #-3]
        sturb   w0, [x7, #-2]
        sturb   w3, [x7, #-1]
        cmp     x10, x7
        b.ne    L2458
        ret

// mlkem_poly_compress_d11 (0x10c bytes)
L2504:
        mov     x8, #0x7800
        mov     x9, x0
        movk    x8, #0x3afb, lsl #16
        add     x10, x0, #0x160
        movk    x8, #0x1, lsl #32
        mov     x7, #0x100000000
        nop
L2520:
        ldrsh   x11, [x1, #2]
        add     x9, x9, #0xb
        ldrsh   x0, [x1]
        add     x1, x1, #0x10
        ldursh  x3, [x1, #-12]
        ldursh  x5, [x1, #-10]
        madd    x11, x11, x8, x7
        ldursh  x4, [x1, #-8]
        madd    x0, x0, x8, x7
        ldursh  x2, [x1, #-6]
        madd    x3, x3, x8, x7
        ldursh  x6, [x1, #-4]
        ubfx    x11, x11, #33, #11
        madd    x5, x5, x8, x7
        ubfx    x12, x0, #41, #3
        ubfx    x0, x0, #33, #11
        orr     w12, w12, w11, lsl #3
        fmov    d0, x0
        ubfx    x0, x3, #33, #11
        fmov    s1, w0
        mov     v0.b[1], w12
        ubfx    x5, x5, #33, #11
        lsl     w3, w0, #6
        ushr    v2.2s, v1.2s, #2
        orr     w11, w3, w11, lsr #5
        madd    x4, x4, x8, x7
        lsl     w3, w5, #1
        madd    x6, x6, x8, x7
        mov     v0.b[2], w11
        orr     w3, w3, w0, lsr #10
        ubfx    x4, x4, #33, #11
        madd    x0, x2, x8, x7
        ldursh  x2, [x1, #-2]
        ubfx    x6, x6, #33, #11
        lsl     w12, w4, #4
        mov     v0.b[3], v2.b[0]
        orr     w5, w12, w5, lsr #7
        ubfx    x0, x0, #33, #11
        fmov    s1, w0
        madd    x2, x2, x8, x7
        lsl     w11, w0, #7
        ushr    v1.2s, v1.2s, #1
        mov     v0.b[4], w3
        orr     w4, w11, w4, lsr #4
        ubfx    x2, x2, #33, #11
        lsl     w11, w6, #2
        orr     w0, w11, w0, lsr #9
        sturb   w0, [x9, #-3]
        lsl     w0, w2, #5
        lsr     w2, w2, #3
        mov     v0.b[5], w5
        orr     w6, w0, w6, lsr #6
        sturb   w6, [x9, #-2]
        sturb   w2, [x9, #-1]
        mov     v0.b[6], w4
        mov     v0.b[7], v1.b[0]
        stur    d0, [x9, #-11]
        cmp     x9, x10
        b.ne    L2520
        ret

// mlkem_poly_decompress_d5 (0x114 bytes)
L2610:
        mov     x6, x1
        mov     x8, x0
        add     x9, x1, #0xa0
        mov     w7, #0xd01
L2620:
        ldrb    w2, [x6, #1]
        add     x6, x6, #0x5
        ldurb   w0, [x6, #-5]
        ldurb   w3, [x6, #-2]
        ldurb   w12, [x6, #-3]
        lsl     w4, w2, #3
        orr     w4, w4, w0, lsr #5
        and     w0, w0, #0x1f
        lsl     w1, w3, #4
        and     w4, w4, #0x1f
        orr     w1, w1, w12, lsr #4
        ubfx    x11, x3, #1, #5
        and     w1, w1, #0x1f
        ldurb   w5, [x6, #-1]
        mul     w4, w4, w7
        lsl     w12, w12, #1
        mul     w0, w0, w7
        add     w4, w4, #0x10
        mul     w1, w1, w7
        fmov    s0, w4
        mul     w11, w11, w7
        lsl     w10, w5, #2
        add     w0, w0, #0x10
        ushr    v2.2s, v0.2s, #5
        orr     w3, w10, w3, lsr #6
        add     w1, w1, #0x10
        fmov    s0, w0
        fmov    s1, w1
        add     w11, w11, #0x10
        fmov    s3, w11
        ubfx    x10, x2, #2, #5
        and     w3, w3, #0x1f
        ushr    v0.2s, v0.2s, #5
        ushr    v3.2s, v3.2s, #5
        ushr    v1.2s, v1.2s, #5
        mul     w4, w10, w7
        orr     w0, w12, w2, lsr #7
        mul     w1, w3, w7
        and     w0, w0, #0x1f
        mov     v0.s[1], v2.s[0]
        add     w2, w4, #0x10
        mov     v1.s[1], v3.s[0]
        add     w1, w1, #0x10
        fmov    s2, w2
        fmov    s3, w1
        lsr     w5, w5, #3
        mul     w0, w0, w7
        ushr    v2.2s, v2.2s, #5
        ushr    v3.2s, v3.2s, #5
        add     w0, w0, #0x10
        mul     w1, w5, w7
        mov     v0.s[2], v2.s[0]
        add     w1, w1, #0x10
        mov     v1.s[2], v3.s[0]
        fmov    s2, w0
        fmov    s3, w1
        ushr    v2.2s, v2.2s, #5
        ushr    v3.2s, v3.2s, #5
        mov     v0.s[3], v2.s[0]
        mov     v1.s[3], v3.s[0]
        uzp1    v0.8h, v0.8h, v1.8h
        str     q0, [x8], #16
        cmp     x9, x6
        b.ne    L2620
        ret

// mlkem_poly_decompress_d11 (0x14c bytes)
L2724:
        mov     x2, x1
        mov     x8, x0
        add     x9, x1, #0x160
        mov     w7, #0xd01
        nop
L2738:
        ldrb    w5, [x2, #8]
        add     x2, x2, #0xb
        ldurb   w11, [x2, #-4]
        ldurb   w6, [x2, #-5]
        lsl     w0, w5, #9
        ldurb   w12, [x2, #-6]
        orr     w11, w0, w11, lsl #1
        ldurb   w4, [x2, #-9]
        lsl     w1, w6, #4
        orr     w6, w11, w6, lsr #7
        ldurb   w10, [x2, #-10]
        and     w6, w6, #0x7ff
        orr     w1, w1, w12, lsr #4
        lsl     w13, w4, #5
        and     w1, w1, #0x7ff
        ldurh   w0, [x2, #-11]
        orr     w10, w13, w10, lsr #3
        mul     w6, w6, w7
        and     w10, w10, #0x7ff
        ldurb   w11, [x2, #-2]
        mul     w1, w1, w7
        add     w6, w6, #0x400
        fmov    s0, w6
        ldurb   w3, [x2, #-7]
        and     w0, w0, #0x7ff
        ldurb   w13, [x2, #-8]
        ushr    v2.2s, v0.2s, #11
        add     w1, w1, #0x400
        mul     w10, w10, w7
        fmov    s0, w1
        lsl     w14, w11, #6
        lsl     w15, w3, #10
        ushr    v1.2s, v0.2s, #11
        mul     w0, w0, w7
        orr     w5, w14, w5, lsr #2
        add     w10, w10, #0x400
        fmov    s0, w10
        orr     w13, w15, w13, lsl #2
        and     w5, w5, #0x7ff
        orr     w4, w13, w4, lsr #6
        ushr    v3.2s, v0.2s, #11
        add     w0, w0, #0x400
        fmov    s0, w0
        and     w4, w4, #0x7ff
        mul     w5, w5, w7
        lsl     w12, w12, #7
        ushr    v0.2s, v0.2s, #11
        orr     w3, w12, w3, lsr #1
        ldurb   w13, [x2, #-1]
        mul     w1, w4, w7
        mov     v1.s[1], v2.s[0]
        and     w0, w3, #0x7ff
        add     w3, w5, #0x400
        fmov    s2, w3
        mov     v0.s[1], v3.s[0]
        add     w1, w1, #0x400
        ushr    v3.2s, v2.2s, #11
        lsr     w11, w11, #5
        fmov    s2, w1
        orr     w4, w11, w13, lsl #3
        mul     w0, w0, w7
        ushr    v2.2s, v2.2s, #11
        mul     w4, w4, w7
        add     w0, w0, #0x400
        mov     v1.s[2], v3.s[0]
        add     w1, w4, #0x400
        fmov    s3, w1
        mov     v0.s[2], v2.s[0]
        fmov    s2, w0
        ushr    v3.2s, v3.2s, #11
        ushr    v2.2s, v2.2s, #11
        mov     v1.s[3], v3.s[0]
        mov     v0.s[3], v2.s[0]
        uzp1    v0.8h, v0.8h, v1.8h
        str     q0, [x8], #16
        cmp     x2, x9
        b.ne    L2738
        ret

// mlkem_poly_tobytes (0x234 bytes)
L2870:
        add     x4, x0, #0x180
        add     x2, x1, #0x200
        cmp     x1, x4
        ccmp    x0, x2, #0x2, cc
        b.cc    L2a64
        mov     x2, x1
        stp     x19, x30, [sp, #-16]!
        add     x19, x1, #0x40
        add     x30, x1, #0x60
        add     x16, x0, #0x60
        ld2     {v0.8h-v1.8h}, [x2], #32
        add     x13, x0, #0x90
        add     x10, x0, #0xc0
        add     x7, x0, #0xf0
        add     x4, x0, #0x120
        add     x18, x1, #0x80
        ld2     {v2.8h-v3.8h}, [x2]
        add     x2, x0, #0x150
        shrn    v16.8b, v1.8h, #4
        add     x17, x1, #0xa0
        add     x15, x1, #0xc0
        add     x14, x1, #0xe0
        uzp1    v7.16b, v1.16b, v3.16b
        add     x12, x1, #0x100
        uzp1    v4.16b, v0.16b, v2.16b
        add     x11, x1, #0x120
        uzp2    v0.16b, v0.16b, v2.16b
        add     x9, x1, #0x140
        add     x8, x1, #0x160
        add     x6, x1, #0x180
        shl     v1.16b, v7.16b, #4
        add     x5, x1, #0x1a0
        add     x3, x1, #0x1c0
        add     x1, x1, #0x1e0
        orr     v5.16b, v0.16b, v1.16b
        mov     v0.8b, v16.8b
        shrn2   v0.16b, v3.8h, #4
        mov     v6.16b, v0.16b
        st3     {v4.16b-v6.16b}, [x0], #48
        ld2     {v0.8h-v1.8h}, [x19]
        ld2     {v2.8h-v3.8h}, [x30]
        shrn    v16.8b, v1.8h, #4
        uzp1    v7.16b, v1.16b, v3.16b
        uzp1    v4.16b, v0.16b, v2.16b
        uzp2    v0.16b, v0.16b, v2.16b
        shl     v1.16b, v7.16b, #4
        orr     v5.16b, v0.16b, v1.16b
        mov     v0.8b, v16.8b
        shrn2   v0.16b, v3.8h, #4
        mov     v6.16b, v0.16b
        st3     {v4.16b-v6.16b}, [x0]
        ld2     {v0.8h-v1.8h}, [x18]
        ld2     {v2.8h-v3.8h}, [x17]
        shrn    v16.8b, v1.8h, #4
        uzp1    v7.16b, v1.16b, v3.16b
        uzp1    v4.16b, v0.16b, v2.16b
        uzp2    v0.16b, v0.16b, v2.16b
        shl     v1.16b, v7.16b, #4
        orr     v5.16b, v0.16b, v1.16b
        mov     v0.8b, v16.8b
        shrn2   v0.16b, v3.8h, #4
        mov     v6.16b, v0.16b
        st3     {v4.16b-v6.16b}, [x16]
        ld2     {v0.8h-v1.8h}, [x15]
        ld2     {v2.8h-v3.8h}, [x14]
        shrn    v16.8b, v1.8h, #4
        uzp1    v7.16b, v1.16b, v3.16b
        uzp1    v4.16b, v0.16b, v2.16b
        uzp2    v0.16b, v0.16b, v2.16b
        shl     v1.16b, v7.16b, #4
        orr     v5.16b, v0.16b, v1.16b
        mov     v0.8b, v16.8b
        shrn2   v0.16b, v3.8h, #4
        mov     v6.16b, v0.16b
        st3     {v4.16b-v6.16b}, [x13]
        ld2     {v0.8h-v1.8h}, [x12]
        ld2     {v2.8h-v3.8h}, [x11]
        shrn    v16.8b, v1.8h, #4
        uzp1    v7.16b, v1.16b, v3.16b
        uzp1    v4.16b, v0.16b, v2.16b
        uzp2    v0.16b, v0.16b, v2.16b
        shl     v1.16b, v7.16b, #4
        orr     v5.16b, v0.16b, v1.16b
        mov     v0.8b, v16.8b
        shrn2   v0.16b, v3.8h, #4
        mov     v6.16b, v0.16b
        st3     {v4.16b-v6.16b}, [x10]
        ld2     {v0.8h-v1.8h}, [x9]
        ld2     {v2.8h-v3.8h}, [x8]
        shrn    v16.8b, v1.8h, #4
        uzp1    v7.16b, v1.16b, v3.16b
        uzp1    v4.16b, v0.16b, v2.16b
        uzp2    v0.16b, v0.16b, v2.16b
        shl     v1.16b, v7.16b, #4
        orr     v5.16b, v0.16b, v1.16b
        mov     v0.8b, v16.8b
        shrn2   v0.16b, v3.8h, #4
        mov     v6.16b, v0.16b
        st3     {v4.16b-v6.16b}, [x7]
        ld2     {v0.8h-v1.8h}, [x6]
        ld2     {v2.8h-v3.8h}, [x5]
        shrn    v16.8b, v1.8h, #4
        uzp1    v7.16b, v1.16b, v3.16b
        uzp1    v4.16b, v0.16b, v2.16b
        uzp2    v0.16b, v0.16b, v2.16b
        shl     v1.16b, v7.16b, #4
        orr     v5.16b, v0.16b, v1.16b
        mov     v0.8b, v16.8b
        shrn2   v0.16b, v3.8h, #4
        mov     v6.16b, v0.16b
        st3     {v4.16b-v6.16b}, [x4]
        ld2     {v0.8h-v1.8h}, [x3]
        ld2     {v2.8h-v3.8h}, [x1]
        shrn    v16.8b, v1.8h, #4
        uzp1    v7.16b, v1.16b, v3.16b
        uzp1    v4.16b, v0.16b, v2.16b
        uzp2    v0.16b, v0.16b, v2.16b
        shl     v1.16b, v7.16b, #4
        orr     v5.16b, v0.16b, v1.16b
        mov     v0.8b, v16.8b
        shrn2   v0.16b, v3.8h, #4
        mov     v6.16b, v0.16b
        st3     {v4.16b-v6.16b}, [x2]
        ldp     x19, x30, [sp], #16
        ret
L2a64:
        mov     x3, x1
        mov     x1, x0
        nop
L2a70:
        ldrsh   w0, [x3]
        add     x1, x1, #0x3
        ldrh    w2, [x3, #2]
        add     x3, x3, #0x4
        sturb   w0, [x1, #-3]
        ubfx    x0, x0, #8, #8
        orr     w0, w0, w2, lsl #4
        lsr     w2, w2, #4
        sturb   w0, [x1, #-2]
        sturb   w2, [x1, #-1]
        cmp     x4, x1
        b.ne    L2a70
        ret

// mlkem_poly_frombytes (0x30c bytes)
L2aa4:
        add     x2, x0, #0x200
        add     x6, x1, #0x180
        cmp     x1, x2
        ccmp    x0, x6, #0x2, cc
        b.cc    L2d7c
        stp     x19, x20, [sp, #-32]!
        mov     x2, x1
        add     x20, x0, #0x40
        str     x30, [sp, #16]
        add     x19, x0, #0x60
        add     x18, x0, #0x80
        add     x17, x0, #0xa0
        ld3     {v1.16b-v3.16b}, [x2], #48
        add     x15, x0, #0xc0
        add     x14, x0, #0xe0
        add     x12, x0, #0x100
        add     x11, x0, #0x120
        add     x9, x0, #0x140
        shll    v17.8h, v2.8b, #8
        add     x8, x0, #0x160
        uxtl    v18.8h, v1.8b
        add     x6, x0, #0x180
        ushr    v6.16b, v2.16b, #4
        add     x5, x0, #0x1a0
        shll2   v0.8h, v2.16b, #8
        add     x4, x0, #0x1c0
        bic     v17.8h, #0xf0, lsl #8
        add     x3, x0, #0x1e0
        uxtl2   v16.8h, v1.16b
        add     x30, x1, #0x60
        add     x16, x1, #0x90
        add     x13, x1, #0xc0
        bic     v0.8h, #0xf0, lsl #8
        add     x10, x1, #0xf0
        orr     v4.16b, v17.16b, v18.16b
        add     x7, x1, #0x120
        uxtl    v18.8h, v6.8b
        add     x1, x1, #0x150
        ushll   v17.8h, v3.8b, #4
        uxtl2   v6.8h, v6.16b
        ushll2  v3.8h, v3.16b, #4
        orr     v0.16b, v0.16b, v16.16b
        orr     v5.16b, v18.16b, v17.16b
        orr     v1.16b, v6.16b, v3.16b
        st2     {v4.8h-v5.8h}, [x0], #32
        st2     {v0.8h-v1.8h}, [x0]
        ld3     {v1.16b-v3.16b}, [x2]
        shll    v17.8h, v2.8b, #8
        uxtl    v18.8h, v1.8b
        ushr    v6.16b, v2.16b, #4
        mov     v16.16b, v1.16b
        bic     v17.8h, #0xf0, lsl #8
        shll2   v0.8h, v2.16b, #8
        uxtl2   v7.8h, v16.16b
        orr     v4.16b, v17.16b, v18.16b
        uxtl    v18.8h, v6.8b
        ushll   v17.8h, v3.8b, #4
        uxtl2   v6.8h, v6.16b
        ushll2  v3.8h, v3.16b, #4
        bic     v0.8h, #0xf0, lsl #8
        orr     v5.16b, v18.16b, v17.16b
        orr     v1.16b, v6.16b, v3.16b
        orr     v0.16b, v0.16b, v7.16b
        st2     {v4.8h-v5.8h}, [x20]
        st2     {v0.8h-v1.8h}, [x19]
        ld3     {v1.16b-v3.16b}, [x30]
        ldr     x30, [sp, #16]
        shll    v17.8h, v2.8b, #8
        uxtl    v18.8h, v1.8b
        ushr    v6.16b, v2.16b, #4
        mov     v16.16b, v1.16b
        bic     v17.8h, #0xf0, lsl #8
        shll2   v0.8h, v2.16b, #8
        uxtl2   v7.8h, v16.16b
        orr     v4.16b, v17.16b, v18.16b
        uxtl    v18.8h, v6.8b
        ushll   v17.8h, v3.8b, #4
        uxtl2   v6.8h, v6.16b
        ushll2  v3.8h, v3.16b, #4
        bic     v0.8h, #0xf0, lsl #8
        orr     v5.16b, v18.16b, v17.16b
        orr     v1.16b, v6.16b, v3.16b
        orr     v0.16b, v0.16b, v7.16b
        st2     {v4.8h-v5.8h}, [x18]
        st2     {v0.8h-v1.8h}, [x17]
        ld3     {v1.16b-v3.16b}, [x16]
        shll    v17.8h, v2.8b, #8
        uxtl    v18.8h, v1.8b
        ushr    v6.16b, v2.16b, #4
        mov     v16.16b, v1.16b
        bic     v17.8h, #0xf0, lsl #8
        shll2   v0.8h, v2.16b, #8
        uxtl2   v7.8h, v16.16b
        orr     v4.16b, v17.16b, v18.16b
        uxtl    v18.8h, v6.8b
        ushll   v17.8h, v3.8b, #4
        uxtl2   v6.8h, v6.16b
        ushll2  v3.8h, v3.16b, #4
        bic     v0.8h, #0xf0, lsl #8
        orr     v5.16b, v18.16b, v17.16b
        orr     v1.16b, v6.16b, v3.16b
        orr     v0.16b, v0.16b, v7.16b
        st2     {v4.8h-v5.8h}, [x15]
        st2     {v0.8h-v1.8h}, [x14]
        ld3     {v1.16b-v3.16b}, [x13]
        shll    v17.8h, v2.8b, #8
        uxtl    v18.8h, v1.8b
        ushr    v6.16b, v2.16b, #4
        mov     v16.16b, v1.16b
        bic     v17.8h, #0xf0, lsl #8
        shll2   v0.8h, v2.16b, #8
        uxtl2   v7.8h, v16.16b
        orr     v4.16b, v17.16b, v18.16b
        uxtl    v18.8h, v6.8b
        ushll   v17.8h, v3.8b, #4
        uxtl2   v6.8h, v6.16b
        ushll2  v3.8h, v3.16b, #4
        bic     v0.8h, #0xf0, lsl #8
        orr     v5.16b, v18.16b, v17.16b
        orr     v1.16b, v6.16b, v3.16b
        orr     v0.16b, v0.16b, v7.16b
        st2     {v4.8h-v5.8h}, [x12]
        st2     {v0.8h-v1.8h}, [x11]
        ld3     {v1.16b-v3.16b}, [x10]
        shll    v17.8h, v2.8b, #8
        uxtl    v18.8h, v1.8b
        ushr    v6.16b, v2.16b, #4
        mov     v16.16b, v1.16b
        bic     v17.8h, #0xf0, lsl #8
        shll2   v0.8h, v2.16b, #8
        uxtl2   v7.8h, v16.16b
        orr     v4.16b, v17.16b, v18.16b
        uxtl    v18.8h, v6.8b
        ushll   v17.8h, v3.8b, #4
        uxtl2   v6.8h, v6.16b
        ushll2  v3.8h, v3.16b, #4
        bic     v0.8h, #0xf0, lsl #8
        orr     v5.16b, v18.16b, v17.16b
        orr     v1.16b, v6.16b, v3.16b
        orr     v0.16b, v0.16b, v7.16b
        st2     {v4.8h-v5.8h}, [x9]
        st2     {v0.8h-v1.8h}, [x8]
        ld3     {v1.16b-v3.16b}, [x7]
        shll    v17.8h, v2.8b, #8
        uxtl    v18.8h, v1.8b
        ushr    v6.16b, v2.16b, #4
        mov     v16.16b, v1.16b
        bic     v17.8h, #0xf0, lsl #8
        shll2   v0.8h, v2.16b, #8
        uxtl2   v7.8h, v16.16b
        orr     v4.16b, v17.16b, v18.16b
        uxtl    v18.8h, v6.8b
        ushll   v17.8h, v3.8b, #4
        uxtl2   v6.8h, v6.16b
        ushll2  v3.8h, v3.16b, #4
        bic     v0.8h, #0xf0, lsl #8
        orr     v5.16b, v18.16b, v17.16b
        orr     v1.16b, v6.16b, v3.16b
        orr     v0.16b, v0.16b, v7.16b
        st2     {v4.8h-v5.8h}, [x6]
        st2     {v0.8h-v1.8h}, [x5]
        ld3     {v1.16b-v3.16b}, [x1]
        shll    v17.8h, v2.8b, #8
        uxtl    v18.8h, v1.8b
        ushr    v6.16b, v2.16b, #4
        mov     v16.16b, v1.16b
        bic     v17.8h, #0xf0, lsl #8
        shll2   v0.8h, v2.16b, #8
        uxtl2   v7.8h, v16.16b
        orr     v4.16b, v17.16b, v18.16b
        uxtl    v18.8h, v6.8b
        ushll   v17.8h, v3.8b, #4
        uxtl2   v6.8h, v6.16b
        ushll2  v3.8h, v3.16b, #4
        bic     v0.8h, #0xf0, lsl #8
        orr     v5.16b, v18.16b, v17.16b
        orr     v1.16b, v6.16b, v3.16b
        orr     v0.16b, v0.16b, v7.16b
        st2     {v4.8h-v5.8h}, [x4]
        st2     {v0.8h-v1.8h}, [x3]
        ldp     x19, x20, [sp], #32
        ret
L2d7c:
        ldrb    w2, [x1, #1]
        add     x0, x0, #0x4
        ldrb    w4, [x1, #2]
        ldrb    w5, [x1], #3
        ubfiz   w3, w2, #8, #4
        lsl     w4, w4, #4
        orr     w3, w3, w5
        orr     w2, w4, w2, lsr #4
        sturh   w3, [x0, #-4]
        sturh   w2, [x0, #-2]
        cmp     x1, x6
        b.ne    L2d7c
        ret

// mlkem_poly_frommsg (0x120 bytes)
L2db0:
        mov     x2, x0
        mov     x3, x1
        add     x13, x0, #0x200
        mov     w12, #0x1
        mov     w4, #0x681
        mov     w11, #0x2
        mov     w10, #0x4
        mov     w9, #0x8
        mov     w8, #0x10
        mov     w7, #0x20
        mov     w6, #0x40
        mov     w5, #0xffffff80
L2de0:
        mov     w0, w12
        ldrb    w1, [x3]
        and     w0, w0, #0xff
        and     w0, w0, w1
        neg     w0, w0
        and     w1, w4, w0, asr #16
        mov     w0, w11
        strh    w1, [x2]
        ldrb    w1, [x3]
        and     w0, w0, #0xff
        and     w0, w0, w1
        neg     w0, w0
        and     w1, w4, w0, asr #16
        mov     w0, w10
        strh    w1, [x2, #2]
        ldrb    w1, [x3]
        and     w0, w0, #0xff
        and     w0, w0, w1
        neg     w0, w0
        and     w1, w4, w0, asr #16
        mov     w0, w9
        strh    w1, [x2, #4]
        ldrb    w1, [x3]
        and     w0, w0, #0xff
        and     w0, w0, w1
        neg     w0, w0
        and     w1, w4, w0, asr #16
        mov     w0, w8
        strh    w1, [x2, #6]
        ldrb    w1, [x3]
        and     w0, w0, #0xff
        and     w0, w0, w1
        neg     w0, w0
        and     w1, w4, w0, asr #16
        mov     w0, w7
        strh    w1, [x2, #8]
        ldrb    w1, [x3]
        and     w0, w0, #0xff
        and     w0, w0, w1
        neg     w0, w0
        and     w1, w4, w0, asr #16
        mov     w0, w6
        strh    w1, [x2, #10]
        ldrb    w1, [x3]
        and     w0, w0, #0xff
        and     w0, w0, w1
        neg     w0, w0
        and     w1, w4, w0, asr #16
        mov     w0, w5
        strh    w1, [x2, #12]
        ldrb    w1, [x3], #1
        and     w0, w0, #0xff
        and     w0, w0, w1
        neg     w0, w0
        and     w0, w4, w0, asr #16
        add     x2, x2, #0x10
        sturh   w0, [x2, #-2]
        cmp     x13, x2
        b.ne    L2de0
        ret

// mlkem_poly_tomsg (0x4a8 bytes)
L2ed0:
        mov     x2, x0
        mov     x0, x1
        add     x1, x2, #0x20
        add     x6, x0, #0x200
        cmp     x0, x1
        ccmp    x2, x6, #0x2, cc
        b.cc    L32b4
        .inst   0xd0000023  // adrp x3, 0x8000
        mov     x1, #0x0
        movi    v7.4s, #0x0
        stp     d8, d9, [sp, #-64]!
        ldr     q1, [x3, #2384]
        stp     d10, d11, [sp, #16]
        movi    v0.4s, #0x40, lsl #24
        stp     d12, d13, [sp, #32]
        stp     d14, d15, [sp, #48]
L2f10:
        str     q7, [x2, x1]
        ldp     q25, q19, [x0]
        ldp     q4, q11, [x0, #32]
        ldp     q20, q18, [x0, #64]
        ldp     q6, q16, [x0, #96]
        ldp     q23, q12, [x0, #128]
        ldp     q5, q10, [x0, #160]
        ldp     q3, q9, [x0, #192]
        ldp     q2, q8, [x0, #224]
        add     x0, x0, #0x100
        uzp2    v15.8h, v6.8h, v16.8h
        uzp2    v28.8h, v25.8h, v19.8h
        uzp2    v17.8h, v4.8h, v11.8h
        uzp2    v22.8h, v20.8h, v18.8h
        uzp2    v13.8h, v2.8h, v8.8h
        uzp2    v27.8h, v23.8h, v12.8h
        uzp2    v14.8h, v5.8h, v10.8h
        uzp2    v21.8h, v3.8h, v9.8h
        uzp1    v4.8h, v4.8h, v11.8h
        uzp1    v26.8h, v22.8h, v15.8h
        uzp1    v11.8h, v28.8h, v17.8h
        uzp1    v6.8h, v6.8h, v16.8h
        uzp1    v5.8h, v5.8h, v10.8h
        uzp1    v2.8h, v2.8h, v8.8h
        uzp1    v10.8h, v27.8h, v14.8h
        uzp1    v24.8h, v21.8h, v13.8h
        uzp1    v25.8h, v25.8h, v19.8h
        uzp1    v20.8h, v20.8h, v18.8h
        uzp1    v23.8h, v23.8h, v12.8h
        uzp1    v3.8h, v3.8h, v9.8h
        uzp1    v12.8h, v11.8h, v26.8h
        uzp1    v8.8h, v10.8h, v24.8h
        uzp1    v16.8h, v25.8h, v4.8h
        uzp1    v9.8h, v3.8h, v2.8h
        uzp2    v25.8h, v25.8h, v4.8h
        uzp2    v27.8h, v27.8h, v14.8h
        uzp1    v4.8h, v20.8h, v6.8h
        mov     v14.16b, v0.16b
        uzp2    v20.8h, v20.8h, v6.8h
        uzp1    v6.8h, v23.8h, v5.8h
        uzp2    v23.8h, v23.8h, v5.8h
        sxtl    v5.4s, v12.4h
        uzp2    v3.8h, v3.8h, v2.8h
        uzp2    v28.8h, v28.8h, v17.8h
        sxtl2   v2.4s, v8.8h
        sxtl    v17.4s, v8.4h
        mla     v14.4s, v5.4s, v1.4s
        uzp1    v8.8h, v6.8h, v9.8h
        mov     v5.16b, v0.16b
        uzp2    v6.8h, v6.8h, v9.8h
        mov     v9.16b, v0.16b
        uzp1    v31.8h, v25.8h, v20.8h
        mla     v5.4s, v2.4s, v1.4s
        sxtl    v2.4s, v8.4h
        uzp2    v21.8h, v21.8h, v13.8h
        sxtl2   v8.4s, v8.8h
        mov     v13.16b, v0.16b
        mla     v9.4s, v2.4s, v1.4s
        mov     v2.16b, v0.16b
        uzp1    v29.8h, v16.8h, v4.8h
        mla     v13.4s, v17.4s, v1.4s
        sxtl    v17.4s, v31.4h
        mla     v2.4s, v8.4s, v1.4s
        mov     v8.16b, v0.16b
        uzp2    v22.8h, v22.8h, v15.8h
        sxtl2   v12.4s, v12.8h
        uzp1    v15.8h, v23.8h, v3.8h
        sxtl2   v31.4s, v31.8h
        mla     v8.4s, v17.4s, v1.4s
        mov     v19.16b, v0.16b
        mov     v17.16b, v0.16b
        sxtl    v18.4s, v29.4h
        uzp2    v16.8h, v16.8h, v4.8h
        mla     v19.4s, v12.4s, v1.4s
        sxtl    v4.4s, v15.4h
        mla     v17.4s, v31.4s, v1.4s
        mov     v12.16b, v0.16b
        mov     v31.16b, v0.16b
        sxtl2   v29.4s, v29.8h
        ushr    v13.4s, v13.4s, #31
        sxtl2   v15.4s, v15.8h
        mla     v12.4s, v18.4s, v1.4s
        uzp1    v30.8h, v28.8h, v22.8h
        mla     v31.4s, v4.4s, v1.4s
        ushr    v5.4s, v5.4s, #31
        mov     v18.16b, v0.16b
        mov     v4.16b, v0.16b
        uzp2    v26.8h, v11.8h, v26.8h
        ushr    v14.4s, v14.4s, #31
        sxtl    v11.4s, v30.4h
        mla     v18.4s, v29.4s, v1.4s
        mla     v4.4s, v15.4s, v1.4s
        uzp1    v29.8h, v27.8h, v21.8h
        uzp1    v5.8h, v13.8h, v5.8h
        ushr    v19.4s, v19.4s, #31
        mov     v13.16b, v0.16b
        uzp2    v24.8h, v10.8h, v24.8h
        ushr    v9.4s, v9.4s, #31
        uzp1    v19.8h, v14.8h, v19.8h
        sxtl    v10.4s, v29.4h
        ushr    v8.4s, v8.4s, #31
        ushr    v17.4s, v17.4s, #31
        mla     v13.4s, v11.4s, v1.4s
        sxtl2   v30.4s, v30.8h
        ushr    v2.4s, v2.4s, #31
        ushr    v31.4s, v31.4s, #31
        ushr    v4.4s, v4.4s, #31
        mov     v11.16b, v0.16b
        mov     v14.16b, v0.16b
        sxtl    v15.4s, v16.4h
        uzp1    v5.16b, v19.16b, v5.16b
        uzp2    v3.8h, v23.8h, v3.8h
        sxtl    v19.4s, v6.4h
        ushr    v12.4s, v12.4s, #31
        mla     v14.4s, v10.4s, v1.4s
        uzp1    v2.8h, v9.8h, v2.8h
        sxtl2   v29.4s, v29.8h
        uzp1    v9.8h, v8.8h, v17.8h
        ushr    v18.4s, v18.4s, #31
        mla     v11.4s, v30.4s, v1.4s
        mov     v10.16b, v0.16b
        uzp1    v4.8h, v31.8h, v4.8h
        mov     v23.16b, v0.16b
        mov     v8.16b, v0.16b
        uzp1    v18.8h, v12.8h, v18.8h
        uzp2    v20.8h, v25.8h, v20.8h
        uzp1    v4.16b, v9.16b, v4.16b
        mla     v8.4s, v19.4s, v1.4s
        sxtl2   v16.4s, v16.8h
        sxtl    v19.4s, v26.4h
        sxtl2   v6.4s, v6.8h
        ushr    v13.4s, v13.4s, #31
        mla     v23.4s, v15.4s, v1.4s
        shl     v25.16b, v5.16b, #1
        mla     v10.4s, v29.4s, v1.4s
        ushr    v11.4s, v11.4s, #31
        mov     v17.16b, v0.16b
        mov     v15.16b, v0.16b
        sxtl2   v26.4s, v26.8h
        mov     v5.16b, v0.16b
        mov     v9.16b, v0.16b
        uzp1    v11.8h, v13.8h, v11.8h
        ushr    v14.4s, v14.4s, #31
        mla     v17.4s, v16.4s, v1.4s
        mla     v15.4s, v6.4s, v1.4s
        sxtl    v16.4s, v24.4h
        uzp1    v2.16b, v18.16b, v2.16b
        ushr    v13.4s, v8.4s, #31
        mla     v5.4s, v19.4s, v1.4s
        ushr    v10.4s, v10.4s, #31
        sxtl2   v24.4s, v24.8h
        mla     v9.4s, v26.4s, v1.4s
        mov     v18.16b, v0.16b
        mov     v8.16b, v0.16b
        uzp1    v10.8h, v14.8h, v10.8h
        uzp2    v6.8h, v28.8h, v22.8h
        ushr    v15.4s, v15.4s, #31
        mla     v18.4s, v16.4s, v1.4s
        shl     v19.16b, v4.16b, #2
        sxtl    v16.4s, v20.4h
        ushr    v9.4s, v9.4s, #31
        mla     v8.4s, v24.4s, v1.4s
        ushr    v5.4s, v5.4s, #31
        mov     v4.16b, v0.16b
        sxtl    v14.4s, v3.4h
        uzp1    v12.16b, v11.16b, v10.16b
        uzp2    v21.8h, v27.8h, v21.8h
        sxtl2   v3.4s, v3.8h
        uzp1    v13.8h, v13.8h, v15.8h
        ushr    v8.4s, v8.4s, #31
        mla     v4.4s, v16.4s, v1.4s
        sxtl    v15.4s, v6.4h
        uzp1    v5.8h, v5.8h, v9.8h
        sxtl2   v6.4s, v6.8h
        ushr    v23.4s, v23.4s, #31
        ushr    v17.4s, v17.4s, #31
        sxtl2   v20.4s, v20.8h
        ushr    v18.4s, v18.4s, #31
        mov     v11.16b, v0.16b
        mov     v16.16b, v0.16b
        mov     v10.16b, v0.16b
        mov     v9.16b, v0.16b
        uzp1    v18.8h, v18.8h, v8.8h
        mla     v16.4s, v14.4s, v1.4s
        mla     v10.4s, v3.4s, v1.4s
        sxtl    v14.4s, v21.4h
        mla     v9.4s, v6.4s, v1.4s
        orr     v2.16b, v25.16b, v2.16b
        uzp1    v17.8h, v23.8h, v17.8h
        mla     v11.4s, v20.4s, v1.4s
        sxtl2   v21.4s, v21.8h
        mov     v3.16b, v0.16b
        mov     v6.16b, v0.16b
        mov     v8.16b, v0.16b
        orr     v2.16b, v2.16b, v19.16b
        shl     v12.16b, v12.16b, #3
        uzp1    v17.16b, v17.16b, v13.16b
        ushr    v4.4s, v4.4s, #31
        ushr    v11.4s, v11.4s, #31
        ushr    v16.4s, v16.4s, #31
        ushr    v10.4s, v10.4s, #31
        mla     v3.4s, v15.4s, v1.4s
        mla     v6.4s, v14.4s, v1.4s
        mla     v8.4s, v21.4s, v1.4s
        orr     v2.16b, v2.16b, v12.16b
        shl     v17.16b, v17.16b, #4
        uzp1    v5.16b, v5.16b, v18.16b
        uzp1    v4.8h, v4.8h, v11.8h
        uzp1    v16.8h, v16.8h, v10.8h
        ushr    v3.4s, v3.4s, #31
        ushr    v9.4s, v9.4s, #31
        ushr    v6.4s, v6.4s, #31
        ushr    v8.4s, v8.4s, #31
        orr     v2.16b, v2.16b, v17.16b
        shl     v5.16b, v5.16b, #5
        uzp1    v4.16b, v4.16b, v16.16b
        uzp1    v3.8h, v3.8h, v9.8h
        uzp1    v6.8h, v6.8h, v8.8h
        orr     v2.16b, v2.16b, v5.16b
        shl     v4.16b, v4.16b, #6
        uzp1    v3.16b, v3.16b, v6.16b
        orr     v2.16b, v2.16b, v4.16b
        shl     v3.16b, v3.16b, #7
        orr     v2.16b, v2.16b, v3.16b
        str     q2, [x2, x1]
        cbnz    x1, L32a0
        mov     x1, #0x10
        b       L2f10
L32a0:
        ldp     d10, d11, [sp, #16]
        ldp     d12, d13, [sp, #32]
        ldp     d14, d15, [sp, #48]
        ldp     d8, d9, [sp], #64
        ret
L32b4:
        mov     w5, #0xafb8
        mov     x1, x2
        movk    w5, #0x13, lsl #16
        mov     w4, #0x40000000
        nop
L32c8:
        strb    wzr, [x1]
        add     x0, x0, #0x10
        ldursh  w2, [x0, #-16]
        madd    w2, w2, w5, w4
        lsr     w2, w2, #31
        strb    w2, [x1]
        ldursh  w3, [x0, #-14]
        madd    w3, w3, w5, w4
        lsr     w3, w3, #31
        orr     w3, w2, w3, lsl #1
        strb    w3, [x1]
        ldursh  w2, [x0, #-12]
        madd    w2, w2, w5, w4
        lsr     w2, w2, #31
        orr     w2, w3, w2, lsl #2
        strb    w2, [x1]
        ldursh  w3, [x0, #-10]
        madd    w3, w3, w5, w4
        lsr     w3, w3, #31
        orr     w3, w2, w3, lsl #3
        strb    w3, [x1]
        ldursh  w2, [x0, #-8]
        madd    w2, w2, w5, w4
        lsr     w2, w2, #31
        orr     w2, w3, w2, lsl #4
        strb    w2, [x1]
        ldursh  w3, [x0, #-6]
        madd    w3, w3, w5, w4
        lsr     w3, w3, #31
        orr     w3, w2, w3, lsl #5
        strb    w3, [x1]
        ldursh  w2, [x0, #-4]
        madd    w2, w2, w5, w4
        lsr     w2, w2, #31
        orr     w2, w3, w2, lsl #6
        strb    w2, [x1]
        ldursh  w3, [x0, #-2]
        madd    w3, w3, w5, w4
        lsr     w3, w3, #31
        orr     w2, w2, w3, lsl #7
        strb    w2, [x1], #1
        cmp     x0, x6
        b.ne    L32c8
        ret
        nop
        nop

// mlk_keccak_absorb_once.constprop.1 (0x10c bytes)
L3380:
        movi    v0.4s, #0x0
        stp     x19, x20, [sp, #-64]!
        mov     x19, x0
        stp     x21, x22, [sp, #16]
        mov     x20, x2
        mov     x21, x1
        str     x30, [sp, #32]
        strb    w3, [sp, #63]
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        stp     q0, q0, [x0, #64]
        stp     q0, q0, [x0, #96]
        stp     q0, q0, [x0, #128]
        stp     q0, q0, [x0, #160]
        str     xzr, [x0, #192]
        cmp     x2, #0x87
        b.ls    L33f4
        nop
L33c8:
        mov     x1, x21
        mov     w3, #0x88
        mov     w2, #0x0
        mov     x0, x19
        bl      L4000
        sub     x20, x20, #0x88
        mov     x0, x19
        bl      L42a0
        add     x21, x21, #0x88
        cmp     x20, #0x87
        b.hi    L33c8
L33f4:
        mov     w22, w20
        cbnz    x20, L3440
L33fc:
        add     x20, sp, #0x3f
        mov     w2, w22
        mov     x1, x20
        mov     x0, x19
        mov     w3, #0x1
        bl      L4000
        mov     w4, #0xffffff80
        mov     x1, x20
        mov     x0, x19
        mov     w3, #0x1
        mov     w2, #0x87
        strb    w4, [sp, #63]
        bl      L4000
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #64
        ret
L3440:
        mov     x1, x21
        mov     w3, w20
        mov     x0, x19
        mov     w2, #0x0
        bl      L4000
        cmp     x20, #0x87
        b.ne    L33fc
        ldrb    w4, [sp, #63]
        mov     w2, w20
        mov     x0, x19
        add     x1, sp, #0x3f
        orr     w4, w4, #0xffffff80
        mov     w3, #0x1
        strb    w4, [sp, #63]
        bl      L4000
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #64
        ret
        nop

// mlkem_shake128_absorb_once (0x138 bytes)
L3490:
        movi    v0.4s, #0x0
        stp     x19, x20, [sp, #-64]!
        mov     x19, x0
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        stp     x21, x22, [sp, #16]
        mov     x20, x2
        str     x30, [sp, #32]
        mov     w2, #0x1f
        mov     x21, x1
        ldr     x3, [x0]
        str     x3, [sp, #56]
        mov     x3, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        strb    w2, [sp, #55]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        str     xzr, [x19, #192]
        cmp     x20, #0xa7
        b.ls    L351c
        nop
L34f0:
        mov     x1, x21
        mov     w3, #0xa8
        mov     w2, #0x0
        mov     x0, x19
        bl      L4000
        sub     x20, x20, #0xa8
        mov     x0, x19
        bl      L42a0
        add     x21, x21, #0xa8
        cmp     x20, #0xa7
        b.hi    L34f0
L351c:
        mov     w22, w20
        cbnz    x20, L3584
L3524:
        add     x20, sp, #0x37
        mov     w2, w22
        mov     x1, x20
        mov     x0, x19
        mov     w3, #0x1
        bl      L4000
        mov     w4, #0xffffff80
        mov     x1, x20
        mov     x0, x19
        mov     w3, #0x1
        mov     w2, #0xa7
        strb    w4, [sp, #55]
        bl      L4000
L3558:
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #56]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L35c4
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #64
        ret
L3584:
        mov     x1, x21
        mov     w3, w20
        mov     x0, x19
        mov     w2, #0x0
        bl      L4000
        cmp     x20, #0xa7
        b.ne    L3524
        ldrb    w4, [sp, #55]
        mov     w2, w20
        mov     x0, x19
        add     x1, sp, #0x37
        orr     w4, w4, #0xffffff80
        mov     w3, #0x1
        strb    w4, [sp, #55]
        bl      L4000
        b       L3558
L35c4:
        bl      L0830
        nop
        nop

// mlkem_shake128_squeezeblocks (0x50 bytes)
L35d0:
        cbz     x1, L361c
        stp     x19, x20, [sp, #-32]!
        mov     x20, x0
        mov     x19, x1
        stp     x21, x30, [sp, #16]
        mov     x21, x2
L35e8:
        mov     x0, x21
        bl      L42a0
        mov     x1, x20
        mov     x0, x21
        mov     w3, #0xa8
        mov     w2, #0x0
        bl      L3ec0
        add     x20, x20, #0xa8
        subs    x19, x19, #0x1
        b.ne    L35e8
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
L361c:
        ret

// mlkem_shake128_init (0x4 bytes)
L3620:
        ret

// mlkem_shake128_release (0x24 bytes)
L3624:
        movi    v0.4s, #0x0
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        stp     q0, q0, [x0, #64]
        stp     q0, q0, [x0, #96]
        stp     q0, q0, [x0, #128]
        stp     q0, q0, [x0, #160]
        stp     q0, q0, [x0, #192]
        ret
        nop
        nop

// mlkem_shake256 (0xd8 bytes)
L3650:
        stp     x19, x20, [sp, #-304]!
        mov     x19, x1
        mov     x1, x2
        .inst   0x900000e4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        stp     x21, x22, [sp, #16]
        add     x21, sp, #0x4f
        str     x30, [sp, #40]
        and     x21, x21, #0xffffffffffffffe0
        mov     x2, x3
        mov     x22, x0
        ldr     x3, [x4]
        str     x3, [sp, #296]
        mov     x3, #0x0
        mov     x0, x21
        mov     w3, #0x1f
        bl      L3380
        cbz     x19, L36d4
        str     x23, [sp, #32]
        mov     x23, #0x88
L36a0:
        mov     x0, x21
        bl      L42a0
        cmp     x19, #0x88
        mov     x1, x22
        csel    x20, x19, x23, ls
        mov     x0, x21
        mov     w3, w20
        mov     w2, #0x0
        bl      L3ec0
        add     x22, x22, x20
        subs    x19, x19, x20
        b.ne    L36a0
        ldr     x23, [sp, #32]
L36d4:
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x21, #64]
        stp     q0, q0, [x21, #96]
        stp     q0, q0, [x21, #128]
        stp     q0, q0, [x21, #160]
        stp     q0, q0, [x21, #192]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3720
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #40]
        ldp     x19, x20, [sp], #304
        ret
L3720:
        str     x23, [sp, #32]
        bl      L0830
        nop
        nop

// mlkem_sha3_256 (0x98 bytes)
L3730:
        stp     x19, x20, [sp, #-240]!
        mov     w3, #0x6
        mov     x20, x0
        .inst   0x900000e4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x20
        ldr     x0, [x4]
        str     x0, [sp, #232]
        mov     x0, #0x0
        mov     x0, x19
        bl      L3380
        mov     x0, x19
        bl      L42a0
        mov     x1, x20
        mov     x0, x19
        mov     w3, #0x20
        mov     w2, #0x0
        bl      L3ec0
        str     xzr, [x19, #192]
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L37c4
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #240
        ret
L37c4:
        bl      L0830
        nop
        nop

// mlkem_sha3_512 (0x174 bytes)
L37d0:
        movi    v0.4s, #0x0
        stp     x19, x20, [sp, #-272]!
        mov     x20, x2
        .inst   0x900000e3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        add     x19, sp, #0x40
        stp     x21, x22, [sp, #16]
        mov     x22, x0
        mov     x21, x1
        stp     x23, x30, [sp, #32]
        ldr     x2, [x3]
        str     x2, [sp, #264]
        mov     x2, #0x0
        stp     q0, q0, [x19]
        mov     w2, #0x6
        stp     q0, q0, [x19, #32]
        strb    w2, [sp, #63]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        str     xzr, [x19, #192]
        cmp     x20, #0x47
        b.ls    L385c
L3830:
        mov     x1, x21
        mov     w3, #0x48
        mov     w2, #0x0
        mov     x0, x19
        bl      L4000
        sub     x20, x20, #0x48
        mov     x0, x19
        bl      L42a0
        add     x21, x21, #0x48
        cmp     x20, #0x47
        b.hi    L3830
L385c:
        mov     w23, w20
        cbnz    x20, L3900
L3864:
        add     x20, sp, #0x3f
        mov     w2, w23
        mov     x1, x20
        mov     x0, x19
        mov     w3, #0x1
        bl      L4000
        mov     w4, #0xffffff80
        mov     x1, x20
        mov     x0, x19
        mov     w3, #0x1
        mov     w2, #0x47
        strb    w4, [sp, #63]
        bl      L4000
L3898:
        mov     x0, x19
        bl      L42a0
        mov     x1, x22
        mov     x0, x19
        mov     w3, #0x40
        mov     w2, #0x0
        bl      L3ec0
        str     xzr, [x19, #192]
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #264]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3940
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #272
        ret
L3900:
        mov     x1, x21
        mov     w3, w20
        mov     x0, x19
        mov     w2, #0x0
        bl      L4000
        cmp     x20, #0x47
        b.ne    L3864
        ldrb    w4, [sp, #63]
        mov     w2, w20
        add     x1, sp, #0x3f
        mov     x0, x19
        orr     w4, w4, #0xffffff80
        mov     w3, #0x1
        strb    w4, [sp, #63]
        bl      L4000
        b       L3898
L3940:
        bl      L0830
        nop
        nop
        nop

// mlkem_shake128x4_absorb_once (0x17c bytes)
L3950:
        stp     x19, x20, [sp, #-80]!
        mov     x20, x1
        mov     x19, x5
        .inst   0x900000e6  // adrp x6, 0x1f000
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
        bl      L0840
        mov     w0, #0x1f
        strb    w0, [sp, #71]
        cmp     x19, #0xa7
        b.ls    L39ec
        nop
L39a8:
        mov     x4, x23
        mov     x3, x22
        mov     x2, x21
        mov     x1, x20
        mov     w6, #0xa8
        mov     w5, #0x0
        mov     x0, x24
        bl      L4220
        mov     x0, x24
        sub     x19, x19, #0xa8
        bl      L4870
        add     x23, x23, #0xa8
        add     x22, x22, #0xa8
        add     x21, x21, #0xa8
        add     x20, x20, #0xa8
        cmp     x19, #0xa7
        b.hi    L39a8
L39ec:
        mov     w25, w19
        cbnz    x19, L3a70
L39f4:
        add     x19, sp, #0x47
        mov     w5, w25
        mov     x4, x19
        mov     x3, x19
        mov     x2, x19
        mov     x1, x19
        mov     x0, x24
        mov     w6, #0x1
        bl      L4220
        mov     w7, #0xffffff80
        mov     x0, x24
        mov     x4, x19
        mov     x3, x19
        mov     x2, x19
        mov     x1, x19
        mov     w6, #0x1
        mov     w5, #0xa7
        strb    w7, [sp, #71]
        bl      L4220
L3a40:
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #72]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3ac8
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #80
        ret
L3a70:
        mov     x4, x23
        mov     x3, x22
        mov     x2, x21
        mov     x1, x20
        mov     w6, w19
        mov     x0, x24
        mov     w5, #0x0
        bl      L4220
        cmp     x19, #0xa7
        b.ne    L39f4
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
        bl      L4220
        b       L3a40
L3ac8:
        bl      L0830
        nop

// mlkem_shake128x4_squeezeblocks (0x88 bytes)
L3ad0:
        cbz     x4, L3b54
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
L3b00:
        mov     x0, x24
        bl      L4870
        mov     x4, x19
        mov     x3, x20
        mov     x2, x21
        mov     x1, x22
        mov     x0, x24
        mov     w6, #0xa8
        mov     w5, #0x0
        bl      L41a0
        add     x19, x19, #0xa8
        add     x20, x20, #0xa8
        add     x21, x21, #0xa8
        add     x22, x22, #0xa8
        subs    x23, x23, #0x1
        b.ne    L3b00
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L3b54:
        ret
        nop
        nop

// mlkem_shake128x4_init (0x4 bytes)
L3b60:
        ret

// mlkem_shake128x4_release (0x1c bytes)
L3b64:
        stp     x19, x30, [sp, #-16]!
        mov     x2, #0x320
        mov     x19, x0
        mov     w1, #0x0
        bl      L0840
        ldp     x19, x30, [sp], #16
        ret

// mlkem_shake256x4 (0x334 bytes)
L3b80:
        sub     sp, sp, #0x5f0
        .inst   0x900000e8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        stp     x27, x28, [sp, #64]
        mov     x27, #0xf0f0f0f0f0f0f0f0
        movk    x27, #0xf0f1
        str     x4, [sp, #104]
        mov     x28, x6
        umulh   x4, x4, x27
        stp     x19, x20, [sp]
        add     x20, sp, #0xaf
        stp     x21, x22, [sp, #16]
        and     x20, x20, #0xffffffffffffffe0
        mov     x22, x3
        stp     x23, x24, [sp, #32]
        mov     x21, x5
        mov     x24, x1
        stp     x25, x26, [sp, #48]
        mov     x25, x0
        lsr     x0, x4, #7
        str     x30, [sp, #80]
        mov     x23, x2
        str     x0, [sp, #112]
        mov     x27, x7
        ldr     x19, [sp, #1528]
        mov     x0, x20
        ldr     x26, [sp, #1520]
        ldr     x1, [x8]
        str     x1, [sp, #1512]
        mov     x1, #0x0
        mov     x2, #0x320
        bl      L0840
        mov     w0, #0x1f
        strb    w0, [sp, #143]
        cmp     x19, #0x87
        b.ls    L3c54
L3c10:
        mov     x4, x26
        mov     x3, x27
        mov     x2, x28
        mov     x1, x21
        mov     w6, #0x88
        mov     w5, #0x0
        mov     x0, x20
        bl      L4220
        mov     x0, x20
        sub     x19, x19, #0x88
        bl      L4870
        add     x26, x26, #0x88
        add     x27, x27, #0x88
        add     x28, x28, #0x88
        add     x21, x21, #0x88
        cmp     x19, #0x87
        b.hi    L3c10
L3c54:
        mov     w7, w19
        cbnz    x19, L3dbc
L3c5c:
        add     x19, sp, #0x8f
        mov     w5, w7
        mov     x4, x19
        mov     x3, x19
        mov     x2, x19
        mov     x1, x19
        mov     x0, x20
        mov     w6, #0x1
        bl      L4220
        mov     w7, #0xffffff80
        mov     x4, x19
        mov     x3, x19
        mov     x2, x19
        mov     x1, x19
        mov     x0, x20
        mov     w6, #0x1
        mov     w5, #0x87
        strb    w7, [sp, #143]
        bl      L4220
L3ca8:
        ldp     x0, x21, [sp, #104]
        mov     x19, #0x0
        cmp     x0, #0x87
        b.ls    L3cec
L3cb8:
        mov     x0, x20
        bl      L4870
        add     x4, x22, x19
        add     x3, x23, x19
        add     x2, x24, x19
        add     x1, x25, x19
        mov     x0, x20
        mov     w6, #0x88
        mov     w5, #0x0
        bl      L41a0
        add     x19, x19, #0x88
        subs    x21, x21, #0x1
        b.ne    L3cb8
L3cec:
        ldr     x0, [sp, #104]
        mov     x19, #0xf0f0f0f0f0f0f0f0
        movk    x19, #0xf0f1
        umulh   x19, x0, x19
        lsr     x19, x19, #7
        add     x19, x19, x19, lsl #4
        subs    x19, x0, x19, lsl #3
        b.ne    L3e1c
        add     x21, sp, #0x560
        add     x26, sp, #0x4d8
        add     x28, sp, #0x450
        add     x27, sp, #0x3c8
L3d1c:
        mov     x0, x20
        mov     x2, #0x320
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        str     xzr, [x27, #128]
        stp     q0, q0, [x27]
        stp     q0, q0, [x27, #32]
        stp     q0, q0, [x27, #64]
        stp     q0, q0, [x27, #96]
        stp     q0, q0, [x28]
        stp     q0, q0, [x28, #32]
        stp     q0, q0, [x28, #64]
        stp     q0, q0, [x28, #96]
        str     xzr, [x28, #128]
        stp     q0, q0, [x26]
        stp     q0, q0, [x26, #32]
        stp     q0, q0, [x26, #64]
        stp     q0, q0, [x26, #96]
        str     xzr, [x26, #128]
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x21, #64]
        stp     q0, q0, [x21, #96]
        str     xzr, [x21, #128]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1512]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3eb0
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x5f0
        ret
L3dbc:
        mov     x4, x26
        mov     x3, x27
        mov     x2, x28
        mov     x1, x21
        mov     w6, w19
        mov     x0, x20
        mov     w5, #0x0
        str     w19, [sp, #124]
        bl      L4220
        ldr     w7, [sp, #124]
        cmp     x19, #0x87
        b.ne    L3c5c
        ldrb    w7, [sp, #143]
        add     x4, sp, #0x8f
        mov     w5, w19
        mov     x3, x4
        orr     w7, w7, #0xffffff80
        mov     x2, x4
        mov     x1, x4
        mov     x0, x20
        mov     w6, #0x1
        strb    w7, [sp, #143]
        bl      L4220
        b       L3ca8
L3e1c:
        ldr     x0, [sp, #112]
        add     x21, sp, #0x560
        add     x26, sp, #0x4d8
        add     x28, sp, #0x450
        add     x27, x0, x0, lsl #4
        mov     x0, x20
        lsl     x1, x27, #3
        add     x27, sp, #0x3c8
        str     x1, [sp, #104]
        bl      L4870
        mov     x4, x21
        mov     x3, x26
        mov     w6, #0x88
        mov     w5, #0x0
        mov     x2, x28
        mov     x1, x27
        mov     x0, x20
        bl      L41a0
        ldr     x0, [sp, #104]
        mov     x2, x19
        mov     x1, x27
        add     x0, x25, x0
        bl      L0810
        ldr     x25, [sp, #104]
        mov     x2, x19
        mov     x1, x28
        add     x0, x24, x25
        bl      L0810
        mov     x2, x19
        mov     x1, x26
        add     x0, x23, x25
        bl      L0810
        mov     x2, x19
        mov     x1, x21
        add     x0, x22, x25
        bl      L0810
        b       L3d1c
L3eb0:
        bl      L0830
        nop
        nop
        nop

// mlkem_keccakf1600_extract_bytes (0x140 bytes)
L3ec0:
        mov     w2, w2
        cbz     w3, L3f0c
        sub     w5, w3, #0x1
        cmp     w5, #0x6
        b.ls    L3ee8
        add     x4, x2, #0x1
        add     x4, x0, x4
        sub     x4, x1, x4
        cmp     x4, #0xe
        b.hi    L3f10
L3ee8:
        mov     w3, w3
        add     x2, x0, x2
        mov     x0, #0x0
        nop
L3ef8:
        ldrb    w4, [x2, x0]
        strb    w4, [x1, x0]
        add     x0, x0, #0x1
        cmp     x0, x3
        b.ne    L3ef8
L3f0c:
        ret
L3f10:
        add     x2, x0, x2
        cmp     w5, #0xe
        b.ls    L3ff4
        and     x4, x3, #0xfffffff0
        mov     x0, #0x0
        nop
L3f28:
        ldr     q0, [x2, x0]
        str     q0, [x1, x0]
        add     x0, x0, #0x10
        cmp     x0, x4
        b.ne    L3f28
        and     w0, w3, #0xfffffff0
        tst     x3, #0xf
        b.eq    L3f0c
        sub     w4, w3, w0
        sub     w5, w4, #0x1
        cmp     w5, #0x6
        b.ls    L3f70
L3f58:
        ldr     d0, [x2, w0, uxtw]
        and     w5, w4, #0xfffffff8
        str     d0, [x1, w0, uxtw]
        add     w0, w0, w5
        tst     x4, #0x7
        b.eq    L3f0c
L3f70:
        ldrb    w5, [x2, w0, uxtw]
        add     w4, w0, #0x1
        strb    w5, [x1, w0, uxtw]
        cmp     w3, w4
        b.ls    L3f0c
        ldrb    w6, [x2, w4, uxtw]
        add     w5, w0, #0x2
        strb    w6, [x1, w4, uxtw]
        cmp     w3, w5
        b.ls    L3f0c
        ldrb    w6, [x2, w5, uxtw]
        add     w4, w0, #0x3
        strb    w6, [x1, w5, uxtw]
        cmp     w3, w4
        b.ls    L3f0c
        ldrb    w6, [x2, w4, uxtw]
        add     w5, w0, #0x4
        strb    w6, [x1, w4, uxtw]
        cmp     w3, w5
        b.ls    L3f0c
        ldrb    w6, [x2, w5, uxtw]
        add     w4, w0, #0x5
        strb    w6, [x1, w5, uxtw]
        cmp     w3, w4
        b.ls    L3f0c
        ldrb    w5, [x2, w4, uxtw]
        add     w0, w0, #0x6
        strb    w5, [x1, w4, uxtw]
        cmp     w3, w0
        b.ls    L3f0c
        ldrb    w2, [x2, w0, uxtw]
        strb    w2, [x1, w0, uxtw]
        ret
L3ff4:
        mov     w4, w3
        mov     w0, #0x0
        b       L3f58

// mlkem_keccakf1600_xor_bytes (0x1a0 bytes)
L4000:
        mov     w2, w2
        cbz     w3, L404c
        sub     w6, w3, #0x1
        add     x4, x0, x2
        cmp     w6, #0x6
        b.ls    L4028
        add     x5, x1, #0x1
        sub     x5, x4, x5
        cmp     x5, #0xe
        b.hi    L4050
L4028:
        mov     w3, w3
        mov     x0, #0x0
L4030:
        ldrb    w2, [x4, x0]
        ldrb    w5, [x1, x0]
        eor     w2, w2, w5
        strb    w2, [x4, x0]
        add     x0, x0, #0x1
        cmp     x0, x3
        b.ne    L4030
L404c:
        ret
L4050:
        cmp     w6, #0xe
        b.ls    L4194
        and     x6, x3, #0xfffffff0
        mov     x5, #0x0
L4060:
        ldr     q0, [x4, x5]
        ldr     q1, [x1, x5]
        eor     v0.16b, v0.16b, v1.16b
        str     q0, [x4, x5]
        add     x5, x5, #0x10
        cmp     x5, x6
        b.ne    L4060
        and     w4, w3, #0xfffffff0
        tst     x3, #0xf
        b.eq    L404c
        sub     w5, w3, w4
        sub     w6, w5, #0x1
        cmp     w6, #0x6
        b.ls    L40bc
L4098:
        add     x6, x2, w4, uxtw
        ldr     d0, [x1, w4, uxtw]
        and     w7, w5, #0xfffffff8
        add     w4, w4, w7
        ldr     d1, [x0, x6]
        eor     v0.8b, v0.8b, v1.8b
        str     d0, [x0, x6]
        tst     x5, #0x7
        b.eq    L404c
L40bc:
        add     x5, x2, w4, uxtw
        ldrb    w6, [x1, w4, uxtw]
        add     w7, w4, #0x1
        ldrb    w8, [x0, x5]
        eor     w6, w6, w8
        strb    w6, [x0, x5]
        cmp     w3, w7
        b.ls    L404c
        add     x8, x2, w7, uxtw
        ldrb    w5, [x1, w7, uxtw]
        add     w6, w4, #0x2
        ldrb    w7, [x0, x8]
        eor     w5, w5, w7
        strb    w5, [x0, x8]
        cmp     w3, w6
        b.ls    L404c
        add     x7, x2, w6, uxtw
        ldrb    w5, [x1, w6, uxtw]
        add     w6, w4, #0x3
        ldrb    w8, [x0, x7]
        eor     w5, w5, w8
        strb    w5, [x0, x7]
        cmp     w3, w6
        b.ls    L404c
        add     x7, x2, w6, uxtw
        ldrb    w5, [x1, w6, uxtw]
        add     w6, w4, #0x4
        ldrb    w8, [x0, x7]
        eor     w5, w5, w8
        strb    w5, [x0, x7]
        cmp     w3, w6
        b.ls    L404c
        add     x7, x2, w6, uxtw
        ldrb    w5, [x1, w6, uxtw]
        add     w6, w4, #0x5
        ldrb    w8, [x0, x7]
        eor     w5, w5, w8
        strb    w5, [x0, x7]
        cmp     w3, w6
        b.ls    L404c
        add     x7, x2, w6, uxtw
        ldrb    w5, [x1, w6, uxtw]
        add     w4, w4, #0x6
        ldrb    w6, [x0, x7]
        eor     w5, w5, w6
        strb    w5, [x0, x7]
        cmp     w3, w4
        b.ls    L404c
        add     x2, x2, w4, uxtw
        ldrb    w1, [x1, w4, uxtw]
        ldrb    w3, [x0, x2]
        eor     w1, w1, w3
        strb    w1, [x0, x2]
        ret
L4194:
        mov     w5, w3
        mov     w4, #0x0
        b       L4098

// mlkem_keccakf1600x4_extract_bytes (0x80 bytes)
L41a0:
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
        bl      L3ec0
        mov     w3, w20
        mov     w2, w19
        mov     x1, x24
        add     x0, x21, #0xc8
        bl      L3ec0
        mov     w3, w20
        mov     w2, w19
        mov     x1, x23
        add     x0, x21, #0x190
        bl      L3ec0
        ldp     x23, x24, [sp, #32]
        mov     w3, w20
        ldr     x30, [sp, #48]
        mov     w2, w19
        mov     x1, x22
        add     x0, x21, #0x258
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        b       L3ec0

// mlkem_keccakf1600x4_xor_bytes (0x80 bytes)
L4220:
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
        bl      L4000
        mov     w3, w20
        mov     w2, w19
        mov     x1, x24
        add     x0, x21, #0xc8
        bl      L4000
        mov     w3, w20
        mov     w2, w19
        mov     x1, x23
        add     x0, x21, #0x190
        bl      L4000
        ldp     x23, x24, [sp, #32]
        mov     w3, w20
        ldr     x30, [sp, #48]
        mov     w2, w19
        mov     x1, x22
        add     x0, x21, #0x258
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        b       L4000

// mlkem_keccakf1600_permute (0x5d0 bytes)
L42a0:
        stp     x19, x20, [sp, #-192]!
        .inst   0x90000021  // adrp x1, 0x8000
        add     x1, x1, #0xab0
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
L4350:
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
        b.ne    L4350
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

// mlkem_keccakf1600x4_permute (0x28 bytes)
L4870:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L42a0
        add     x0, x19, #0xc8
        bl      L42a0
        add     x0, x19, #0x190
        bl      L42a0
        add     x0, x19, #0x258
        ldp     x19, x30, [sp], #16
        b       L42a0
        nop
        nop

// mlkem512_gen_matrix (0xc4 bytes)
L48a0:
        stp     x19, x30, [sp, #-304]!
        .inst   0xf00000c5  // adrp x5, 0x1f000
        ldr     x5, [x5, #4088]
        add     x19, sp, #0x2f
        and     x19, x19, #0xffffffffffffffe0
        mov     x3, x19
        add     x4, x19, #0x100
        ldr     x6, [x5]
        str     x6, [sp, #296]
        mov     x6, #0x0
L48c8:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x3]
        add     x3, x3, #0x40
        cmp     x4, x3
        b.ne    L48c8
        cmp     w2, #0x0
        mov     w1, #0x1
        mov     w2, #0x100
        csel    w7, w2, w1, eq
        csel    w5, w1, w2, eq
        mov     w6, #0x101
        mov     x4, x19
        add     x3, x0, #0x600
        add     x2, x0, #0x400
        add     x1, x0, #0x200
        strh    wzr, [x19, #32]
        strh    w5, [x19, #96]
        strh    w7, [x19, #160]
        strh    w6, [x19, #224]
        bl      L68a0
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        stp     q0, q0, [x19, #192]
        stp     q0, q0, [x19, #224]
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4960
        ldp     x19, x30, [sp], #304
        ret
L4960:
        bl      L0830

// mlkem512_indcpa_keypair_derand (0x1f4 bytes)
L4964:
        mov     x12, #0x16f0
        sub     sp, sp, x12
        mov     x3, #0x1640
        mov     x4, #0x1600
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0x7f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        add     x22, x19, x3
        add     x20, x19, x4
        stp     x23, x24, [sp, #48]
        add     x23, x19, #0x1, lsl #12
        mov     w24, #0x2
        stp     x25, x26, [sp, #64]
        mov     x26, x0
        add     x21, x19, #0x800
        stp     x27, x30, [sp, #80]
        mov     x27, x1
        mov     x1, x22
        ldp     q0, q1, [x2]
        .inst   0xf00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        ldr     x0, [x2]
        str     x0, [sp, #5864]
        mov     x0, #0x0
        stp     q0, q1, [x22]
        mov     x0, x20
        mov     x2, #0x21
        strb    w24, [x23, #1632]
        bl      L37d0
        mov     x1, x20
        mov     x0, x19
        mov     w2, #0x0
        bl      L48a0
        mov     w7, w24
        mov     x8, #0x1400
        add     x4, x20, #0x20
        add     x3, x23, #0x200
        mov     x2, x23
        add     x1, x19, #0xa00
        mov     w0, #0x3
        strb    w0, [sp]
        mov     w6, #0x1
        mov     w5, #0x0
        add     x25, x19, x8
        mov     x0, x21
        bl      L6540
        add     x24, x19, #0xc00
        mov     x0, x21
        bl      L62e0
        mov     x0, x23
        bl      L62e0
        mov     x1, x21
        mov     x0, x25
        bl      L64a4
        mov     x3, x25
        mov     x2, x21
        mov     x0, x24
        mov     x1, x19
        bl      L6320
        mov     x3, x25
        mov     x2, x21
        add     x1, x19, #0x400
        add     x0, x19, #0xe00
        bl      L6320
        mov     x0, x24
        bl      L6520
        mov     x1, x23
        mov     x0, x24
        bl      L64f0
        mov     x0, x24
        bl      L64d0
        mov     x0, x21
        bl      L64d0
        mov     x1, x21
        mov     x0, x27
        bl      L6280
        mov     x1, x24
        mov     x0, x26
        bl      L6280
        ldp     q0, q1, [x20]
        mov     x0, x25
        mov     x2, #0x200
        mov     w1, #0x0
        stp     q0, q1, [x26, #768]
        bl      L0840
        mov     x2, #0x400
        mov     x0, x21
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x400
        mov     x0, x24
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x400
        mov     x0, x23
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        stp     xzr, xzr, [x22]
        stp     xzr, xzr, [x22, #16]
        strb    wzr, [x22, #32]
        movi    v0.4s, #0x0
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #5864]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4b54
        ldp     x19, x20, [sp, #16]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x16f0
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x30, [sp, #80]
        add     sp, sp, x12
        ret
L4b54:
        bl      L0830
        nop
        nop

// mlkem512_indcpa_enc (0x280 bytes)
L4b60:
        mov     x12, #0x20c0
        sub     sp, sp, x12
        mov     x4, #0x1a00
        mov     x5, #0x1800
        stp     x19, x20, [sp, #16]
        mov     x20, x2
        add     x19, sp, #0x9f
        .inst   0xf00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x21, x22, [sp, #32]
        and     x19, x19, #0xffffffffffffffe0
        stp     x23, x24, [sp, #48]
        mov     x21, x3
        mov     x3, #0x1c00
        stp     x25, x26, [sp, #64]
        add     x26, x19, x3
        add     x24, x19, #0x1, lsl #12
        stp     x27, x28, [sp, #80]
        add     x23, x19, x5
        add     x27, x19, x4
        str     x30, [sp, #96]
        mov     x22, x1
        str     x0, [sp, #120]
        mov     x1, x20
        mov     x0, x24
        add     x28, x19, #0x2, lsl #12
        ldr     x3, [x2]
        str     x3, [sp, #8376]
        mov     x3, #0x0
        add     x25, x19, #0xc00
        bl      L62b0
        ldp     q0, q1, [x20, #768]
        mov     x1, x22
        mov     x0, x26
        add     x22, x19, #0x800
        stp     q0, q1, [x28]
        bl      L2db0
        mov     x1, x28
        mov     x0, x19
        mov     w2, #0x1
        bl      L48a0
        mov     w0, #0x3
        strb    w0, [sp]
        mov     x6, #0x1400
        add     x20, x19, x6
        mov     x4, x21
        mov     w6, #0x1
        mov     w5, #0x0
        add     x3, x19, #0xe00
        mov     w7, #0x2
        mov     x2, x25
        add     x1, x20, #0x200
        mov     x0, x20
        bl      L6744
        mov     x1, x21
        mov     w2, #0x4
        mov     x0, x27
        bl      L66a0
        mov     x0, x20
        bl      L62e0
        mov     x1, x20
        mov     x0, x23
        bl      L64a4
        mov     x7, #0x1e00
        mov     x3, x23
        add     x21, x19, x7
        mov     x2, x20
        mov     x0, x22
        mov     x1, x19
        bl      L6320
        mov     x3, x23
        mov     x2, x20
        add     x1, x19, #0x400
        add     x0, x19, #0xa00
        bl      L6320
        mov     x3, x23
        mov     x2, x20
        mov     x1, x24
        mov     x0, x21
        bl      L6320
        mov     x0, x22
        bl      L6300
        mov     x0, x21
        bl      L5e30
        mov     x1, x25
        mov     x0, x22
        bl      L64f0
        mov     x1, x27
        mov     x0, x21
        bl      L56b0
        mov     x1, x26
        mov     x0, x21
        bl      L56b0
        mov     x0, x22
        bl      L64d0
        mov     x0, x21
        bl      L5660
        ldr     x0, [sp, #120]
        mov     x1, x22
        bl      L6220
        ldr     x0, [sp, #120]
        mov     x1, x21
        add     x0, x0, #0x280
        bl      L1e40
        mov     x0, x23
        mov     x2, #0x200
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x27
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x26
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x21
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x400
        mov     x0, x22
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x400
        mov     x0, x25
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x400
        mov     x0, x24
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x400
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        stp     xzr, xzr, [x28]
        stp     xzr, xzr, [x28, #16]
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #8376]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4ddc
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
L4ddc:
        bl      L0830

// mlkem512_indcpa_dec (0x148 bytes)
L4de0:
        sub     sp, sp, #0xe60
        .inst   0xf00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x5f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        add     x20, x19, #0x400
        stp     x23, x24, [sp, #32]
        add     x21, x19, #0xc00
        mov     x24, x0
        str     x30, [sp, #48]
        mov     x0, x20
        mov     x23, x1
        ldr     x2, [x3]
        str     x2, [sp, #3672]
        mov     x2, #0x0
        bl      L6250
        add     x1, x23, #0x280
        mov     x0, x21
        bl      L2060
        add     x23, x19, #0x800
        mov     x1, x22
        mov     x0, x19
        bl      L62b0
        add     x22, x19, #0xa00
        mov     x0, x20
        bl      L62e0
        mov     x1, x20
        mov     x0, x23
        bl      L64a4
        mov     x3, x23
        mov     x2, x20
        mov     x1, x19
        mov     x0, x22
        bl      L6320
        mov     x0, x22
        bl      L5e30
        mov     x1, x22
        mov     x0, x21
        bl      L56e0
        mov     x0, x21
        bl      L5660
        mov     x1, x21
        mov     x0, x24
        bl      L2ed0
        mov     x0, x23
        mov     x2, #0x200
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x22
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x21
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x400
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x400
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #3672]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4f24
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        add     sp, sp, #0xe60
        ret
L4f24:
        bl      L0830
        nop
        nop

// mlkem512_check_pk (0x138 bytes)
L4f30:
        sub     sp, sp, #0x740
        mov     x1, x0
        .inst   0xf00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x19, x20, [sp]
        add     x20, sp, #0x3f
        and     x20, x20, #0xffffffffffffffe0
        stp     x21, x30, [sp, #16]
        mov     x19, x0
        mov     x0, x20
        ldr     x3, [x2]
        str     x3, [sp, #1848]
        mov     x3, #0x0
        add     x21, x20, #0x400
        bl      L62b0
        mov     x0, x20
        bl      L64d0
        mov     x0, x21
        mov     x1, x20
        bl      L6280
        movi    v2.4s, #0x0
        mov     x0, x19
        mov     x2, x21
        add     x1, x20, #0x700
        mov     v3.16b, v2.16b
        nop
L4f98:
        ldr     q0, [x0], #16
        ldr     q1, [x2], #16
        eor     v0.16b, v0.16b, v1.16b
        orr     v3.16b, v3.16b, v0.16b
        eor     v2.16b, v2.16b, v0.16b
        cmp     x1, x2
        b.ne    L4f98
        movi    v1.4s, #0x0
        ext     v4.16b, v3.16b, v1.16b, #8
        ext     v0.16b, v2.16b, v1.16b, #8
        orr     v3.16b, v4.16b, v3.16b
        eor     v2.16b, v0.16b, v2.16b
        ext     v4.16b, v3.16b, v1.16b, #4
        ext     v0.16b, v2.16b, v1.16b, #4
        orr     v4.16b, v4.16b, v3.16b
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
        neg     w0, w0
        eor     w0, w1, w0, asr #16
        cmp     w1, w0, uxtb
        mov     x2, #0x300
        mov     x0, x21
        mov     w1, #0x0
        mov     w19, #0xfffffffc
        csel    w19, wzr, w19, eq
        bl      L0840
        mov     x2, #0x400
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1848]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L5064
        ldp     x21, x30, [sp, #16]
        mov     w0, w19
        ldp     x19, x20, [sp]
        add     sp, sp, #0x740
        ret
L5064:
        bl      L0830
        nop
        nop

// mlkem512_check_sk (0xe8 bytes)
L5070:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        add     x1, x0, #0x300
        .inst   0xd00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x3f
        mov     x2, #0x320
        ldr     x4, [x3]
        str     x4, [sp, #88]
        mov     x4, #0x0
        and     x19, x19, #0xffffffffffffffe0
        mov     x0, x19
        bl      L3730
        ldp     q1, q3, [x19]
        ldr     q0, [x20, #1568]
        ldr     q2, [x20, #1584]
        eor     v0.16b, v0.16b, v1.16b
        movi    v1.4s, #0x0
        eor     v2.16b, v2.16b, v3.16b
        orr     v4.16b, v0.16b, v2.16b
        eor     v0.16b, v0.16b, v2.16b
        ext     v3.16b, v4.16b, v1.16b, #8
        ext     v2.16b, v0.16b, v1.16b, #8
        orr     v3.16b, v3.16b, v4.16b
        eor     v2.16b, v2.16b, v0.16b
        ext     v4.16b, v3.16b, v1.16b, #4
        ext     v0.16b, v2.16b, v1.16b, #4
        orr     v4.16b, v4.16b, v3.16b
        eor     v0.16b, v0.16b, v2.16b
        ext     v3.16b, v4.16b, v1.16b, #2
        ext     v2.16b, v0.16b, v1.16b, #2
        orr     v3.16b, v3.16b, v4.16b
        eor     v2.16b, v2.16b, v0.16b
        ext     v0.16b, v3.16b, v1.16b, #1
        ext     v1.16b, v2.16b, v1.16b, #1
        orr     v0.16b, v0.16b, v3.16b
        eor     v1.16b, v1.16b, v2.16b
        umov    w1, v0.b[0]
        umov    w2, v1.b[0]
        neg     w1, w1
        eor     w1, w2, w1, asr #16
        cmp     w2, w1, uxtb
        mov     w0, #0xfffffffb
        csel    w0, wzr, w0, eq
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xd00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #88]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L5154
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #96
        ret
L5154:
        bl      L0830
        nop
        nop

// mlkem512_keypair_derand (0x94 bytes)
L5160:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        mov     x21, x0
        str     x30, [sp, #32]
        bl      L4964
        mov     x2, #0x320
        mov     w20, w0
        cbnz    w0, L51c4
        mov     x1, x21
        add     x0, x19, #0x300
        bl      L0810
        mov     x1, x21
        add     x0, x19, #0x620
        mov     x2, #0x320
        bl      L3730
        ldp     q0, q1, [x22, #32]
        add     x19, x19, #0x640
        mov     w0, w20
        stp     q0, q1, [x19]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L51c4:
        mov     x0, x21
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x660
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mlkem512_keypair (0x8c bytes)
L51f4:
        stp     x19, x20, [sp, #-128]!
        mov     x20, x0
        .inst   0xd00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x21, x30, [sp, #16]
        add     x19, sp, #0x3f
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x1
        ldr     x1, [x2]
        str     x1, [sp, #120]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x40
        bl      L0820
        cbnz    w0, L5274
        mov     x1, x21
        mov     x0, x20
        mov     x2, x19
        bl      L5160
L5240:
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xd00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #120]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L527c
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #128
        ret
L5274:
        mov     w0, #0xfffffffd
        b       L5240
L527c:
        bl      L0830

// mlkem512_enc_derand (0xe0 bytes)
L5280:
        stp     x19, x20, [sp, #-224]!
        .inst   0xd00000c4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x5f
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        and     x19, x19, #0xffffffffffffffe0
        str     x30, [sp, #48]
        mov     x24, x0
        mov     x21, x2
        mov     x22, x3
        ldr     x1, [x4]
        str     x1, [sp, #216]
        mov     x1, #0x0
        mov     x0, x2
        add     x20, x19, #0x40
        bl      L4f30
        cbz     w0, L5310
L52cc:
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        .inst   0xd00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #216]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L535c
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #224
        ret
L5310:
        ldp     q0, q1, [x22]
        mov     x1, x21
        add     x0, x19, #0x60
        mov     x2, #0x320
        stp     q0, q1, [x20]
        bl      L3730
        mov     x1, x20
        mov     x0, x19
        mov     x2, #0x40
        bl      L37d0
        mov     x2, x21
        mov     x0, x24
        add     x3, x19, #0x20
        mov     x1, x20
        bl      L4b60
        cbnz    w0, L52cc
        ldp     q0, q1, [x19]
        stp     q0, q1, [x23]
        b       L52cc
L535c:
        bl      L0830

// mlkem512_enc (0x98 bytes)
L5360:
        stp     x19, x20, [sp, #-112]!
        mov     x20, x0
        .inst   0xd00000c3  // adrp x3, 0x1f000
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
        bl      L0820
        cbnz    w0, L53ec
        mov     x2, x22
        mov     x1, x21
        mov     x0, x20
        mov     x3, x19
        bl      L5280
L53b8:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xd00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #104]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L53f4
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret
L53ec:
        mov     w0, #0xfffffffd
        b       L53b8
L53f4:
        bl      L0830
        nop
        nop

// mlkem512_dec (0x20c bytes)
L5400:
        sub     sp, sp, #0x400
        .inst   0xd00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x5f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        stp     x23, x24, [sp, #32]
        mov     x23, x0
        mov     x24, x2
        stp     x25, x30, [sp, #48]
        mov     x25, x1
        mov     x0, x2
        ldr     x1, [x3]
        str     x1, [sp, #1016]
        mov     x1, #0x0
        bl      L5070
        cbz     w0, L54b0
        mov     w20, w0
        add     x22, x19, #0x360
        add     x21, x19, #0x320
L5454:
        mov     x0, x19
        mov     x2, #0x320
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x22]
        stp     q0, q0, [x22, #32]
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1016]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L5608
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        add     sp, sp, #0x400
        ret
L54b0:
        add     x22, x19, #0x360
        mov     x2, x24
        mov     x0, x22
        mov     x1, x25
        add     x21, x19, #0x320
        bl      L4de0
        mov     w20, w0
        cbnz    w0, L5454
        ldr     q0, [x24, #1568]
        mov     x1, x22
        ldr     q1, [x24, #1584]
        mov     x0, x21
        mov     x2, #0x40
        stp     q0, q1, [x19, #896]
        bl      L37d0
        add     x3, x19, #0x340
        add     x2, x24, #0x300
        mov     x1, x22
        mov     x0, x19
        bl      L4b60
        mov     w20, w0
        cbnz    w0, L5454
        movi    v2.4s, #0x0
        mov     x0, x19
        mov     x1, x25
        add     x2, x19, #0x300
        mov     v3.16b, v2.16b
        nop
L5520:
        ldr     q0, [x1], #16
        ldr     q1, [x0], #16
        eor     v0.16b, v0.16b, v1.16b
        orr     v3.16b, v3.16b, v0.16b
        eor     v2.16b, v2.16b, v0.16b
        cmp     x0, x2
        b.ne    L5520
        movi    v1.4s, #0x0
        ext     v4.16b, v3.16b, v1.16b, #8
        ext     v0.16b, v2.16b, v1.16b, #8
        orr     v3.16b, v4.16b, v3.16b
        eor     v2.16b, v0.16b, v2.16b
        ext     v4.16b, v3.16b, v1.16b, #4
        ext     v0.16b, v2.16b, v1.16b, #4
        orr     v4.16b, v4.16b, v3.16b
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
        neg     w0, w0
        eor     w0, w1, w0, asr #16
        ldr     q0, [x24, #1600]
        and     w0, w0, #0xff
        ldr     q1, [x24, #1616]
        mov     x2, #0x300
        eor     w24, w0, w1
        mov     x1, x25
        add     x0, x19, #0x20
        stp     q0, q1, [x19]
        bl      L0810
        mov     x0, x23
        mov     x2, x19
        mov     x3, #0x320
        mov     x1, #0x20
        bl      L3650
        neg     w4, w24
        sub     x23, x23, #0x1
        mov     x0, #0x1
        nop
L55d8:
        add     x2, x21, x0
        mov     w1, w4
        ldurb   w2, [x2, #-1]
        ldrb    w3, [x23, x0]
        eor     w3, w2, w3
        and     w1, w3, w1, asr #16
        eor     w2, w2, w1
        strb    w2, [x23, x0]
        add     x0, x0, #0x1
        cmp     x0, #0x21
        b.ne    L55d8
        b       L5454
L5608:
        bl      L0830
        nop

// mlkem_poly_tomont (0x48 bytes)
L5610:
        .inst   0xf0000002  // adrp x2, 0x8000
        .inst   0xf0000001  // adrp x1, 0x8000
        mvni    v3.8h, #0xd, lsl #8
        ldr     q5, [x2, #2336]
        ldr     q4, [x1, #2400]
        add     x1, x0, #0x200
L5628:
        ldr     q0, [x0]
        smull   v1.4s, v0.4h, v4.4h
        smull2  v0.4s, v0.8h, v4.8h
        uzp1    v2.8h, v1.8h, v0.8h
        mul     v2.8h, v2.8h, v5.8h
        smlal   v1.4s, v2.4h, v3.4h
        smlal2  v0.4s, v2.8h, v3.8h
        uzp2    v1.8h, v1.8h, v0.8h
        str     q1, [x0], #16
        cmp     x1, x0
        b.ne    L5628
        ret
        nop
        nop

// mlkem_poly_reduce (0x4c bytes)
L5660:
        add     x5, x0, #0x200
        mov     w7, #0x4ebf
        mov     w6, #0x2000000
        mov     w4, #0xfffff2ff
L5670:
        ldrsh   w2, [x0]
        madd    w1, w2, w7, w6
        asr     w1, w1, #26
        madd    w1, w1, w4, w2
        sxth    w1, w1
        mov     w2, w1
        neg     w2, w2, lsr #16
        add     w3, w1, #0xd01
        eor     w3, w1, w3
        and     w2, w3, w2, asr #16
        eor     w1, w1, w2
        strh    w1, [x0], #2
        cmp     x5, x0
        b.ne    L5670
        ret
        nop

// mlkem_poly_add (0x28 bytes)
L56b0:
        mov     x2, #0x0
        nop
L56b8:
        ldr     q0, [x0, x2]
        ldr     q1, [x1, x2]
        add     v0.8h, v0.8h, v1.8h
        str     q0, [x0, x2]
        add     x2, x2, #0x10
        cmp     x2, #0x200
        b.ne    L56b8
        ret
        nop
        nop

// mlkem_poly_sub (0x28 bytes)
L56e0:
        mov     x2, #0x0
        nop
L56e8:
        ldr     q0, [x0, x2]
        ldr     q1, [x1, x2]
        sub     v0.8h, v0.8h, v1.8h
        str     q0, [x0, x2]
        add     x2, x2, #0x10
        cmp     x2, #0x200
        b.ne    L56e8
        ret
        nop
        nop

// mlkem_poly_mulcache_compute (0x41c bytes)
L5710:
        add     x2, x0, #0x100
        add     x4, x1, #0x2
        cmp     x4, x2
        add     x2, x1, #0x200
        ccmp    x0, x2, #0x2, cc
        b.cc    L5abc
        ld4     {v4.8h-v7.8h}, [x4]
        .inst   0xf0000004  // adrp x4, 0x8000
        str     d8, [sp, #-16]!
        mov     x3, x0
        ldr     q8, [x4, #2416]
        .inst   0xf0000004  // adrp x4, 0x8000
        mov     v0.16b, v4.16b
        add     x14, x1, #0x42
        mov     v1.16b, v6.16b
        .inst   0xf000000f  // adrp x15, 0x8000
        ldr     q6, [x4, #2432]
        .inst   0xf0000004  // adrp x4, 0x8000
        smull   v7.4s, v0.4h, v8.4h
        add     x13, x1, #0x82
        smull2  v4.4s, v0.8h, v8.8h
        add     x12, x0, #0x40
        smull   v5.4s, v1.4h, v6.4h
        add     x11, x1, #0xc2
        smull2  v1.4s, v1.8h, v6.8h
        add     x10, x0, #0x60
        ldr     q16, [x4, #2336]
        add     x9, x1, #0x102
        uzp1    v8.8h, v7.8h, v4.8h
        add     x8, x0, #0x80
        uzp1    v6.8h, v5.8h, v1.8h
        add     x7, x1, #0x142
        mvni    v0.8h, #0xd, lsl #8
        add     x6, x0, #0xa0
        ldr     q19, [x15, #2448]
        .inst   0xf000000f  // adrp x15, 0x8000
        mul     v8.8h, v8.8h, v16.8h
        add     x5, x1, #0x182
        mul     v6.8h, v6.8h, v16.8h
        ldr     d20, [x15, #2336]
        .inst   0xf000000f  // adrp x15, 0x8000
        add     x4, x0, #0xc0
        smlal   v7.4s, v8.4h, v0.4h
        smlal2  v4.4s, v8.8h, v0.8h
        smlal2  v1.4s, v6.8h, v0.8h
        smlal   v5.4s, v6.4h, v0.4h
        ldr     q18, [x15, #2464]
        .inst   0xf000000f  // adrp x15, 0x8000
        uzp2    v2.8h, v7.8h, v4.8h
        uzp2    v3.8h, v5.8h, v1.8h
        ldr     q8, [x15, #2480]
        .inst   0xf000000f  // adrp x15, 0x8000
        st2     {v2.8h-v3.8h}, [x3], #32
        ld4     {v4.8h-v7.8h}, [x14]
        .inst   0xf000000e  // adrp x14, 0x8000
        ldr     q31, [x15, #2496]
        .inst   0xf000000f  // adrp x15, 0x8000
        mov     v1.16b, v6.16b
        mov     v17.16b, v4.16b
        smull   v6.4s, v4.4h, v19.4h
        ldr     q30, [x15, #2512]
        .inst   0xf000000f  // adrp x15, 0x8000
        smull   v5.4s, v1.4h, v18.4h
        smull2  v4.4s, v17.8h, v19.8h
        smull2  v1.4s, v1.8h, v18.8h
        ldr     q29, [x15, #2528]
        .inst   0xf000000f  // adrp x15, 0x8000
        uzp1    v17.8h, v6.8h, v4.8h
        uzp1    v7.8h, v5.8h, v1.8h
        ldr     q27, [x14, #2560]
        .inst   0xf000000e  // adrp x14, 0x8000
        mul     v17.8h, v17.8h, v16.8h
        mul     v7.8h, v7.8h, v16.8h
        ldr     q28, [x15, #2544]
        smlal   v6.4s, v17.4h, v0.4h
        smlal2  v4.4s, v17.8h, v0.8h
        smlal2  v1.4s, v7.8h, v0.8h
        smlal   v5.4s, v7.4h, v0.4h
        ldr     q26, [x14, #2576]
        .inst   0xf000000e  // adrp x14, 0x8000
        uzp2    v2.8h, v6.8h, v4.8h
        uzp2    v3.8h, v5.8h, v1.8h
        ldr     q25, [x14, #2592]
        .inst   0xf000000e  // adrp x14, 0x8000
        mvni    v19.4s, #0xd, lsl #8
        st2     {v2.8h-v3.8h}, [x3]
        ld4     {v4.8h-v7.8h}, [x13]
        ldr     q24, [x14, #2608]
        .inst   0xf000000e  // adrp x14, 0x8000
        mov     v1.16b, v6.16b
        mov     v17.16b, v4.16b
        smull   v6.4s, v4.4h, v8.4h
        ldr     q23, [x14, #2624]
        .inst   0xf000000e  // adrp x14, 0x8000
        smull   v5.4s, v1.4h, v31.4h
        smull2  v4.4s, v17.8h, v8.8h
        smull2  v1.4s, v1.8h, v31.8h
        ldr     q22, [x14, #2640]
        .inst   0xf000000e  // adrp x14, 0x8000
        uzp1    v8.8h, v6.8h, v4.8h
        uzp1    v7.8h, v5.8h, v1.8h
        ldr     q21, [x14, #2656]
        .inst   0xf000000e  // adrp x14, 0x8000
        mul     v8.8h, v8.8h, v16.8h
        mul     v7.8h, v7.8h, v16.8h
        ldr     q18, [x14, #2672]
        smlal   v6.4s, v8.4h, v0.4h
        smlal2  v4.4s, v8.8h, v0.8h
        smlal2  v1.4s, v7.8h, v0.8h
        smlal   v5.4s, v7.4h, v0.4h
        uzp2    v2.8h, v6.8h, v4.8h
        uzp2    v3.8h, v5.8h, v1.8h
        st2     {v2.8h-v3.8h}, [x12]
        ld4     {v4.8h-v7.8h}, [x11]
        mov     v1.16b, v6.16b
        mov     v17.16b, v4.16b
        smull   v6.4s, v4.4h, v30.4h
        smull   v5.4s, v1.4h, v29.4h
        smull2  v4.4s, v17.8h, v30.8h
        smull2  v1.4s, v1.8h, v29.8h
        uzp1    v8.8h, v6.8h, v4.8h
        uzp1    v7.8h, v5.8h, v1.8h
        mul     v8.8h, v8.8h, v16.8h
        mul     v7.8h, v7.8h, v16.8h
        smlal   v6.4s, v8.4h, v0.4h
        smlal2  v4.4s, v8.8h, v0.8h
        smlal2  v1.4s, v7.8h, v0.8h
        smlal   v5.4s, v7.4h, v0.4h
        uzp2    v2.8h, v6.8h, v4.8h
        uzp2    v3.8h, v5.8h, v1.8h
        st2     {v2.8h-v3.8h}, [x10]
        ld4     {v4.8h-v7.8h}, [x9]
        mov     v1.16b, v6.16b
        mov     v17.16b, v4.16b
        smull   v6.4s, v4.4h, v28.4h
        smull   v5.4s, v1.4h, v27.4h
        smull2  v4.4s, v17.8h, v28.8h
        smull2  v1.4s, v1.8h, v27.8h
        uzp1    v8.8h, v6.8h, v4.8h
        uzp1    v7.8h, v5.8h, v1.8h
        mul     v8.8h, v8.8h, v16.8h
        mul     v7.8h, v7.8h, v16.8h
        smlal   v6.4s, v8.4h, v0.4h
        smlal2  v4.4s, v8.8h, v0.8h
        smlal2  v1.4s, v7.8h, v0.8h
        smlal   v5.4s, v7.4h, v0.4h
        uzp2    v2.8h, v6.8h, v4.8h
        uzp2    v3.8h, v5.8h, v1.8h
        st2     {v2.8h-v3.8h}, [x8]
        ld4     {v4.8h-v7.8h}, [x7]
        mov     v1.16b, v6.16b
        mov     v17.16b, v4.16b
        smull   v6.4s, v4.4h, v26.4h
        smull   v5.4s, v1.4h, v25.4h
        smull2  v4.4s, v17.8h, v26.8h
        smull2  v1.4s, v1.8h, v25.8h
        uzp1    v8.8h, v6.8h, v4.8h
        uzp1    v7.8h, v5.8h, v1.8h
        mul     v8.8h, v8.8h, v16.8h
        mul     v7.8h, v7.8h, v16.8h
        smlal   v6.4s, v8.4h, v0.4h
        smlal2  v4.4s, v8.8h, v0.8h
        smlal2  v1.4s, v7.8h, v0.8h
        smlal   v5.4s, v7.4h, v0.4h
        uzp2    v2.8h, v6.8h, v4.8h
        uzp2    v3.8h, v5.8h, v1.8h
        st2     {v2.8h-v3.8h}, [x6]
        ld4     {v4.8h-v7.8h}, [x5]
        mov     v1.16b, v6.16b
        mov     v17.16b, v4.16b
        smull   v6.4s, v4.4h, v24.4h
        smull   v5.4s, v1.4h, v23.4h
        smull2  v4.4s, v17.8h, v24.8h
        smull2  v1.4s, v1.8h, v23.8h
        uzp1    v8.8h, v6.8h, v4.8h
        uzp1    v7.8h, v5.8h, v1.8h
        mul     v8.8h, v8.8h, v16.8h
        mul     v7.8h, v7.8h, v16.8h
        smlal   v6.4s, v8.4h, v0.4h
        smlal2  v4.4s, v8.8h, v0.8h
        ldr     d8, [sp], #16
        smlal   v5.4s, v7.4h, v0.4h
        smlal2  v1.4s, v7.8h, v0.8h
        uzp2    v2.8h, v6.8h, v4.8h
        uzp2    v3.8h, v5.8h, v1.8h
        st2     {v2.8h-v3.8h}, [x4]
        ldur    d1, [x2, #-62]
        ldur    d4, [x2, #-54]
        ldur    d3, [x2, #-46]
        ldur    d2, [x2, #-38]
        uzp1    v1.4h, v1.4h, v4.4h
        uzp1    v3.4h, v3.4h, v2.4h
        uzp1    v2.4h, v1.4h, v3.4h
        uzp2    v1.4h, v1.4h, v3.4h
        sxtl    v2.4s, v2.4h
        sxtl    v1.4s, v1.4h
        mul     v2.4s, v2.4s, v22.4s
        mul     v1.4s, v1.4s, v21.4s
        xtn     v4.4h, v2.4s
        xtn     v3.4h, v1.4s
        mul     v4.4h, v4.4h, v20.4h
        mul     v3.4h, v3.4h, v20.4h
        sxtl    v4.4s, v4.4h
        sxtl    v3.4s, v3.4h
        mla     v2.4s, v4.4s, v19.4s
        mla     v1.4s, v3.4s, v19.4s
        shrn    v2.4h, v2.4s, #16
        shrn    v1.4h, v1.4s, #16
        zip1    v3.4h, v2.4h, v1.4h
        zip2    v2.4h, v2.4h, v1.4h
        stp     d3, d2, [x0, #224]
        ldr     h2, [x1, #486]
        ldr     h1, [x1, #482]
        ldr     h7, [x1, #490]
        ldr     h6, [x1, #494]
        mov     v1.h[1], v2.h[0]
        ldr     h5, [x1, #498]
        ldr     h4, [x1, #502]
        ldr     h3, [x1, #506]
        ldr     h2, [x1, #510]
        mov     v1.h[2], v7.h[0]
        mov     v1.h[3], v6.h[0]
        mov     v1.h[4], v5.h[0]
        mov     v1.h[5], v4.h[0]
        mov     v1.h[6], v3.h[0]
        mov     v1.h[7], v2.h[0]
        smull   v2.4s, v1.4h, v18.4h
        smull2  v1.4s, v1.8h, v18.8h
        uzp1    v3.8h, v2.8h, v1.8h
        mul     v3.8h, v3.8h, v16.8h
        smlal   v2.4s, v3.4h, v0.4h
        smlal2  v1.4s, v3.8h, v0.8h
        uzp2    v2.8h, v2.8h, v1.8h
        str     q2, [x0, #240]
        ret
L5abc:
        .inst   0xf0000008  // adrp x8, 0x8000
        add     x8, x8, #0xb80
        add     x5, x8, #0x80
        add     x3, x0, #0x2
        add     x8, x8, #0x100
        mov     w7, #0xfffff301
        mov     w6, #0xfffff2ff
L5ad8:
        ldrsh   w0, [x5], #2
        add     x4, x4, #0x8
        ldursh  w2, [x4, #-8]
        neg     w1, w0
        sxth    w1, w1
        mul     w2, w2, w0
        mul     w0, w2, w7
        sxth    w0, w0
        madd    w0, w0, w6, w2
        asr     w0, w0, #16
        sturh   w0, [x3, #-2]
        ldursh  w0, [x4, #-4]
        mul     w1, w1, w0
        mul     w0, w1, w7
        sxth    w0, w0
        madd    w0, w0, w6, w1
        asr     w0, w0, #16
        strh    w0, [x3], #4
        cmp     x8, x5
        b.ne    L5ad8
        ret
        nop

// mlkem_poly_ntt (0x2f8 bytes)
L5b30:
        mov     x4, x0
        add     x17, x0, #0x2
        .inst   0xf0000000  // adrp x0, 0x8000
        stp     x19, x20, [sp, #-32]!
        .inst   0xf000000e  // adrp x14, 0x8000
        ldr     q6, [x0, #2336]
        .inst   0xf0000000  // adrp x0, 0x8000
        mvni    v16.4s, #0xd, lsl #8
        add     x14, x14, #0xb80
        mvni    v5.8h, #0xd, lsl #8
        ldr     d7, [x0, #2336]
        mov     w11, #0x0
        mov     w6, #0xfffffd0a
        mov     w18, #0x1
        mov     w9, #0xfffff301
        mov     w8, #0xfffff2ff
        stp     x21, x30, [sp, #16]
        mov     w30, #0x100
L5b78:
        add     w16, w11, #0x1
        mov     w7, #0x0
        lsl     w11, w18, w11
        lsr     w15, w30, w16
        mov     x13, x15
        mov     w10, w15
        lsl     w12, w15, #1
        nop
L5b98:
        add     w11, w11, #0x1
        cmp     w7, w10
        b.cs    L5c38
        sub     w20, w10, w7
        mov     w1, w7
        sub     w19, w20, #0x1
        cmp     w19, #0x2
        b.ls    L5bec
        add     x5, x15, x1
        lsl     x2, x1, #1
        add     x0, x5, #0x8
        add     x21, x2, #0x10
        add     x21, x4, x21
        add     x2, x4, x2
        lsl     x0, x0, #1
        sub     x3, x0, #0x10
        add     x0, x4, x0
        add     x3, x4, x3
        cmp     x3, x21
        ccmp    x2, x0, #0x2, cc
        b.cs    L5c50
L5bec:
        add     x19, x1, w19, uxtw
        mov     w5, w10
        sub     x5, x5, x1
        add     x1, x4, x1, lsl #1
        add     x19, x17, x19, lsl #1
L5c00:
        ldrsh   w2, [x1, x5, lsl #1]
        ldrh    w3, [x1]
        mul     w2, w2, w6
        mul     w0, w2, w9
        sxth    w0, w0
        madd    w0, w0, w8, w2
        asr     w0, w0, #16
        sub     w2, w3, w0
        strh    w2, [x1, x5, lsl #1]
        ldrh    w2, [x1]
        add     w0, w0, w2
        strh    w0, [x1], #2
        cmp     x19, x1
        b.ne    L5c00
L5c38:
        add     w7, w7, w12
        add     w10, w10, w12
        cmp     w7, #0xff
        b.hi    L5df8
L5c48:
        ldrsh   w6, [x14, w11, uxtw #1]
        b       L5b98
L5c50:
        cmp     w19, #0x6
        b.ls    L5e10
        lsr     w19, w20, #3
        dup     v4.8h, w6
        mov     x0, #0x0
        lsl     x19, x19, #4
L5c68:
        ldr     q1, [x3, x0]
        ldr     q3, [x2, x0]
        smull   v0.4s, v1.4h, v4.4h
        smull2  v1.4s, v1.8h, v4.8h
        uzp1    v2.8h, v0.8h, v1.8h
        mul     v2.8h, v2.8h, v6.8h
        smlal2  v1.4s, v2.8h, v5.8h
        smlal   v0.4s, v2.4h, v5.4h
        uzp2    v0.8h, v0.8h, v1.8h
        sub     v1.8h, v3.8h, v0.8h
        str     q1, [x3, x0]
        ldr     q1, [x2, x0]
        add     v0.8h, v1.8h, v0.8h
        str     q0, [x2, x0]
        add     x0, x0, #0x10
        cmp     x19, x0
        b.ne    L5c68
        and     w0, w20, #0xfffffff8
        add     w2, w7, w0
        tst     x20, #0x7
        b.eq    L5c38
        sub     w20, w20, w0
        sub     w3, w20, #0x1
        cmp     w3, #0x2
        b.ls    L5d28
L5ccc:
        add     x5, x5, x0
        fmov    s1, w6
        add     x0, x1, x0
        and     w3, w20, #0xfffffffc
        lsl     x5, x5, #1
        add     w2, w2, w3
        lsl     x0, x0, #1
        ldr     d0, [x4, x5]
        ldr     d2, [x4, x0]
        sxtl    v0.4s, v0.4h
        mul     v0.4s, v0.4s, v1.s[0]
        xtn     v1.4h, v0.4s
        mul     v1.4h, v1.4h, v7.4h
        sxtl    v1.4s, v1.4h
        mla     v0.4s, v1.4s, v16.4s
        shrn    v0.4h, v0.4s, #16
        sub     v1.4h, v2.4h, v0.4h
        str     d1, [x4, x5]
        ldr     d1, [x4, x0]
        add     v0.4h, v1.4h, v0.4h
        str     d0, [x4, x0]
        tst     x20, #0x3
        b.eq    L5c38
L5d28:
        add     w5, w13, w2
        ubfiz   x3, x2, #1, #32
        add     w1, w2, #0x1
        ldrsh   w19, [x4, x5, lsl #1]
        ldrh    w20, [x4, x3]
        mul     w19, w19, w6
        mul     w0, w19, w9
        sxth    w0, w0
        madd    w0, w0, w8, w19
        asr     w0, w0, #16
        sub     w19, w20, w0
        strh    w19, [x4, x5, lsl #1]
        ldrh    w5, [x4, x3]
        add     w0, w0, w5
        strh    w0, [x4, x3]
        cmp     w10, w1
        b.ls    L5c38
        add     w19, w13, w1
        ubfiz   x1, x1, #1, #32
        add     w2, w2, #0x2
        ldrsh   w3, [x4, x19, lsl #1]
        ldrh    w5, [x4, x1]
        mul     w3, w3, w6
        mul     w0, w3, w9
        sxth    w0, w0
        madd    w0, w0, w8, w3
        asr     w0, w0, #16
        sub     w3, w5, w0
        strh    w3, [x4, x19, lsl #1]
        ldrh    w3, [x4, x1]
        add     w0, w0, w3
        strh    w0, [x4, x1]
        cmp     w10, w2
        b.ls    L5c38
        add     w5, w13, w2
        ubfiz   x2, x2, #1, #32
        add     w7, w7, w12
        add     w10, w10, w12
        ldrsh   w1, [x4, x5, lsl #1]
        ldrh    w3, [x4, x2]
        mul     w1, w1, w6
        mul     w0, w1, w9
        sxth    w0, w0
        madd    w0, w0, w8, w1
        asr     w0, w0, #16
        sub     w1, w3, w0
        strh    w1, [x4, x5, lsl #1]
        ldrh    w1, [x4, x2]
        add     w0, w0, w1
        strh    w0, [x4, x2]
        cmp     w7, #0xff
        b.ls    L5c48
L5df8:
        cmp     w16, #0x7
        b.eq    L5e1c
        lsl     w0, w18, w16
        mov     w11, w16
        ldrsh   w6, [x14, x0, lsl #1]
        b       L5b78
L5e10:
        mov     w2, w7
        mov     x0, #0x0
        b       L5ccc
L5e1c:
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop
        nop

// mlkem_poly_invntt_tomont (0x3f0 bytes)
L5e30:
        mov     x4, x0
        .inst   0xf0000000  // adrp x0, 0x8000
        stp     x19, x20, [sp, #-32]!
        add     x1, x4, #0x200
        ldr     q4, [x0, #2688]
        .inst   0xf0000000  // adrp x0, 0x8000
        mvni    v3.8h, #0xd, lsl #8
        stp     x21, x30, [sp, #16]
        ldr     q5, [x0, #2336]
        mov     x0, x4
L5e58:
        ldr     q0, [x0]
        smull   v1.4s, v0.4h, v4.4h
        smull2  v0.4s, v0.8h, v4.8h
        uzp1    v2.8h, v1.8h, v0.8h
        mul     v2.8h, v2.8h, v5.8h
        smlal   v1.4s, v2.4h, v3.4h
        smlal2  v0.4s, v2.8h, v3.8h
        uzp2    v1.8h, v1.8h, v0.8h
        str     q1, [x0], #16
        cmp     x0, x1
        b.ne    L5e58
        .inst   0xf0000000  // adrp x0, 0x8000
        mov     w10, #0x4ebf
        mvni    v19.4h, #0xd, lsl #8
        .inst   0xf000000f  // adrp x15, 0x8000
        ldr     q6, [x0, #2704]
        .inst   0xf0000000  // adrp x0, 0x8000
        movi    v5.4s, #0x2, lsl #24
        add     x15, x15, #0xb80
        ldr     q7, [x0, #2336]
        .inst   0xf0000000  // adrp x0, 0x8000
        dup     v18.4s, w10
        add     x18, x4, #0x2
        ldr     d17, [x0, #2336]
        mov     w8, #0x65c
        mov     w17, #0x7
        mov     w12, #0x2000000
        mov     w6, #0xfffff2ff
        mov     w11, #0xfffff301
        nop
L5ed0:
        mov     w14, #0x100
        mov     w9, #0x1
        lsr     w16, w14, w17
        mov     x14, x16
        mvni    v16.4s, #0xd, lsl #8
        lsl     w9, w9, w17
        mvni    v3.8h, #0xd, lsl #8
        mov     w7, w16
        lsl     w13, w16, #1
        sub     w9, w9, #0x1
        mov     w5, #0x0
        nop
L5f00:
        sub     w9, w9, #0x1
        cmp     w5, w7
        b.cs    L5fb4
        sub     w30, w7, w5
        mov     w3, w5
        sub     w20, w30, #0x1
        cmp     w20, #0x2
        b.ls    L5f54
        add     x19, x16, x3
        lsl     x2, x3, #1
        add     x0, x19, #0x8
        add     x21, x2, #0x10
        add     x21, x4, x21
        add     x2, x4, x2
        lsl     x0, x0, #1
        sub     x1, x0, #0x10
        add     x0, x4, x0
        add     x1, x4, x1
        cmp     x1, x21
        ccmp    x2, x0, #0x2, cc
        b.cs    L5fcc
L5f54:
        mov     w0, w7
        add     x2, x4, w7, uxtw #1
        add     x30, x0, w20, uxtw
        sub     x3, x3, x0
        add     x30, x18, x30, lsl #1
L5f68:
        ldrsh   w19, [x2, x3, lsl #1]
        ldrh    w0, [x2]
        add     w0, w19, w0
        sxth    w0, w0
        madd    w1, w0, w10, w12
        asr     w1, w1, #26
        madd    w0, w1, w6, w0
        strh    w0, [x2, x3, lsl #1]
        ldrh    w0, [x2]
        sub     w0, w0, w19
        sxth    w0, w0
        mul     w0, w0, w8
        mul     w1, w0, w11
        sxth    w1, w1
        madd    w0, w1, w6, w0
        asr     w0, w0, #16
        strh    w0, [x2], #2
        cmp     x2, x30
        b.ne    L5f68
L5fb4:
        add     w5, w5, w13
        add     w7, w7, w13
        cmp     w5, #0xff
        b.hi    L61ec
L5fc4:
        ldrsh   w8, [x15, w9, uxtw #1]
        b       L5f00
L5fcc:
        cmp     w20, #0x6
        b.ls    L6208
        lsr     w20, w30, #3
        dup     v20.8h, w8
        mov     x0, #0x0
        lsl     x20, x20, #4
        nop
L5fe8:
        ldr     q4, [x2, x0]
        ldr     q0, [x1, x0]
        mov     v1.16b, v5.16b
        mov     v2.16b, v5.16b
        add     v0.8h, v0.8h, v4.8h
        smlal   v1.4s, v0.4h, v6.4h
        smlal2  v2.4s, v0.8h, v6.8h
        sshr    v1.4s, v1.4s, #26
        sshr    v2.4s, v2.4s, #26
        uzp1    v1.8h, v1.8h, v2.8h
        mla     v0.8h, v1.8h, v3.8h
        str     q0, [x2, x0]
        ldr     q0, [x1, x0]
        sub     v0.8h, v0.8h, v4.8h
        smull   v1.4s, v0.4h, v20.4h
        smull2  v0.4s, v0.8h, v20.8h
        uzp1    v2.8h, v1.8h, v0.8h
        mul     v2.8h, v2.8h, v7.8h
        smlal   v1.4s, v2.4h, v3.4h
        smlal2  v0.4s, v2.8h, v3.8h
        uzp2    v1.8h, v1.8h, v0.8h
        str     q1, [x1, x0]
        add     x0, x0, #0x10
        cmp     x20, x0
        b.ne    L5fe8
        and     w0, w30, #0xfffffff8
        add     w1, w5, w0
        tst     x30, #0x7
        b.eq    L5fb4
        sub     w30, w30, w0
        sub     w2, w30, #0x1
        cmp     w2, #0x2
        b.ls    L60e0
L606c:
        add     x3, x3, x0
        add     x0, x19, x0
        mov     v1.16b, v5.16b
        and     w2, w30, #0xfffffffc
        lsl     x0, x0, #1
        lsl     x3, x3, #1
        add     w1, w1, w2
        ldr     d2, [x4, x3]
        ldr     d0, [x4, x0]
        add     v0.4h, v0.4h, v2.4h
        sxtl    v4.4s, v0.4h
        mla     v1.4s, v4.4s, v18.4s
        sshr    v1.4s, v1.4s, #26
        xtn     v1.4h, v1.4s
        mla     v0.4h, v1.4h, v19.4h
        fmov    s1, w8
        str     d0, [x4, x3]
        ldr     d0, [x4, x0]
        sub     v0.4h, v0.4h, v2.4h
        sxtl    v0.4s, v0.4h
        mul     v0.4s, v0.4s, v1.s[0]
        xtn     v1.4h, v0.4s
        mul     v1.4h, v1.4h, v17.4h
        sxtl    v1.4s, v1.4h
        mla     v0.4s, v1.4s, v16.4s
        shrn    v0.4h, v0.4s, #16
        str     d0, [x4, x0]
        tst     x30, #0x3
        b.eq    L5fb4
L60e0:
        add     w2, w14, w1
        ldrsh   w20, [x4, w1, uxtw #1]
        add     w19, w1, #0x1
        lsl     x2, x2, #1
        ldrh    w0, [x4, x2]
        add     w0, w20, w0
        sxth    w0, w0
        madd    w3, w0, w10, w12
        asr     w3, w3, #26
        madd    w0, w3, w6, w0
        strh    w0, [x4, w1, uxtw #1]
        ldrh    w0, [x4, x2]
        sub     w0, w0, w20
        sxth    w0, w0
        mul     w0, w0, w8
        mul     w3, w0, w11
        sxth    w3, w3
        madd    w0, w3, w6, w0
        asr     w0, w0, #16
        strh    w0, [x4, x2]
        cmp     w19, w7
        b.cs    L5fb4
        add     w3, w14, w19
        ldrsh   w20, [x4, w19, uxtw #1]
        add     w1, w1, #0x2
        lsl     x3, x3, #1
        ldrh    w0, [x4, x3]
        add     w0, w20, w0
        sxth    w0, w0
        madd    w2, w0, w10, w12
        asr     w2, w2, #26
        madd    w0, w2, w6, w0
        strh    w0, [x4, w19, uxtw #1]
        ldrh    w0, [x4, x3]
        sub     w0, w0, w20
        sxth    w0, w0
        mul     w0, w0, w8
        mul     w2, w0, w11
        sxth    w2, w2
        madd    w0, w2, w6, w0
        asr     w0, w0, #16
        strh    w0, [x4, x3]
        cmp     w7, w1
        b.ls    L5fb4
        add     w2, w14, w1
        ldrsh   w19, [x4, w1, uxtw #1]
        add     w5, w5, w13
        add     w7, w7, w13
        lsl     x2, x2, #1
        ldrh    w0, [x4, x2]
        add     w0, w19, w0
        sxth    w0, w0
        madd    w3, w0, w10, w12
        asr     w3, w3, #26
        madd    w0, w3, w6, w0
        strh    w0, [x4, w1, uxtw #1]
        ldrh    w0, [x4, x2]
        sub     w0, w0, w19
        sxth    w0, w0
        mul     w0, w0, w8
        mul     w1, w0, w11
        sxth    w1, w1
        madd    w0, w1, w6, w0
        asr     w0, w0, #16
        strh    w0, [x4, x2]
        cmp     w5, #0xff
        b.ls    L5fc4
L61ec:
        subs    w17, w17, #0x1
        b.eq    L6214
        mov     w0, #0x1
        lsl     w0, w0, w17
        sub     w0, w0, #0x1
        ldrsh   w8, [x15, x0, lsl #1]
        b       L5ed0
L6208:
        mov     w1, w5
        mov     x0, #0x0
        b       L606c
L6214:
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret

// mlkem512_polyvec_compress_du (0x28 bytes)
L6220:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L1fd0
        ldr     x30, [sp, #16]
        add     x1, x20, #0x200
        add     x0, x19, #0x140
        ldp     x19, x20, [sp], #32
        b       L1fd0
        nop
        nop

// mlkem512_polyvec_decompress_du (0x28 bytes)
L6250:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L23b0
        ldr     x30, [sp, #16]
        add     x1, x20, #0x140
        add     x0, x19, #0x200
        ldp     x19, x20, [sp], #32
        b       L23b0
        nop
        nop

// mlkem512_polyvec_tobytes (0x28 bytes)
L6280:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L2870
        ldr     x30, [sp, #16]
        add     x1, x20, #0x200
        add     x0, x19, #0x180
        ldp     x19, x20, [sp], #32
        b       L2870
        nop
        nop

// mlkem512_polyvec_frombytes (0x28 bytes)
L62b0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L2aa4
        ldr     x30, [sp, #16]
        add     x1, x20, #0x180
        add     x0, x19, #0x200
        ldp     x19, x20, [sp], #32
        b       L2aa4
        nop
        nop

// mlkem512_polyvec_ntt (0x18 bytes)
L62e0:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L5b30
        add     x0, x19, #0x200
        ldp     x19, x30, [sp], #16
        b       L5b30
        nop
        nop

// mlkem512_polyvec_invntt_tomont (0x18 bytes)
L6300:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L5e30
        add     x0, x19, #0x200
        ldp     x19, x30, [sp], #16
        b       L5e30
        nop
        nop

// mlkem512_polyvec_basemul_acc_montgomery_cached (0x184 bytes)
L6320:
        mov     x4, x0
        add     x0, x0, #0x200
        cmp     x3, x0
        mov     x6, x3
        add     x3, x3, #0x200
        mov     x0, x1
        ccmp    x4, x3, #0x2, cc
        mov     x1, x2
        b.cc    L63fc
        .inst   0xd0000003  // adrp x3, 0x8000
        mov     x2, x6
        mvni    v18.8h, #0xd, lsl #8
        add     x6, x1, #0x200
        ldr     q19, [x3, #2336]
L6358:
        add     x3, x0, #0x200
        add     x5, x1, #0x200
        add     x2, x2, #0x10
        ld2     {v6.8h-v7.8h}, [x0]
        add     x0, x0, #0x20
        ld2     {v4.8h-v5.8h}, [x3]
        ld2     {v22.8h-v23.8h}, [x1]
        add     x1, x1, #0x20
        ld2     {v16.8h-v17.8h}, [x5]
        smull2  v0.4s, v23.8h, v6.8h
        smull   v1.4s, v23.4h, v6.4h
        smull   v3.4s, v4.4h, v16.4h
        smull2  v2.4s, v4.8h, v16.8h
        ldur    q25, [x2, #-16]
        smlal   v3.4s, v22.4h, v6.4h
        smlal2  v2.4s, v22.8h, v6.8h
        smlal2  v0.4s, v22.8h, v7.8h
        smlal   v1.4s, v22.4h, v7.4h
        ldr     q27, [x2, #240]
        smlal2  v0.4s, v4.8h, v17.8h
        smlal   v1.4s, v4.4h, v17.4h
        smlal2  v2.4s, v25.8h, v7.8h
        smlal   v3.4s, v25.4h, v7.4h
        smlal2  v0.4s, v5.8h, v16.8h
        smlal   v1.4s, v5.4h, v16.4h
        smlal2  v2.4s, v5.8h, v27.8h
        smlal   v3.4s, v5.4h, v27.4h
        uzp1    v4.8h, v1.8h, v0.8h
        uzp1    v6.8h, v3.8h, v2.8h
        mul     v4.8h, v4.8h, v19.8h
        mul     v5.8h, v6.8h, v19.8h
        smlal   v1.4s, v4.4h, v18.4h
        smlal2  v0.4s, v4.8h, v18.8h
        smlal   v3.4s, v5.4h, v18.4h
        smlal2  v2.4s, v5.8h, v18.8h
        uzp2    v21.8h, v1.8h, v0.8h
        uzp2    v20.8h, v3.8h, v2.8h
        st2     {v20.8h-v21.8h}, [x4], #32
        cmp     x6, x1
        b.ne    L6358
        ret
L63fc:
        mov     x7, x4
        add     x13, x0, #0x200
        mov     w12, #0xfffff301
        mov     w11, #0xfffff2ff
        nop
L6410:
        ldrsh   w16, [x0, #2]
        add     x0, x0, #0x4
        ldrsh   w2, [x1]
        add     x6, x6, #0x2
        ldrsh   w3, [x1, #512]
        add     x7, x7, #0x4
        ldursh  w10, [x0, #-4]
        add     x1, x1, #0x4
        ldrsh   w15, [x0, #510]
        ldrsh   w14, [x0, #508]
        ldursh  w5, [x6, #-2]
        ldrsh   w9, [x6, #254]
        mul     w18, w2, w10
        ldrsh   w4, [x1, #510]
        mul     w2, w2, w16
        ldursh  w8, [x1, #-2]
        mul     w17, w3, w14
        mul     w3, w3, w15
        madd    w5, w5, w16, w18
        madd    w4, w4, w14, w3
        madd    w2, w8, w10, w2
        madd    w9, w9, w15, w17
        add     w4, w4, w2
        add     w5, w5, w9
        mul     w2, w4, w12
        mul     w3, w5, w12
        sxth    w2, w2
        sxth    w3, w3
        madd    w2, w2, w11, w4
        madd    w3, w3, w11, w5
        asr     w2, w2, #16
        sturh   w2, [x7, #-2]
        asr     w3, w3, #16
        sturh   w3, [x7, #-4]
        cmp     x0, x13
        b.ne    L6410
        ret

// mlkem512_polyvec_mulcache_compute (0x28 bytes)
L64a4:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L5710
        ldr     x30, [sp, #16]
        add     x1, x20, #0x200
        add     x0, x19, #0x100
        ldp     x19, x20, [sp], #32
        b       L5710
        nop

// mlkem512_polyvec_reduce (0x18 bytes)
L64d0:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L5660
        add     x0, x19, #0x200
        ldp     x19, x30, [sp], #16
        b       L5660
        nop
        nop

// mlkem512_polyvec_add (0x28 bytes)
L64f0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L56b0
        ldr     x30, [sp, #16]
        add     x1, x20, #0x200
        add     x0, x19, #0x200
        ldp     x19, x20, [sp], #32
        b       L56b0
        nop
        nop

// mlkem512_polyvec_tomont (0x18 bytes)
L6520:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L5610
        add     x0, x19, #0x200
        ldp     x19, x30, [sp], #16
        b       L5610
        nop
        nop

// mlkem512_poly_getnoise_eta1_4x (0x158 bytes)
L6540:
        sub     sp, sp, #0x480
        stp     x19, x20, [sp, #16]
        add     x20, sp, #0x7f
        and     x20, x20, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        add     x10, x20, #0x340
        add     x9, x20, #0x380
        stp     x23, x24, [sp, #48]
        add     x19, x20, #0x300
        mov     x22, x2
        stp     x25, x26, [sp, #64]
        add     x8, x20, #0x3c0
        add     x25, x20, #0x180
        stp     x27, x30, [sp, #80]
        add     x27, x20, #0x240
        mov     x21, x3
        ldp     q0, q1, [x4]
        mov     x3, x27
        .inst   0xb00000c4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        mov     x24, x0
        mov     x23, x1
        mov     x0, x20
        ldr     x2, [x4]
        str     x2, [sp, #1144]
        mov     x2, #0x0
        stp     q0, q1, [x9]
        mov     x2, x25
        stp     q0, q1, [x10]
        mov     x4, #0xc0
        add     x26, x20, x4
        strb    w5, [x19, #32]
        mov     x5, x19
        strb    w6, [x19, #96]
        mov     x6, x10
        strb    w7, [x19, #160]
        mov     x7, x9
        mov     x9, #0x21
        stp     x8, x9, [sp]
        ldrb    w9, [sp, #1152]
        stp     q0, q1, [x8]
        mov     x1, x26
        strb    w9, [x19, #224]
        stp     q0, q1, [x19]
        bl      L3b80
        mov     x1, x20
        mov     x0, x24
        bl      L7270
        mov     x1, x26
        mov     x0, x23
        bl      L7270
        mov     x1, x25
        mov     x0, x22
        bl      L7270
        cbz     x21, L6628
        mov     x1, x27
        mov     x0, x21
        bl      L7270
L6628:
        mov     x0, x20
        mov     x2, #0x300
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        stp     q0, q0, [x19, #192]
        stp     q0, q0, [x19, #224]
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1144]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L6694
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x30, [sp, #80]
        add     sp, sp, #0x480
        ret
L6694:
        bl      L0830
        nop
        nop

// mlkem512_poly_getnoise_eta2 (0xa4 bytes)
L66a0:
        stp     x19, x20, [sp, #-240]!
        mov     x3, #0x21
        add     x19, sp, #0x3f
        stp     x21, x30, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        .inst   0xb00000c4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        add     x20, x19, #0x80
        ldp     q0, q1, [x1]
        mov     x21, x0
        ldr     x0, [x4]
        str     x0, [sp, #232]
        mov     x0, #0x0
        strb    w2, [x20, #32]
        mov     x2, x20
        mov     x0, x19
        mov     x1, #0x80
        stp     q0, q1, [x20]
        bl      L3650
        mov     x1, x19
        mov     x0, x21
        bl      L6fe0
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     xzr, xzr, [x19, #128]
        stp     xzr, xzr, [x20, #16]
        strb    wzr, [x20, #32]
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L6740
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #240
        ret
L6740:
        bl      L0830

// mlkem512_poly_getnoise_eta1122_4x (0x154 bytes)
L6744:
        sub     sp, sp, #0x480
        stp     x19, x20, [sp, #16]
        add     x20, sp, #0x7f
        and     x20, x20, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        add     x10, x20, #0x340
        add     x9, x20, #0x380
        stp     x23, x24, [sp, #48]
        add     x19, x20, #0x300
        mov     x22, x2
        stp     x25, x26, [sp, #64]
        add     x8, x20, #0x3c0
        add     x25, x20, #0x240
        stp     x27, x30, [sp, #80]
        add     x26, x20, #0x180
        mov     x21, x3
        ldp     q0, q1, [x4]
        mov     x3, x25
        .inst   0xb00000c4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        mov     x24, x0
        mov     x23, x1
        mov     x0, x20
        ldr     x2, [x4]
        str     x2, [sp, #1144]
        mov     x2, #0x0
        stp     q0, q1, [x9]
        mov     x2, x26
        stp     q0, q1, [x10]
        mov     x4, #0xc0
        add     x27, x20, x4
        strb    w5, [x19, #32]
        mov     x5, x19
        strb    w6, [x19, #96]
        mov     x6, x10
        strb    w7, [x19, #160]
        mov     x7, x9
        mov     x9, #0x21
        stp     x8, x9, [sp]
        ldrb    w9, [sp, #1152]
        stp     q0, q1, [x8]
        mov     x1, x27
        strb    w9, [x19, #224]
        stp     q0, q1, [x19]
        bl      L3b80
        mov     x1, x20
        mov     x0, x24
        bl      L7270
        mov     x1, x27
        mov     x0, x23
        bl      L7270
        mov     x1, x26
        mov     x0, x22
        bl      L6fe0
        mov     x1, x25
        mov     x0, x21
        bl      L6fe0
        mov     x0, x20
        mov     x2, #0x300
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        stp     q0, q0, [x19, #192]
        stp     q0, q0, [x19, #224]
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1144]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L6894
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x30, [sp, #80]
        add     sp, sp, #0x480
        ret
L6894:
        bl      L0830
        nop
        nop

// mlkem_poly_rej_uniform_x4 (0x568 bytes)
L68a0:
        sub     sp, sp, #0xbd0
        add     x6, sp, #0xaf
        .inst   0xb00000c5  // adrp x5, 0x1f000
        ldr     x5, [x5, #4088]
        stp     x21, x22, [sp, #16]
        and     x22, x6, #0xffffffffffffffe0
        add     x6, x22, #0x800
        stp     x19, x20, [sp]
        mov     x20, x1
        stp     x23, x24, [sp, #32]
        mov     x19, x4
        mov     x23, x6
        stp     x25, x26, [sp, #48]
        mov     x21, x2
        add     x24, x22, #0x600
        stp     x27, x28, [sp, #64]
        mov     x28, x0
        mov     x0, x6
        str     x30, [sp, #80]
        mov     w25, #0x0
        str     x3, [sp, #104]
        str     x6, [sp, #136]
        ldr     x1, [x5]
        str     x1, [sp, #3016]
        mov     x1, #0x0
        bl      L3b60
        add     x4, x19, #0xc0
        add     x3, x19, #0x80
        add     x2, x19, #0x40
        mov     x1, x19
        mov     x0, x23
        add     x19, x22, #0x400
        mov     x5, #0x22
        stp     x19, x24, [sp, #112]
        bl      L3950
        add     x0, x22, #0x200
        mov     x5, x23
        mov     x1, x0
        mov     x3, x24
        mov     x2, x19
        mov     x4, #0x3
        str     x0, [sp, #128]
        mov     x0, x22
        bl      L3ad0
        ldr     x8, [sp, #104]
        add     x10, x22, #0x1f8
        mov     x1, x22
        mov     w5, #0xd00
        b       L6990
L6964:
        cmp     w25, #0xff
        ccmp    w2, w5, #0x0, ls
        b.gt    L6984
        mov     w3, w25
L6974:
        add     w25, w3, #0x1
        strh    w2, [x28, w3, uxtw #1]
        cmp     w25, #0x100
        b.eq    L69d4
L6984:
        add     x1, x1, #0x3
        cmp     x1, x10
        b.eq    L69d4
L6990:
        ldrb    w0, [x1, #1]
        ldrb    w4, [x1]
        ldrb    w2, [x1, #2]
        lsr     w3, w0, #4
        orr     w0, w4, w0, lsl #8
        and     w0, w0, #0xfff
        orr     w2, w3, w2, lsl #4
        cmp     w0, #0xd00
        b.gt    L6964
        add     w3, w25, #0x1
        strh    w0, [x28, w25, uxtw #1]
        cmp     w3, #0xff
        mov     w25, w3
        ccmp    w2, w5, #0x0, ls
        b.le    L6974
        cmp     w25, #0x100
        b.ne    L6984
L69d4:
        ldr     x1, [sp, #128]
        add     x10, x22, #0x3f8
        mov     w26, #0x0
        mov     w5, #0xd00
        b       L6a14
L69e8:
        cmp     w26, #0xff
        ccmp    w2, w5, #0x0, ls
        b.gt    L6a08
        mov     w3, w26
L69f8:
        add     w26, w3, #0x1
        strh    w2, [x20, w3, uxtw #1]
        cmp     w26, #0x100
        b.eq    L6a58
L6a08:
        add     x1, x1, #0x3
        cmp     x1, x10
        b.eq    L6a58
L6a14:
        ldrb    w0, [x1, #1]
        ldrb    w4, [x1]
        ldrb    w2, [x1, #2]
        lsr     w3, w0, #4
        orr     w0, w4, w0, lsl #8
        and     w0, w0, #0xfff
        orr     w2, w3, w2, lsl #4
        cmp     w0, #0xd00
        b.gt    L69e8
        add     w3, w26, #0x1
        strh    w0, [x20, w26, uxtw #1]
        cmp     w3, #0xff
        mov     w26, w3
        ccmp    w2, w5, #0x0, ls
        b.le    L69f8
        cmp     w26, #0x100
        b.ne    L6a08
L6a58:
        ldr     x1, [sp, #112]
        add     x10, x22, #0x5f8
        mov     w24, #0x0
        mov     w5, #0xd00
        b       L6a98
L6a6c:
        cmp     w24, #0xff
        ccmp    w2, w5, #0x0, ls
        b.gt    L6a8c
        mov     w3, w24
L6a7c:
        add     w24, w3, #0x1
        strh    w2, [x21, w3, uxtw #1]
        cmp     w24, #0x100
        b.eq    L6adc
L6a8c:
        add     x1, x1, #0x3
        cmp     x1, x10
        b.eq    L6adc
L6a98:
        ldrb    w0, [x1, #1]
        ldrb    w4, [x1]
        ldrb    w2, [x1, #2]
        lsr     w3, w0, #4
        orr     w0, w4, w0, lsl #8
        and     w0, w0, #0xfff
        orr     w2, w3, w2, lsl #4
        cmp     w0, #0xd00
        b.gt    L6a6c
        add     w3, w24, #0x1
        strh    w0, [x21, w24, uxtw #1]
        cmp     w3, #0xff
        mov     w24, w3
        ccmp    w2, w5, #0x0, ls
        b.le    L6a7c
        cmp     w24, #0x100
        b.ne    L6a8c
L6adc:
        ldr     x1, [sp, #120]
        add     x10, x22, #0x7f8
        mov     w23, #0x0
        mov     w5, #0xd00
        b       L6b1c
L6af0:
        cmp     w23, #0xff
        ccmp    w2, w5, #0x0, ls
        b.gt    L6b10
        mov     w3, w23
L6b00:
        add     w23, w3, #0x1
        strh    w2, [x8, w3, uxtw #1]
        cmp     w23, #0x100
        b.eq    L6b60
L6b10:
        add     x1, x1, #0x3
        cmp     x1, x10
        b.eq    L6b74
L6b1c:
        ldrb    w0, [x1, #1]
        ldrb    w4, [x1]
        ldrb    w2, [x1, #2]
        lsr     w3, w0, #4
        orr     w0, w4, w0, lsl #8
        and     w0, w0, #0xfff
        orr     w2, w3, w2, lsl #4
        cmp     w0, #0xd00
        b.gt    L6af0
        add     w3, w23, #0x1
        strh    w0, [x8, w23, uxtw #1]
        cmp     w3, #0xff
        mov     w23, w3
        ccmp    w2, w5, #0x0, ls
        b.le    L6b00
        cmp     w23, #0x100
        b.ne    L6b10
L6b60:
        cmp     w25, #0xff
        mov     w0, #0xff
        ccmp    w26, w0, #0x0, hi
        ccmp    w24, w0, #0x0, hi
        b.hi    L6da4
L6b74:
        mov     w27, #0xd00
        mov     w19, #0xff
        nop
L6b80:
        ldp     x2, x3, [sp, #112]
        mov     x0, x22
        ldp     x1, x5, [sp, #128]
        mov     x4, #0x1
        str     x8, [sp, #104]
        bl      L3ad0
        ldr     x8, [sp, #104]
        cmp     w25, #0xff
        b.hi    L6c20
        add     x5, x22, #0xa8
        mov     x1, x22
        b       L6bdc
L6bb0:
        cmp     w2, #0xd00
        ccmp    w25, w19, #0x2, le
        b.hi    L6bd0
        mov     w3, w25
L6bc0:
        add     w25, w3, #0x1
        strh    w2, [x28, w3, uxtw #1]
        cmp     w25, #0x100
        b.eq    L6c20
L6bd0:
        add     x1, x1, #0x3
        cmp     x1, x5
        b.eq    L6c20
L6bdc:
        ldrb    w0, [x1, #1]
        ldrb    w4, [x1]
        ldrb    w2, [x1, #2]
        lsr     w3, w0, #4
        orr     w0, w4, w0, lsl #8
        and     w0, w0, #0xfff
        orr     w2, w3, w2, lsl #4
        cmp     w0, #0xd00
        b.gt    L6bb0
        add     w3, w25, #0x1
        strh    w0, [x28, w25, uxtw #1]
        cmp     w3, #0xff
        mov     w25, w3
        ccmp    w2, w27, #0x0, ls
        b.le    L6bc0
        cmp     w25, #0x100
        b.ne    L6bd0
L6c20:
        cmp     w26, #0xff
        b.hi    L6ca8
        ldr     x1, [sp, #128]
        add     x5, x22, #0x2a8
        b       L6c60
L6c34:
        cmp     w26, #0xff
        ccmp    w2, w27, #0x0, ls
        b.gt    L6c54
        mov     w3, w26
L6c44:
        add     w26, w3, #0x1
        strh    w2, [x20, w3, uxtw #1]
        cmp     w26, #0x100
        b.eq    L6ca8
L6c54:
        add     x1, x1, #0x3
        cmp     x1, x5
        b.eq    L6ca8
L6c60:
        ldrb    w0, [x1, #1]
        ldrb    w4, [x1]
        ldrb    w2, [x1, #2]
        lsr     w3, w0, #4
        orr     w0, w4, w0, lsl #8
        and     w0, w0, #0xfff
        orr     w2, w3, w2, lsl #4
        cmp     w0, #0xd00
        b.gt    L6c34
        add     w3, w26, #0x1
        strh    w0, [x20, w26, uxtw #1]
        cmp     w3, #0xff
        mov     w26, w3
        ccmp    w2, w27, #0x0, ls
        b.le    L6c44
        cmp     w26, #0x100
        b.ne    L6c54
        nop
L6ca8:
        cmp     w24, #0xff
        b.hi    L6d2c
        ldr     x1, [sp, #112]
        add     x5, x22, #0x4a8
        b       L6ce8
L6cbc:
        cmp     w24, #0xff
        ccmp    w2, w27, #0x0, ls
        b.gt    L6cdc
        mov     w3, w24
L6ccc:
        add     w24, w3, #0x1
        strh    w2, [x21, w3, uxtw #1]
        cmp     w24, #0x100
        b.eq    L6d2c
L6cdc:
        add     x1, x1, #0x3
        cmp     x1, x5
        b.eq    L6df8
L6ce8:
        ldrb    w0, [x1, #1]
        ldrb    w4, [x1]
        ldrb    w2, [x1, #2]
        lsr     w3, w0, #4
        orr     w0, w4, w0, lsl #8
        and     w0, w0, #0xfff
        orr     w2, w3, w2, lsl #4
        cmp     w0, #0xd00
        b.gt    L6cbc
        add     w3, w24, #0x1
        strh    w0, [x21, w24, uxtw #1]
        cmp     w3, #0xff
        mov     w24, w3
        ccmp    w2, w27, #0x0, ls
        b.le    L6ccc
        cmp     w24, #0x100
        b.ne    L6cdc
L6d2c:
        cmp     w23, #0xff
        b.hi    L6d94
L6d34:
        ldr     x1, [sp, #120]
        add     x5, x22, #0x6a8
        b       L6d4c
L6d40:
        add     x1, x1, #0x3
        cmp     x1, x5
        b.eq    L6b80
L6d4c:
        ldrb    w0, [x1, #1]
        ldrb    w4, [x1]
        ldrb    w2, [x1, #2]
        lsr     w3, w0, #4
        orr     w0, w4, w0, lsl #8
        and     w0, w0, #0xfff
        orr     w2, w3, w2, lsl #4
        cmp     w0, #0xd00
        b.gt    L6d78
        strh    w0, [x8, w23, uxtw #1]
        add     w23, w23, #0x1
L6d78:
        cmp     w23, #0xff
        ccmp    w2, w27, #0x0, ls
        b.gt    L6d8c
        strh    w2, [x8, w23, uxtw #1]
        add     w23, w23, #0x1
L6d8c:
        cmp     w23, #0x100
        b.ne    L6d40
L6d94:
        cmp     w26, #0xff
        ccmp    w25, w19, #0x0, hi
        ccmp    w24, w19, #0x0, hi
        b.ls    L6b80
L6da4:
        ldr     x0, [sp, #136]
        bl      L3b64
        mov     x0, x22
        mov     x2, #0x800
        mov     w1, #0x0
        bl      L0840
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #3016]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L6e04
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0xbd0
        ret
L6df8:
        cmp     w23, #0xff
        b.ls    L6d34
        b       L6b80
L6e04:
        bl      L0830
        nop
        nop

// mlkem_poly_rej_uniform (0x1d0 bytes)
L6e10:
        sub     sp, sp, #0x340
        .inst   0xb00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x19, x20, [sp]
        add     x20, sp, #0x5f
        and     x20, x20, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        add     x21, x20, #0x200
        mov     x22, x0
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        mov     x0, x21
        str     x30, [sp, #48]
        mov     w19, #0x0
        ldr     x1, [x2]
        str     x1, [sp, #824]
        mov     x1, #0x0
        bl      L3620
        mov     x1, x23
        mov     x0, x21
        mov     x2, #0x22
        bl      L3490
        mov     x1, #0x3
        mov     x2, x21
        mov     x0, x20
        bl      L35d0
        add     x5, x20, #0x1f8
        mov     x1, x20
        mov     w7, #0xd00
        mov     w6, #0xff
        b       L6eb8
L6e8c:
        cmp     w2, #0xd00
        ccmp    w19, w6, #0x2, le
        b.hi    L6eac
        mov     w3, w19
L6e9c:
        add     w19, w3, #0x1
        strh    w2, [x22, w3, uxtw #1]
        cmp     w19, #0x100
        b.eq    L6f00
L6eac:
        add     x1, x1, #0x3
        cmp     x1, x5
        b.eq    L6f4c
L6eb8:
        ldrb    w0, [x1, #1]
        ldrb    w4, [x1]
        ldrb    w2, [x1, #2]
        lsr     w3, w0, #4
        orr     w0, w4, w0, lsl #8
        and     w0, w0, #0xfff
        orr     w2, w3, w2, lsl #4
        cmp     w0, #0xd00
        b.gt    L6e8c
        add     w3, w19, #0x1
        strh    w0, [x22, w19, uxtw #1]
        cmp     w3, #0xff
        mov     w19, w3
        ccmp    w2, w7, #0x0, ls
        b.le    L6e9c
        cmp     w19, #0x100
        b.ne    L6eac
        nop
L6f00:
        mov     x0, x21
        bl      L3624
        mov     x0, x20
        mov     x2, #0x1f8
        mov     w1, #0x0
        bl      L0840
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #824]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L6fdc
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        add     sp, sp, #0x340
        ret
L6f4c:
        add     x24, x20, #0xa8
        mov     w23, #0xd00
        nop
L6f58:
        mov     x2, x21
        mov     x0, x20
        mov     x1, #0x1
        bl      L35d0
        mov     x2, x20
        b       L6f9c
L6f70:
        cmp     w19, #0xff
        ccmp    w3, w23, #0x0, ls
        b.gt    L6f90
        mov     w4, w19
L6f80:
        add     w19, w4, #0x1
        strh    w3, [x22, w4, uxtw #1]
L6f88:
        cmp     w19, #0x100
        b.eq    L6f00
L6f90:
        add     x2, x2, #0x3
        cmp     x2, x24
        b.eq    L6f58
L6f9c:
        ldrb    w1, [x2, #1]
        ldrb    w5, [x2]
        ldrb    w3, [x2, #2]
        lsr     w4, w1, #4
        orr     w1, w5, w1, lsl #8
        and     w1, w1, #0xfff
        orr     w3, w4, w3, lsl #4
        cmp     w1, #0xd00
        b.gt    L6f70
        add     w4, w19, #0x1
        strh    w1, [x22, w19, uxtw #1]
        cmp     w4, #0xff
        mov     w19, w4
        ccmp    w3, w23, #0x0, ls
        b.gt    L6f88
        b       L6f80
L6fdc:
        bl      L0830

// mlkem_poly_cbd2 (0x28c bytes)
L6fe0:
        mov     x3, x1
        mov     x1, x0
        add     x4, x3, #0x80
        add     x0, x0, #0x200
        cmp     x1, x4
        ccmp    x3, x0, #0x2, cc
        b.cc    L71a4
        movi    v18.16b, #0x55
        mov     x2, x3
        movi    v2.8h, #0x3
        mov     x0, x1
L700c:
        ldp     q1, q0, [x2]
        add     x2, x2, #0x20
        ushr    v4.4s, v1.4s, #1
        ushr    v3.4s, v0.4s, #1
        and     v1.16b, v1.16b, v18.16b
        and     v0.16b, v0.16b, v18.16b
        and     v4.16b, v4.16b, v18.16b
        and     v3.16b, v3.16b, v18.16b
        add     v1.4s, v4.4s, v1.4s
        add     v0.4s, v3.4s, v0.4s
        shrn    v26.4h, v1.4s, #2
        ushr    v17.4s, v0.4s, #18
        ushr    v27.4s, v0.4s, #22
        ushr    v19.4s, v0.4s, #28
        ushr    v25.4s, v1.4s, #18
        ushr    v16.4s, v1.4s, #24
        ushr    v31.4s, v0.4s, #24
        ushr    v23.4s, v1.4s, #26
        ushr    v30.4s, v0.4s, #26
        shrn    v4.4h, v1.4s, #8
        shrn    v22.4h, v1.4s, #10
        ushr    v7.4s, v1.4s, #20
        ushr    v29.4s, v0.4s, #20
        ushr    v21.4s, v1.4s, #22
        shrn    v24.4h, v1.4s, #4
        shrn    v20.4h, v1.4s, #6
        ushr    v6.4s, v1.4s, #28
        shrn    v3.4h, v1.4s, #12
        shrn    v5.4h, v1.4s, #14
        shrn2   v26.8h, v0.4s, #2
        uzp1    v28.8h, v1.8h, v0.8h
        uzp1    v25.8h, v25.8h, v17.8h
        shrn2   v4.8h, v0.4s, #8
        uzp2    v17.8h, v1.8h, v0.8h
        shrn2   v22.8h, v0.4s, #10
        uzp1    v21.8h, v21.8h, v27.8h
        shrn2   v24.8h, v0.4s, #4
        shrn2   v20.8h, v0.4s, #6
        uzp1    v6.8h, v6.8h, v19.8h
        ushr    v27.4s, v0.4s, #30
        ushr    v19.4s, v1.4s, #30
        shrn2   v3.8h, v0.4s, #12
        shrn2   v5.8h, v0.4s, #14
        uzp1    v16.8h, v16.8h, v31.8h
        uzp1    v23.8h, v23.8h, v30.8h
        uzp1    v7.8h, v7.8h, v29.8h
        uzp1    v19.8h, v19.8h, v27.8h
        and     v5.16b, v5.16b, v2.16b
        and     v26.16b, v26.16b, v2.16b
        and     v0.16b, v28.16b, v2.16b
        and     v25.16b, v25.16b, v2.16b
        and     v17.16b, v17.16b, v2.16b
        and     v16.16b, v16.16b, v2.16b
        and     v23.16b, v23.16b, v2.16b
        and     v4.16b, v4.16b, v2.16b
        and     v22.16b, v22.16b, v2.16b
        and     v7.16b, v7.16b, v2.16b
        and     v21.16b, v21.16b, v2.16b
        and     v1.16b, v24.16b, v2.16b
        and     v20.16b, v20.16b, v2.16b
        and     v6.16b, v6.16b, v2.16b
        and     v3.16b, v3.16b, v2.16b
        sub     v17.8h, v17.8h, v25.8h
        sub     v16.8h, v16.8h, v23.8h
        sub     v6.8h, v6.8h, v19.8h
        sub     v7.8h, v7.8h, v21.8h
        sub     v3.8h, v3.8h, v5.8h
        sub     v0.8h, v0.8h, v26.8h
        sub     v4.8h, v4.8h, v22.8h
        sub     v1.8h, v1.8h, v20.8h
        zip1    v5.8h, v0.8h, v17.8h
        zip1    v19.8h, v4.8h, v16.8h
        zip2    v4.8h, v4.8h, v16.8h
        zip1    v16.8h, v1.8h, v7.8h
        zip2    v1.8h, v1.8h, v7.8h
        zip1    v7.8h, v3.8h, v6.8h
        zip2    v0.8h, v0.8h, v17.8h
        zip2    v3.8h, v3.8h, v6.8h
        zip1    v17.8h, v5.8h, v19.8h
        zip2    v5.8h, v5.8h, v19.8h
        zip1    v19.8h, v16.8h, v7.8h
        zip2    v6.8h, v16.8h, v7.8h
        zip1    v7.8h, v0.8h, v4.8h
        zip2    v0.8h, v0.8h, v4.8h
        zip1    v4.8h, v1.8h, v3.8h
        zip2    v1.8h, v1.8h, v3.8h
        zip1    v3.8h, v17.8h, v19.8h
        zip2    v17.8h, v17.8h, v19.8h
        zip1    v16.8h, v5.8h, v6.8h
        zip2    v5.8h, v5.8h, v6.8h
        zip1    v6.8h, v7.8h, v4.8h
        zip2    v7.8h, v7.8h, v4.8h
        stp     q3, q17, [x0]
        zip1    v3.8h, v0.8h, v1.8h
        stp     q16, q5, [x0, #32]
        zip2    v0.8h, v0.8h, v1.8h
        stp     q6, q7, [x0, #64]
        stp     q3, q0, [x0, #96]
        add     x0, x0, #0x80
        cmp     x4, x2
        b.ne    L700c
        ret
L71a4:
        movi    v7.8h, #0x3
        mov     x2, #0x0
        nop
L71b0:
        ldr     w0, [x3, x2, lsl #2]
        lsl     x4, x2, #4
        add     x2, x2, #0x1
        and     w5, w0, #0x55555555
        lsr     w0, w0, #1
        and     w0, w0, #0x55555555
        add     w9, w0, w5
        fmov    s0, w9
        fmov    s16, w9
        ushr    v2.2s, v0.2s, #20
        ushr    v3.2s, v0.2s, #16
        ubfx    x6, x9, #6, #2
        ubfx    x0, x9, #2, #2
        fmov    d1, x0
        ubfx    x5, x9, #10, #2
        ushr    v4.2s, v0.2s, #4
        ubfx    x8, x9, #14, #2
        mov     v1.h[1], w6
        ushr    v0.2s, v0.2s, #24
        mov     v3.s[1], v2.s[0]
        ubfx    x7, x9, #18, #2
        fmov    s2, w9
        ushr    v5.2s, v16.2s, #28
        ubfx    x6, x9, #22, #2
        ushr    v6.2s, v2.2s, #8
        mov     v1.h[2], w5
        mov     v2.16b, v16.16b
        ubfx    x5, x9, #26, #2
        mov     v3.s[2], v0.s[0]
        ushr    v0.2s, v16.2s, #30
        mov     v1.h[3], w8
        mov     v2.s[1], v4.s[0]
        ushr    v4.2s, v16.2s, #12
        mov     v3.s[3], v5.s[0]
        mov     v1.h[4], w7
        mov     v2.s[2], v6.s[0]
        mov     v1.h[5], w6
        mov     v2.s[3], v4.s[0]
        mov     v1.h[6], w5
        uzp1    v2.8h, v2.8h, v3.8h
        mov     v1.h[7], v0.h[0]
        and     v2.16b, v2.16b, v7.16b
        sub     v0.8h, v2.8h, v1.8h
        str     q0, [x1, x4]
        cmp     x2, #0x20
        b.ne    L71b0
        ret
        nop

// mlkem_poly_cbd3 (0x2c0 bytes)
L7270:
        mov     x3, x0
        mov     x0, x1
        add     x1, x3, #0x200
        add     x7, x0, #0xc0
        cmp     x0, x1
        ccmp    x3, x7, #0x2, cc
        b.cc    L7488
        .inst   0xb0000001  // adrp x1, 0x8000
        stp     d8, d9, [sp, #-32]!
        movi    v4.8h, #0x7
        str     d10, [sp, #16]
        ldr     q7, [x1, #2720]
        mov     x1, x3
L72a4:
        ld3     {v22.16b-v24.16b}, [x0], #48
        mov     x2, x1
        add     x1, x1, #0x80
        uxtl    v0.8h, v22.8b
        shll    v20.8h, v23.8b, #8
        uxtl    v2.8h, v24.8b
        uxtl2   v1.8h, v22.16b
        shll2   v6.8h, v23.16b, #8
        uxtl    v8.4s, v20.4h
        uxtl    v3.4s, v0.4h
        shll    v9.4s, v2.4h, #16
        uxtl2   v5.8h, v24.16b
        uxtl2   v20.4s, v20.8h
        orr     v3.16b, v3.16b, v8.16b
        uxtl    v21.4s, v1.4h
        uxtl    v8.4s, v6.4h
        uxtl2   v0.4s, v0.8h
        orr     v3.16b, v3.16b, v9.16b
        uxtl2   v6.4s, v6.8h
        orr     v0.16b, v0.16b, v20.16b
        shll2   v20.4s, v2.8h, #16
        uxtl2   v2.4s, v1.8h
        orr     v1.16b, v21.16b, v8.16b
        shll    v8.4s, v5.4h, #16
        orr     v0.16b, v0.16b, v20.16b
        ushr    v22.4s, v3.4s, #1
        ushr    v21.4s, v3.4s, #2
        orr     v1.16b, v1.16b, v8.16b
        orr     v2.16b, v2.16b, v6.16b
        shll2   v5.4s, v5.8h, #16
        ushr    v20.4s, v0.4s, #1
        and     v21.16b, v21.16b, v7.16b
        ushr    v6.4s, v1.4s, #1
        orr     v2.16b, v2.16b, v5.16b
        and     v22.16b, v22.16b, v7.16b
        ushr    v5.4s, v1.4s, #2
        ushr    v24.4s, v0.4s, #2
        ushr    v23.4s, v2.4s, #2
        add     v22.4s, v22.4s, v21.4s
        and     v6.16b, v6.16b, v7.16b
        and     v21.16b, v3.16b, v7.16b
        and     v3.16b, v20.16b, v7.16b
        and     v20.16b, v5.16b, v7.16b
        ushr    v5.4s, v2.4s, #1
        add     v22.4s, v22.4s, v21.4s
        and     v24.16b, v24.16b, v7.16b
        and     v21.16b, v0.16b, v7.16b
        add     v0.4s, v6.4s, v20.4s
        and     v20.16b, v1.16b, v7.16b
        and     v1.16b, v5.16b, v7.16b
        and     v5.16b, v23.16b, v7.16b
        add     v3.4s, v3.4s, v24.4s
        add     v0.4s, v0.4s, v20.4s
        and     v20.16b, v2.16b, v7.16b
        add     v1.4s, v1.4s, v5.4s
        add     v3.4s, v3.4s, v21.4s
        shrn    v5.4h, v0.4s, #3
        shrn    v6.4h, v22.4s, #3
        add     v1.4s, v1.4s, v20.4s
        uzp1    v26.8h, v22.8h, v3.8h
        shrn    v9.4h, v0.4s, #9
        shrn2   v6.8h, v3.4s, #3
        uzp1    v2.8h, v0.8h, v1.8h
        shrn2   v5.8h, v1.4s, #3
        shrn    v25.4h, v22.4s, #6
        shrn    v24.4h, v22.4s, #9
        shrn2   v9.8h, v1.4s, #9
        and     v6.16b, v6.16b, v4.16b
        shrn2   v25.8h, v3.4s, #6
        shrn2   v24.8h, v3.4s, #9
        and     v26.16b, v26.16b, v4.16b
        shrn    v8.4h, v22.4s, #12
        and     v5.16b, v5.16b, v4.16b
        and     v2.16b, v2.16b, v4.16b
        sub     v16.8h, v26.8h, v6.8h
        shrn    v27.4h, v0.4s, #6
        shrn    v21.4h, v0.4s, #12
        sub     v28.8h, v2.8h, v5.8h
        shrn    v20.4h, v0.4s, #15
        and     v10.16b, v25.16b, v4.16b
        and     v26.16b, v9.16b, v4.16b
        and     v25.16b, v24.16b, v4.16b
        ushr    v5.4s, v0.4s, #18
        mov     v24.8b, v8.8b
        ushr    v9.4s, v1.4s, #18
        ushr    v8.4s, v3.4s, #18
        shrn    v23.4h, v22.4s, #15
        ushr    v6.4s, v22.4s, #18
        shrn2   v27.8h, v1.4s, #6
        shrn2   v24.8h, v3.4s, #12
        shrn2   v23.8h, v3.4s, #15
        shrn2   v21.8h, v1.4s, #12
        shrn2   v20.8h, v1.4s, #15
        ushr    v3.4s, v3.4s, #21
        ushr    v2.4s, v22.4s, #21
        uzp1    v6.8h, v6.8h, v8.8h
        ushr    v0.4s, v0.4s, #21
        uzp1    v5.8h, v5.8h, v9.8h
        ushr    v1.4s, v1.4s, #21
        uzp1    v2.8h, v2.8h, v3.8h
        and     v27.16b, v27.16b, v4.16b
        and     v24.16b, v24.16b, v4.16b
        and     v23.16b, v23.16b, v4.16b
        and     v21.16b, v21.16b, v4.16b
        and     v20.16b, v20.16b, v4.16b
        and     v6.16b, v6.16b, v4.16b
        and     v3.16b, v5.16b, v4.16b
        uzp1    v0.8h, v0.8h, v1.8h
        sub     v17.8h, v10.8h, v25.8h
        sub     v29.8h, v27.8h, v26.8h
        sub     v18.8h, v24.8h, v23.8h
        sub     v30.8h, v21.8h, v20.8h
        sub     v19.8h, v6.8h, v2.8h
        sub     v31.8h, v3.8h, v0.8h
        st4     {v16.8h-v19.8h}, [x2], #64
        st4     {v28.8h-v31.8h}, [x2]
        cmp     x0, x7
        b.ne    L72a4
        ldr     d10, [sp, #16]
        ldp     d8, d9, [sp], #32
        ret
L7488:
        movi    v5.4h, #0x7
        mov     w4, #0x9249
        mov     x2, x0
        movk    w4, #0x24, lsl #16
L7498:
        ldrb    w0, [x2, #1]
        add     x2, x2, #0x3
        ldurb   w1, [x2, #-1]
        ldurb   w5, [x2, #-3]
        lsl     w0, w0, #8
        orr     w1, w0, w1, lsl #16
        orr     w1, w1, w5
        and     w5, w1, w4
        and     w0, w4, w1, lsr #2
        and     w1, w4, w1, lsr #1
        add     w0, w0, w1
        add     w0, w0, w5
        fmov    s1, w0
        fmov    s0, w0
        ushr    v4.2s, v1.2s, #12
        ushr    v3.2s, v1.2s, #18
        ubfx    x1, x0, #9, #3
        fmov    d1, x0
        ushr    v0.2s, v0.2s, #6
        ubfx    x6, x0, #3, #3
        mov     v1.d[1], x1
        fmov    d2, x6
        ubfx    x5, x0, #15, #3
        mov     v2.h[1], w1
        mov     v1.s[1], v0.s[0]
        fmov    s0, w0
        mov     v2.h[2], w5
        ushr    v0.2s, v0.2s, #21
        mov     v1.s[2], v4.s[0]
        mov     v2.h[3], v0.h[0]
        mov     v1.s[3], v3.s[0]
        xtn     v0.4h, v1.4s
        and     v0.8b, v0.8b, v5.8b
        sub     v0.4h, v0.4h, v2.4h
        str     d0, [x3], #8
        cmp     x2, x7
        b.ne    L7498
        ret

// mlkem768_gen_matrix (0x154 bytes)
L7530:
        stp     x19, x20, [sp, #-320]!
        mov     w4, w2
        mov     x20, x0
        .inst   0x900000c5  // adrp x5, 0x1f000
        ldr     x5, [x5, #4088]
        add     x19, sp, #0x3f
        str     x30, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     x3, x19
        add     x0, x19, #0x100
        ldr     x2, [x5]
        str     x2, [sp, #312]
        mov     x2, #0x0
L7564:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x3]
        add     x3, x3, #0x40
        cmp     x0, x3
        b.ne    L7564
        add     x1, x20, #0x200
        add     x2, x20, #0x400
        add     x3, x20, #0x600
        cbnz    w4, L7648
        mov     w7, #0x1
        mov     w6, #0x2
        mov     w5, #0x100
        mov     x4, x19
        mov     x0, x20
        strh    wzr, [x19, #32]
        strh    w7, [x19, #96]
        strh    w6, [x19, #160]
        strh    w5, [x19, #224]
        bl      L68a0
        mov     w5, #0x201
        mov     w6, #0x200
        mov     w7, #0x102
L75bc:
        mov     w8, #0x101
        mov     x4, x19
        add     x3, x20, #0xe00
        add     x2, x20, #0xc00
        add     x1, x20, #0xa00
        add     x0, x20, #0x800
        strh    w8, [x19, #32]
        strh    w7, [x19, #96]
        strh    w6, [x19, #160]
        strh    w5, [x19, #224]
        bl      L68a0
        mov     w2, #0x202
        add     x0, x20, #0x1, lsl #12
        mov     x1, x19
        strh    w2, [x19, #32]
        bl      L6e10
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        stp     q0, q0, [x19, #192]
        stp     q0, q0, [x19, #224]
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #312]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L7680
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #320
        ret
L7648:
        mov     w7, #0x100
        mov     w6, #0x200
        mov     w5, #0x1
        mov     x4, x19
        mov     x0, x20
        strh    wzr, [x19, #32]
        strh    w7, [x19, #96]
        strh    w6, [x19, #160]
        strh    w5, [x19, #224]
        bl      L68a0
        mov     w5, #0x102
        mov     w6, #0x2
        mov     w7, #0x201
        b       L75bc
L7680:
        bl      L0830

// mlkem768_indcpa_keypair_derand (0x248 bytes)
L7684:
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
        mov     x7, #0x1800
        add     x21, x19, x4
        stp     x23, x24, [sp, #48]
        add     x23, x19, x3
        add     x20, x19, x5
        stp     x25, x26, [sp, #64]
        add     x25, x19, #0x2, lsl #12
        add     x26, x19, x6
        stp     x27, x28, [sp, #80]
        add     x24, x19, x7
        mov     w27, #0x3
        str     x30, [sp, #96]
        mov     w22, #0xffffffff
        stp     x0, x1, [sp, #112]
        mov     x1, x23
        add     x28, x21, #0x20
        ldp     q0, q1, [x2]
        .inst   0x900000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        ldr     x0, [x2]
        str     x0, [sp, #10248]
        mov     x0, #0x0
        stp     q0, q1, [x23]
        mov     x0, x21
        mov     x2, #0x21
        strb    w27, [x25, #1888]
        bl      L37d0
        mov     x1, x21
        mov     x0, x19
        mov     w2, #0x0
        bl      L7530
        strb    w22, [sp]
        mov     x4, x28
        add     x2, x20, #0x400
        add     x1, x20, #0x200
        mov     x0, x20
        mov     w7, #0x2
        mov     w6, #0x1
        mov     w5, #0x0
        mov     x3, #0x0
        bl      L87b4
        mov     x1, x25
        mov     x4, x28
        mov     w5, w27
        mov     x8, #0x2400
        add     x2, x26, #0x400
        strb    w22, [sp]
        mov     w7, #0x5
        mov     w6, #0x4
        mov     x3, #0x0
        add     x27, x19, x8
        mov     x0, x26
        bl      L87b4
        mov     x0, x20
        bl      L84c0
        mov     x0, x26
        bl      L84c0
        mov     x25, x24
        mov     x28, x19
        mov     x1, x20
        mov     x0, x27
        mov     w22, #0x0
        bl      L8704
L77a8:
        mov     x1, x28
        mov     x0, x25
        mov     x3, x27
        mov     x2, x20
        add     w22, w22, #0x1
        bl      L8500
        add     x28, x28, #0x600
        add     x25, x25, #0x200
        cmp     w22, #0x3
        b.ne    L77a8
        mov     x0, x24
        bl      L8794
        mov     x1, x26
        mov     x0, x24
        bl      L8760
        mov     x0, x24
        bl      L8740
        mov     x0, x20
        bl      L8740
        ldr     x0, [sp, #120]
        mov     x1, x20
        bl      L8450
        ldr     x22, [sp, #112]
        mov     x1, x24
        mov     x0, x22
        bl      L8450
        ldp     q0, q1, [x21]
        add     x25, x22, #0x480
        mov     x0, x27
        mov     x2, #0x300
        mov     w1, #0x0
        stp     q0, q1, [x25]
        bl      L0840
        mov     x2, #0x600
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x600
        mov     x0, x24
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x600
        mov     x0, x26
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x1200
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        stp     xzr, xzr, [x23]
        stp     xzr, xzr, [x23, #16]
        strb    wzr, [x23, #32]
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #10248]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L78c8
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
L78c8:
        bl      L0830
        nop

// mlkem768_indcpa_enc (0x2c8 bytes)
L78d0:
        mov     x12, #0x33d0
        sub     sp, sp, x12
        mov     x4, #0x1e00
        mov     x5, #0x2d00
        mov     x6, #0x1800
        mov     x7, #0x2a00
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0xaf
        and     x19, x19, #0xffffffffffffffe0
        mov     x20, x2
        add     x4, x19, x4
        .inst   0x900000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x21, x22, [sp, #32]
        mov     x21, x3
        stp     x23, x24, [sp, #48]
        mov     x22, x1
        add     x24, x19, x6
        stp     x25, x26, [sp, #64]
        add     x23, x19, x7
        mov     x1, x20
        stp     x27, x28, [sp, #80]
        add     x28, x19, x5
        mov     x26, x19
        str     x30, [sp, #96]
        stp     x0, x4, [sp, #120]
        mov     x0, x4
        ldr     x3, [x2]
        str     x3, [sp, #13256]
        mov     x3, #0x0
        bl      L8484
        ldr     q0, [x20, #1152]
        mov     x8, #0x3300
        ldr     q1, [x20, #1168]
        add     x2, x19, x8
        mov     x9, #0x2f00
        mov     x10, #0x1200
        mov     x11, #0x2400
        add     x0, x19, x9
        add     x20, x19, x11
        mov     x1, x22
        mov     x25, x2
        add     x22, x19, x10
        stp     q0, q1, [x2]
        mov     x27, x22
        str     x0, [sp, #136]
        bl      L2db0
        mov     x1, x25
        mov     x0, x19
        mov     w2, #0x1
        bl      L7530
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
        bl      L87b4
        mov     x4, x21
        add     x1, x24, #0x200
        mov     x3, x28
        add     x2, x24, #0x400
        mov     w0, #0x6
        strb    w0, [sp]
        mov     w7, #0x5
        mov     w6, #0x4
        mov     w5, #0x3
        mov     x0, x24
        bl      L87b4
        mov     w21, #0x0
        mov     x0, x20
        bl      L84c0
        mov     x1, x20
        mov     x0, x23
        bl      L8704
L7a0c:
        mov     x1, x26
        mov     x0, x27
        mov     x3, x23
        mov     x2, x20
        add     w21, w21, #0x1
        bl      L8500
        add     x26, x26, #0x600
        add     x27, x27, #0x200
        cmp     w21, #0x3
        b.ne    L7a0c
        ldr     x27, [sp, #128]
        mov     x3, x23
        mov     x2, x20
        mov     x0, #0x3100
        mov     x1, x27
        add     x21, x19, x0
        mov     x0, x21
        bl      L8500
        mov     x0, x22
        bl      L84e0
        mov     x0, x21
        bl      L5e30
        mov     x1, x24
        mov     x0, x22
        bl      L8760
        mov     x1, x28
        mov     x0, x21
        bl      L56b0
        ldr     x26, [sp, #136]
        mov     x0, x21
        mov     x1, x26
        bl      L56b0
        mov     x0, x22
        bl      L8740
        mov     x0, x21
        bl      L5660
        ldr     x0, [sp, #120]
        mov     x1, x22
        bl      L83e0
        ldr     x0, [sp, #120]
        mov     x1, x21
        add     x0, x0, #0x3c0
        bl      L1e40
        mov     x0, x23
        mov     x2, #0x300
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x28
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x26
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x21
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x600
        mov     x0, x22
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x600
        mov     x0, x24
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x600
        mov     x0, x27
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x600
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x1200
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        stp     xzr, xzr, [x25]
        stp     xzr, xzr, [x25, #16]
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #13256]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L7b94
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
L7b94:
        bl      L0830
        nop
        nop

// mlkem768_indcpa_dec (0x154 bytes)
L7ba0:
        mov     x12, #0x1360
        sub     sp, sp, x12
        .inst   0x900000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x5f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        mov     x2, #0x1100
        stp     x23, x24, [sp, #32]
        add     x21, x19, x2
        add     x20, x19, #0x600
        str     x30, [sp, #48]
        mov     x24, x0
        mov     x23, x1
        mov     x0, x20
        ldr     x2, [x3]
        str     x2, [sp, #4952]
        mov     x2, #0x0
        bl      L8414
        add     x1, x23, #0x3c0
        mov     x0, x21
        bl      L2060
        add     x23, x19, #0xc00
        mov     x1, x22
        mov     x0, x19
        bl      L8484
        add     x22, x19, #0xf00
        mov     x0, x20
        bl      L84c0
        mov     x1, x20
        mov     x0, x23
        bl      L8704
        mov     x3, x23
        mov     x2, x20
        mov     x1, x19
        mov     x0, x22
        bl      L8500
        mov     x0, x22
        bl      L5e30
        mov     x1, x22
        mov     x0, x21
        bl      L56e0
        mov     x0, x21
        bl      L5660
        mov     x1, x21
        mov     x0, x24
        bl      L2ed0
        mov     x0, x23
        mov     x2, #0x300
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x22
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x21
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x600
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x600
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4952]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L7cf0
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x1360
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        add     sp, sp, x12
        ret
L7cf0:
        bl      L0830
        nop
        nop
        nop

// mlkem768_check_pk (0x138 bytes)
L7d00:
        sub     sp, sp, #0xac0
        mov     x1, x0
        .inst   0x900000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x19, x20, [sp]
        add     x20, sp, #0x3f
        and     x20, x20, #0xffffffffffffffe0
        stp     x21, x30, [sp, #16]
        mov     x19, x0
        mov     x0, x20
        ldr     x3, [x2]
        str     x3, [sp, #2744]
        mov     x3, #0x0
        add     x21, x20, #0x600
        bl      L8484
        mov     x0, x20
        bl      L8740
        mov     x0, x21
        mov     x1, x20
        bl      L8450
        movi    v2.4s, #0x0
        mov     x0, x19
        mov     x2, x21
        add     x1, x20, #0xa80
        mov     v3.16b, v2.16b
        nop
L7d68:
        ldr     q0, [x0], #16
        ldr     q1, [x2], #16
        eor     v0.16b, v0.16b, v1.16b
        orr     v3.16b, v3.16b, v0.16b
        eor     v2.16b, v2.16b, v0.16b
        cmp     x1, x2
        b.ne    L7d68
        movi    v1.4s, #0x0
        ext     v4.16b, v3.16b, v1.16b, #8
        ext     v0.16b, v2.16b, v1.16b, #8
        orr     v3.16b, v4.16b, v3.16b
        eor     v2.16b, v0.16b, v2.16b
        ext     v4.16b, v3.16b, v1.16b, #4
        ext     v0.16b, v2.16b, v1.16b, #4
        orr     v4.16b, v4.16b, v3.16b
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
        neg     w0, w0
        eor     w0, w1, w0, asr #16
        cmp     w1, w0, uxtb
        mov     x2, #0x480
        mov     x0, x21
        mov     w1, #0x0
        mov     w19, #0xfffffffc
        csel    w19, wzr, w19, eq
        bl      L0840
        mov     x2, #0x600
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        .inst   0x900000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #2744]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L7e34
        ldp     x21, x30, [sp, #16]
        mov     w0, w19
        ldp     x19, x20, [sp]
        add     sp, sp, #0xac0
        ret
L7e34:
        bl      L0830
        nop
        nop

// mlkem768_check_sk (0xe8 bytes)
L7e40:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        add     x1, x0, #0x480
        .inst   0x900000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x3f
        mov     x2, #0x4a0
        ldr     x4, [x3]
        str     x4, [sp, #88]
        mov     x4, #0x0
        and     x19, x19, #0xffffffffffffffe0
        mov     x0, x19
        bl      L3730
        ldp     q1, q3, [x19]
        ldr     q0, [x20, #2336]
        ldr     q2, [x20, #2352]
        eor     v0.16b, v0.16b, v1.16b
        movi    v1.4s, #0x0
        eor     v2.16b, v2.16b, v3.16b
        orr     v4.16b, v0.16b, v2.16b
        eor     v0.16b, v0.16b, v2.16b
        ext     v3.16b, v4.16b, v1.16b, #8
        ext     v2.16b, v0.16b, v1.16b, #8
        orr     v3.16b, v3.16b, v4.16b
        eor     v2.16b, v2.16b, v0.16b
        ext     v4.16b, v3.16b, v1.16b, #4
        ext     v0.16b, v2.16b, v1.16b, #4
        orr     v4.16b, v4.16b, v3.16b
        eor     v0.16b, v0.16b, v2.16b
        ext     v3.16b, v4.16b, v1.16b, #2
        ext     v2.16b, v0.16b, v1.16b, #2
        orr     v3.16b, v3.16b, v4.16b
        eor     v2.16b, v2.16b, v0.16b
        ext     v0.16b, v3.16b, v1.16b, #1
        ext     v1.16b, v2.16b, v1.16b, #1
        orr     v0.16b, v0.16b, v3.16b
        eor     v1.16b, v1.16b, v2.16b
        umov    w1, v0.b[0]
        umov    w2, v1.b[0]
        neg     w1, w1
        eor     w1, w2, w1, asr #16
        cmp     w2, w1, uxtb
        mov     w0, #0xfffffffb
        csel    w0, wzr, w0, eq
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0x900000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #88]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L7f24
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #96
        ret
L7f24:
        bl      L0830
        nop
        nop

// mlkem768_keypair_derand (0x94 bytes)
L7f30:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        mov     x21, x0
        str     x30, [sp, #32]
        bl      L7684
        mov     x2, #0x4a0
        mov     w20, w0
        cbnz    w0, L7f94
        mov     x1, x21
        add     x0, x19, #0x480
        bl      L0810
        mov     x1, x21
        add     x0, x19, #0x920
        mov     x2, #0x4a0
        bl      L3730
        ldp     q0, q1, [x22, #32]
        add     x19, x19, #0x940
        mov     w0, w20
        stp     q0, q1, [x19]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L7f94:
        mov     x0, x21
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x960
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret

// mlkem768_keypair (0x8c bytes)
L7fc4:
        stp     x19, x20, [sp, #-128]!
        mov     x20, x0
        .inst   0x900000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x21, x30, [sp, #16]
        add     x19, sp, #0x3f
        and     x19, x19, #0xffffffffffffffe0
        mov     x21, x1
        ldr     x1, [x2]
        str     x1, [sp, #120]
        mov     x1, #0x0
        mov     x0, x19
        mov     x1, #0x40
        bl      L0820
        cbnz    w0, L8044
        mov     x1, x21
        mov     x0, x20
        mov     x2, x19
        bl      L7f30
L8010:
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xf00000a1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #120]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L804c
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #128
        ret
L8044:
        mov     w0, #0xfffffffd
        b       L8010
L804c:
        bl      L0830

// mlkem768_enc_derand (0xe0 bytes)
L8050:
        stp     x19, x20, [sp, #-224]!
        .inst   0xf00000a4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        stp     x21, x22, [sp, #16]
        add     x19, sp, #0x5f
        stp     x23, x24, [sp, #32]
        mov     x23, x1
        and     x19, x19, #0xffffffffffffffe0
        str     x30, [sp, #48]
        mov     x24, x0
        mov     x21, x2
        mov     x22, x3
        ldr     x1, [x4]
        str     x1, [sp, #216]
        mov     x1, #0x0
        mov     x0, x2
        add     x20, x19, #0x40
        bl      L7d00
        cbz     w0, L80e0
L809c:
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        .inst   0xf00000a1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #216]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L812c
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #224
        ret
L80e0:
        ldp     q0, q1, [x22]
        mov     x1, x21
        add     x0, x19, #0x60
        mov     x2, #0x4a0
        stp     q0, q1, [x20]
        bl      L3730
        mov     x1, x20
        mov     x0, x19
        mov     x2, #0x40
        bl      L37d0
        mov     x2, x21
        mov     x0, x24
        add     x3, x19, #0x20
        mov     x1, x20
        bl      L78d0
        cbnz    w0, L809c
        ldp     q0, q1, [x19]
        stp     q0, q1, [x23]
        b       L809c
L812c:
        bl      L0830

// mlkem768_enc (0x98 bytes)
L8130:
        stp     x19, x20, [sp, #-112]!
        mov     x20, x0
        .inst   0xf00000a3  // adrp x3, 0x1f000
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
        bl      L0820
        cbnz    w0, L81bc
        mov     x2, x22
        mov     x1, x21
        mov     x0, x20
        mov     x3, x19
        bl      L8050
L8188:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xf00000a1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #104]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L81c4
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret
L81bc:
        mov     w0, #0xfffffffd
        b       L8188
L81c4:
        bl      L0830
        nop
        nop

// mlkem768_dec (0x20c bytes)
L81d0:
        sub     sp, sp, #0x540
        .inst   0xf00000a3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x5f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        stp     x23, x24, [sp, #32]
        mov     x23, x0
        mov     x24, x2
        stp     x25, x30, [sp, #48]
        mov     x25, x1
        mov     x0, x2
        ldr     x1, [x3]
        str     x1, [sp, #1336]
        mov     x1, #0x0
        bl      L7e40
        cbz     w0, L8280
        mov     w20, w0
        add     x22, x19, #0x4a0
        add     x21, x19, #0x460
L8224:
        mov     x0, x19
        mov     x2, #0x460
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x22]
        stp     q0, q0, [x22, #32]
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1336]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L83d8
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        add     sp, sp, #0x540
        ret
L8280:
        add     x22, x19, #0x4a0
        mov     x2, x24
        mov     x0, x22
        mov     x1, x25
        add     x21, x19, #0x460
        bl      L7ba0
        mov     w20, w0
        cbnz    w0, L8224
        ldr     q0, [x24, #2336]
        add     x3, x19, #0x4c0
        ldr     q1, [x24, #2352]
        mov     x1, x22
        mov     x0, x21
        mov     x2, #0x40
        stp     q0, q1, [x3]
        bl      L37d0
        add     x3, x19, #0x480
        add     x2, x24, #0x480
        mov     x1, x22
        mov     x0, x19
        bl      L78d0
        mov     w20, w0
        cbnz    w0, L8224
        movi    v2.4s, #0x0
        mov     x0, x19
        mov     x1, x25
        add     x2, x19, #0x440
        mov     v3.16b, v2.16b
L82f0:
        ldr     q0, [x1], #16
        ldr     q1, [x0], #16
        eor     v0.16b, v0.16b, v1.16b
        orr     v3.16b, v3.16b, v0.16b
        eor     v2.16b, v2.16b, v0.16b
        cmp     x0, x2
        b.ne    L82f0
        movi    v1.4s, #0x0
        ext     v4.16b, v3.16b, v1.16b, #8
        ext     v0.16b, v2.16b, v1.16b, #8
        orr     v3.16b, v4.16b, v3.16b
        eor     v2.16b, v0.16b, v2.16b
        ext     v4.16b, v3.16b, v1.16b, #4
        ext     v0.16b, v2.16b, v1.16b, #4
        orr     v4.16b, v4.16b, v3.16b
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
        neg     w0, w0
        eor     w0, w1, w0, asr #16
        ldr     q0, [x24, #2368]
        and     w0, w0, #0xff
        ldr     q1, [x24, #2384]
        mov     x2, #0x440
        eor     w24, w0, w1
        mov     x1, x25
        add     x0, x19, #0x20
        stp     q0, q1, [x19]
        bl      L0810
        mov     x0, x23
        mov     x2, x19
        mov     x3, #0x460
        mov     x1, #0x20
        bl      L3650
        neg     w4, w24
        sub     x23, x23, #0x1
        mov     x0, #0x1
        nop
L83a8:
        add     x2, x21, x0
        mov     w1, w4
        ldurb   w2, [x2, #-1]
        ldrb    w3, [x23, x0]
        eor     w3, w2, w3
        and     w1, w3, w1, asr #16
        eor     w2, w2, w1
        strb    w2, [x23, x0]
        add     x0, x0, #0x1
        cmp     x0, #0x21
        b.ne    L83a8
        b       L8224
L83d8:
        bl      L0830
        nop

// mlkem768_polyvec_compress_du (0x34 bytes)
L83e0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L1fd0
        add     x1, x20, #0x200
        add     x0, x19, #0x140
        bl      L1fd0
        ldr     x30, [sp, #16]
        add     x1, x20, #0x400
        add     x0, x19, #0x280
        ldp     x19, x20, [sp], #32
        b       L1fd0

// mlkem768_polyvec_decompress_du (0x34 bytes)
L8414:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L23b0
        add     x1, x20, #0x140
        add     x0, x19, #0x200
        bl      L23b0
        ldr     x30, [sp, #16]
        add     x1, x20, #0x280
        add     x0, x19, #0x400
        ldp     x19, x20, [sp], #32
        b       L23b0
        nop
        nop

// mlkem768_polyvec_tobytes (0x34 bytes)
L8450:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L2870
        add     x1, x20, #0x200
        add     x0, x19, #0x180
        bl      L2870
        ldr     x30, [sp, #16]
        add     x1, x20, #0x400
        add     x0, x19, #0x300
        ldp     x19, x20, [sp], #32
        b       L2870

// mlkem768_polyvec_frombytes (0x34 bytes)
L8484:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L2aa4
        add     x1, x20, #0x180
        add     x0, x19, #0x200
        bl      L2aa4
        ldr     x30, [sp, #16]
        add     x1, x20, #0x300
        add     x0, x19, #0x400
        ldp     x19, x20, [sp], #32
        b       L2aa4
        nop
        nop

// mlkem768_polyvec_ntt (0x20 bytes)
L84c0:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L5b30
        add     x0, x19, #0x200
        bl      L5b30
        add     x0, x19, #0x400
        ldp     x19, x30, [sp], #16
        b       L5b30

// mlkem768_polyvec_invntt_tomont (0x20 bytes)
L84e0:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L5e30
        add     x0, x19, #0x200
        bl      L5e30
        add     x0, x19, #0x400
        ldp     x19, x30, [sp], #16
        b       L5e30

// mlkem768_polyvec_basemul_acc_montgomery_cached (0x204 bytes)
L8500:
        mov     x6, x3
        stp     x19, x30, [sp, #-48]!
        add     x3, x0, #0x200
        mov     x5, x0
        cmp     x6, x3
        add     x3, x6, #0x300
        mov     x0, x1
        ccmp    x5, x3, #0x2, cc
        mov     x1, x2
        b.cc    L862c
        .inst   0x90000002  // adrp x2, 0x8000
        add     x7, x6, #0x200
        mvni    v4.8h, #0xd, lsl #8
        stp     d8, d9, [sp, #16]
        ldr     q5, [x2, #2336]
        mov     x2, x0
        add     x0, x6, #0x100
        stp     d10, d11, [sp, #32]
L8548:
        add     x3, x2, #0x200
        add     x6, x1, #0x200
        add     x4, x2, #0x400
        ld2     {v28.8h-v29.8h}, [x2]
        add     x2, x2, #0x20
        ld2     {v22.8h-v23.8h}, [x3]
        add     x3, x1, #0x400
        ld2     {v30.8h-v31.8h}, [x1]
        add     x1, x1, #0x20
        ld2     {v24.8h-v25.8h}, [x6]
        smull2  v3.4s, v31.8h, v28.8h
        smull   v0.4s, v31.4h, v28.4h
        smull2  v1.4s, v24.8h, v22.8h
        smull   v2.4s, v24.4h, v22.4h
        ld2     {v16.8h-v17.8h}, [x4]
        ld2     {v18.8h-v19.8h}, [x3]
        smlal2  v1.4s, v30.8h, v28.8h
        smlal   v2.4s, v30.4h, v28.4h
        smlal2  v3.4s, v30.8h, v29.8h
        smlal   v0.4s, v30.4h, v29.4h
        ldur    q8, [x0, #-256]
        add     x0, x0, #0x10
        smlal2  v1.4s, v16.8h, v18.8h
        smlal   v2.4s, v16.4h, v18.4h
        smlal2  v3.4s, v25.8h, v22.8h
        smlal   v0.4s, v25.4h, v22.4h
        ldur    q10, [x0, #-16]
        smlal2  v3.4s, v24.8h, v23.8h
        smlal   v0.4s, v24.4h, v23.4h
        smlal2  v1.4s, v8.8h, v29.8h
        smlal   v2.4s, v8.4h, v29.4h
        ldr     q9, [x0, #240]
        smlal   v0.4s, v16.4h, v19.4h
        smlal2  v3.4s, v16.8h, v19.8h
        smlal2  v1.4s, v10.8h, v23.8h
        smlal   v2.4s, v10.4h, v23.4h
        smlal   v0.4s, v17.4h, v18.4h
        smlal2  v3.4s, v17.8h, v18.8h
        smlal2  v1.4s, v17.8h, v9.8h
        smlal   v2.4s, v17.4h, v9.4h
        uzp1    v16.8h, v0.8h, v3.8h
        uzp1    v20.8h, v2.8h, v1.8h
        mul     v16.8h, v16.8h, v5.8h
        mul     v17.8h, v20.8h, v5.8h
        smlal   v0.4s, v16.4h, v4.4h
        smlal2  v3.4s, v16.8h, v4.8h
        smlal   v2.4s, v17.4h, v4.4h
        smlal2  v1.4s, v17.8h, v4.8h
        uzp2    v7.8h, v0.8h, v3.8h
        uzp2    v6.8h, v2.8h, v1.8h
        st2     {v6.8h-v7.8h}, [x5], #32
        cmp     x0, x7
        b.ne    L8548
        ldp     d8, d9, [sp, #16]
        ldp     d10, d11, [sp, #32]
        ldp     x19, x30, [sp], #48
        ret
L862c:
        mov     x7, x5
        add     x11, x0, #0x200
        mov     w10, #0xfffff301
        mov     w9, #0xfffff2ff
        nop
L8640:
        ldrsh   w4, [x1]
        add     x0, x0, #0x4
        ldursh  w18, [x0, #-4]
        add     x6, x6, #0x2
        ldrsh   w2, [x1, #512]
        add     x7, x7, #0x4
        ldursh  w12, [x0, #-2]
        add     x1, x1, #0x4
        ldrsh   w8, [x0, #510]
        ldrsh   w30, [x0, #508]
        mul     w13, w4, w18
        ldursh  w14, [x6, #-2]
        ldrsh   w3, [x6, #254]
        mul     w15, w4, w12
        ldrsh   w17, [x0, #1022]
        mul     w5, w2, w8
        ldrsh   w16, [x0, #1020]
        mul     w19, w2, w30
        ldrsh   w4, [x1, #1020]
        madd    w14, w14, w12, w13
        ldrsh   w2, [x1, #510]
        madd    w3, w3, w8, w19
        ldursh  w13, [x1, #-2]
        ldrsh   w12, [x6, #510]
        add     w3, w3, w14
        ldrsh   w8, [x1, #1022]
        mul     w19, w4, w16
        madd    w2, w2, w30, w5
        mul     w4, w4, w17
        madd    w13, w13, w18, w15
        madd    w5, w12, w17, w19
        madd    w4, w8, w16, w4
        add     w2, w2, w13
        add     w3, w3, w5
        add     w2, w2, w4
        mul     w5, w3, w10
        mul     w4, w2, w10
        sxth    w5, w5
        sxth    w4, w4
        madd    w3, w5, w9, w3
        madd    w2, w4, w9, w2
        asr     w3, w3, #16
        sturh   w3, [x7, #-4]
        asr     w2, w2, #16
        sturh   w2, [x7, #-2]
        cmp     x0, x11
        b.ne    L8640
        ldp     x19, x30, [sp], #48
        ret

// mlkem768_polyvec_mulcache_compute (0x34 bytes)
L8704:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L5710
        add     x1, x20, #0x200
        add     x0, x19, #0x100
        bl      L5710
        ldr     x30, [sp, #16]
        add     x1, x20, #0x400
        add     x0, x19, #0x200
        ldp     x19, x20, [sp], #32
        b       L5710
        nop
        nop

// mlkem768_polyvec_reduce (0x20 bytes)
L8740:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L5660
        add     x0, x19, #0x200
        bl      L5660
        add     x0, x19, #0x400
        ldp     x19, x30, [sp], #16
        b       L5660

// mlkem768_polyvec_add (0x34 bytes)
L8760:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L56b0
        add     x1, x20, #0x200
        add     x0, x19, #0x200
        bl      L56b0
        ldr     x30, [sp, #16]
        add     x1, x20, #0x400
        add     x0, x19, #0x400
        ldp     x19, x20, [sp], #32
        b       L56b0

// mlkem768_polyvec_tomont (0x20 bytes)
L8794:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L5610
        add     x0, x19, #0x200
        bl      L5610
        add     x0, x19, #0x400
        ldp     x19, x30, [sp], #16
        b       L5610

// mlkem768_poly_getnoise_eta1_4x (0x158 bytes)
L87b4:
        sub     sp, sp, #0x380
        stp     x19, x20, [sp, #16]
        add     x20, sp, #0x7f
        and     x20, x20, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        add     x10, x20, #0x240
        add     x9, x20, #0x280
        stp     x23, x24, [sp, #48]
        add     x19, x20, #0x200
        mov     x22, x2
        stp     x25, x26, [sp, #64]
        add     x8, x20, #0x2c0
        add     x25, x20, #0x100
        stp     x27, x30, [sp, #80]
        add     x27, x20, #0x180
        mov     x21, x3
        ldp     q0, q1, [x4]
        mov     x3, x27
        .inst   0xf00000a4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        mov     x24, x0
        mov     x23, x1
        mov     x0, x20
        ldr     x2, [x4]
        str     x2, [sp, #888]
        mov     x2, #0x0
        stp     q0, q1, [x9]
        mov     x2, x25
        stp     q0, q1, [x10]
        mov     x4, #0x80
        add     x26, x20, x4
        strb    w5, [x19, #32]
        mov     x5, x19
        strb    w6, [x19, #96]
        mov     x6, x10
        strb    w7, [x19, #160]
        mov     x7, x9
        mov     x9, #0x21
        stp     x8, x9, [sp]
        ldrb    w9, [sp, #896]
        stp     q0, q1, [x8]
        mov     x1, x26
        strb    w9, [x19, #224]
        stp     q0, q1, [x19]
        bl      L3b80
        mov     x1, x20
        mov     x0, x24
        bl      L6fe0
        mov     x1, x26
        mov     x0, x23
        bl      L6fe0
        mov     x1, x25
        mov     x0, x22
        bl      L6fe0
        cbz     x21, L889c
        mov     x1, x27
        mov     x0, x21
        bl      L6fe0
L889c:
        mov     x0, x20
        mov     x2, #0x200
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        stp     q0, q0, [x19, #192]
        stp     q0, q0, [x19, #224]
        .inst   0xf00000a0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #888]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L8908
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x30, [sp, #80]
        add     sp, sp, #0x380
        ret
L8908:
        bl      L0830

// Padding (0x890c to 0x8920)

        .long   0x00000000
        .long   0x00000000
        .long   0x00000000
        .long   0x00000000
        .long   0x00000000

// The read-only data (0x8920 to 0x8c80)

        .quad   0xf301f301f301f301
        .quad   0xf301f301f301f301
        .quad   0x0013afb00013afb0
        .quad   0x0013afb00013afb0
        .quad   0x0d010d010d010d01
        .quad   0x0d010d010d010d01
        .quad   0x0013afb80013afb8
        .quad   0x0013afb80013afb8
        .quad   0x0549054905490549
        .quad   0x0549054905490549
        .quad   0x034b022b01aefbb1
        .quad   0x0069060e0367fb1d
        .quad   0xfcb5fdd5fe52044f
        .quad   0xff97f9f2fc9904e3
        .quad   0xff1500b1024b01a6
        .quad   0x06750626fe34fedd
        .quad   0x00ebff4ffdb5fe5a
        .quad   0xf98bf9da01cc0123
        .quad   0xff6d0487030aff0a
        .quad   0x045ffda605cbfcf7
        .quad   0x0093fb79fcf600f6
        .quad   0xfba1025afa350309
        .quad   0x015dfc980284f9ca
        .quad   0xffb5ff64014901a2
        .quad   0xfea30368fd7c0636
        .quad   0x004b009cfeb7fe5e
        .quad   0x0262025b04490331
        .quad   0x0180fa47fafb052a
        .quad   0xfd9efda5fbb7fccf
        .quad   0xfe8005b90505fad6
        .quad   0xfac904c2ff78fb41
        .quad   0xf985fb5d00dcfc96
        .quad   0x0537fb3e008804bf
        .quad   0x067b04a3ff24036a
        .quad   0x031afb02fa06fb5f
        .quad   0x01defc9afcaafa1a
        .quad   0xfce604fe05fa04a1
        .quad   0xfe220366035605e6
        .quad   0xfffffeccffffff94
        .quad   0x000003df000003e4
        .quad   0x000001340000006c
        .quad   0xfffffc21fffffc1c
        .quad   0x05b4fa4cfc4203be
        .quad   0xf9a4065cfa0e05f2
        .quad   0x05a105a105a105a1
        .quad   0x05a105a105a105a1
        .quad   0x4ebf4ebf4ebf4ebf
        .quad   0x4ebf4ebf4ebf4ebf
        .quad   0x0024924900249249
        .quad   0x0024924900249249
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
        .quad   0x0000000000000000
        .quad   0x0000000000000000
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
