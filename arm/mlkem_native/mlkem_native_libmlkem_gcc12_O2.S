// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// The code and read-only data of mlkem-native's libmlkem.so (gcc 12, -O2)
//
// This is a transcription of the binary binaries/multilevel/gcc12/O2/
// libmlkem.so from the binary branch of mlkem-native (see README.md), as
// loaded at an address that is a multiple of 4096: the start of its first
// segment, from address 0 up to the end of the read-only data. The ELF
// header and dynamic linking information at the start are given as data,
// as are the padding and the read-only data at the end, while the
// procedure linkage table and the code are given as instructions. The ADRP
// instructions, which compute addresses of pages relative to that of the
// instruction, are given as words, as are the branches to addresses outside
// the code. The labels are named after the addresses in the binary.
// ----------------------------------------------------------------------------

        .text
        .balign 4

// ELF header and dynamic linking information (0x0 to 0x7f0)

        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x0000000100b70003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x0000000000026570
        .quad   0x0038004000000000
        .quad   0x0019001a00400005
        .quad   0x0000000500000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x00000000000076ec
        .quad   0x00000000000076ec
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
        .quad   0x0000000000003f30
        .quad   0x000000000000020c
        .quad   0x000800120000003e
        .quad   0x0000000000001150
        .quad   0x00000000000000e8
        .quad   0x000800120000010d
        .quad   0x0000000000003db0
        .quad   0x00000000000000e0
        .quad   0x00080012000001a9
        .quad   0x0000000000005c10
        .quad   0x000000000000020c
        .quad   0x000800120000014d
        .quad   0x0000000000005880
        .quad   0x00000000000000e8
        .quad   0x0008001200000071
        .quad   0x00000000000012d4
        .quad   0x000000000000008c
        .quad   0x000800120000002b
        .quad   0x0000000000001010
        .quad   0x0000000000000138
        .quad   0x00080012000000a4
        .quad   0x0000000000001440
        .quad   0x0000000000000098
        .quad   0x00080012000000e4
        .quad   0x0000000000003c90
        .quad   0x0000000000000094
        .quad   0x000800120000013b
        .quad   0x0000000000005740
        .quad   0x0000000000000138
        .quad   0x0008001200000177
        .quad   0x0000000000005a04
        .quad   0x000000000000008c
        .quad   0x000800120000008f
        .quad   0x0000000000001360
        .quad   0x00000000000000e0
        .quad   0x000800120000015f
        .quad   0x0000000000005970
        .quad   0x0000000000000094
        .quad   0x0008001200000121
        .quad   0x0000000000003e90
        .quad   0x0000000000000098
        .quad   0x00080012000000d2
        .quad   0x0000000000003ba0
        .quad   0x00000000000000e8
        .quad   0x0008001200000188
        .quad   0x0000000000005a90
        .quad   0x00000000000000e0
        .quad   0x000800120000019c
        .quad   0x0000000000005b70
        .quad   0x0000000000000098
        .quad   0x00080012000000c0
        .quad   0x0000000000003a60
        .quad   0x0000000000000138
        .quad   0x00080012000000b2
        .quad   0x00000000000014e0
        .quad   0x000000000000020c
        .quad   0x00080012000000fc
        .quad   0x0000000000003d24
        .quad   0x000000000000008c
        .quad   0x0008001200000051
        .quad   0x0000000000001240
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

// The procedure linkage table and the code (0x7f0 to 0x61f8)
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

// mlkem1024_gen_matrix (0x14c bytes)
L0850:
        stp     x19, x20, [sp, #-368]!
        .inst   0xf00000e4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        add     x20, sp, #0x6f
        stp     x21, x22, [sp, #16]
        and     x20, x20, #0xffffffffffffffe0
        mov     x3, x20
        stp     x23, x24, [sp, #32]
        mov     x24, x0
        add     x0, x20, #0x100
        stp     x25, x26, [sp, #48]
        mov     w25, w2
        str     x30, [sp, #64]
        ldr     x2, [x4]
        str     x2, [sp, #360]
        mov     x2, #0x0
L0890:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x3]
        add     x3, x3, #0x40
        cmp     x0, x3
        b.ne    L0890
        mov     w19, #0x4
        mov     w26, #0x800
        mov     x23, #0x600
        mov     x22, #0x400
        mov     x21, #0x200
L08b8:
        sub     w0, w19, #0x4
        mov     x6, x20
        mov     w1, w0
L08c4:
        and     w5, w1, #0x3
        ubfx    x3, x1, #2, #8
        cmp     w25, #0x0
        mov     w4, w5
        add     w1, w1, #0x1
        csel    w5, w5, w3, eq
        csel    w3, w3, w4, eq
        strb    w5, [x6, #32]
        strb    w3, [x6, #33]
        add     x6, x6, #0x40
        cmp     w19, w1
        b.ne    L08c4
        sub     w3, w19, #0x1
        sub     w2, w19, #0x2
        sub     w1, w19, #0x3
        lsr     w0, w0, #2
        lsr     w3, w3, #2
        lsr     w2, w2, #2
        lsr     w1, w1, #2
        add     w19, w19, #0x4
        add     x0, x24, x0, lsl #11
        mov     x4, x20
        umaddl  x3, w3, w26, x23
        umaddl  x2, w2, w26, x22
        umaddl  x1, w1, w26, x21
        add     x3, x24, x3
        add     x2, x24, x2
        add     x1, x24, x1
        bl      L4b30
        cmp     w19, #0x14
        b.ne    L08b8
        movi    v0.4s, #0x0
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        stp     q0, q0, [x20, #64]
        stp     q0, q0, [x20, #96]
        stp     q0, q0, [x20, #128]
        stp     q0, q0, [x20, #160]
        stp     q0, q0, [x20, #192]
        stp     q0, q0, [x20, #224]
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #360]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L0998
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #368
        ret
L0998:
        bl      L0830
        nop

// mlkem1024_indcpa_keypair_derand (0x238 bytes)
L09a0:
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
        bl      L26f4
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
        bl      L19e0
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
        bl      L19e0
        mov     x19, x25
        mov     x0, x20
        bl      L17f0
        mov     x0, x23
        bl      L17f0
        mov     x1, x20
        mov     x0, x26
        bl      L1900
L0abc:
        mov     x1, x28
        mov     x0, x19
        mov     x3, x26
        mov     x2, x20
        add     x19, x19, #0x200
        bl      L1850
        add     x28, x28, #0x800
        cmp     x19, x23
        b.ne    L0abc
        mov     x0, x25
        bl      L19b0
        mov     x1, x19
        mov     x0, x25
        bl      L1970
        mov     x0, x25
        bl      L1940
        mov     x0, x20
        bl      L1940
        ldr     x0, [sp, #120]
        mov     x1, x20
        bl      L1770
        mov     x1, x25
        mov     x0, x27
        bl      L1770
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
        b.ne    L0bd4
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
L0bd4:
        bl      L0830
        nop
        nop

// mlkem1024_indcpa_enc (0x2c8 bytes)
L0be0:
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
        bl      L17b0
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
        bl      L22e0
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
        bl      L19e0
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
        bl      L19e0
        mov     x1, x21
        mov     w2, #0x8
        mov     x0, x28
        bl      L1b40
        add     x21, x19, #0x2, lsl #12
        mov     x0, x20
        bl      L17f0
        mov     x27, x21
        add     x22, x21, #0x800
        mov     x1, x20
        mov     x0, x23
        bl      L1900
L0d20:
        mov     x1, x26
        mov     x0, x27
        mov     x3, x23
        mov     x2, x20
        add     x27, x27, #0x200
        bl      L1850
        add     x26, x26, #0x800
        cmp     x27, x22
        b.ne    L0d20
        ldr     x27, [sp, #128]
        mov     x3, x23
        mov     x2, x20
        mov     x0, #0x4800
        mov     x1, x27
        add     x22, x19, x0
        mov     x0, x22
        bl      L1850
        mov     x0, x21
        bl      L1820
        mov     x0, x22
        bl      L4394
        mov     x1, x24
        mov     x0, x21
        bl      L1970
        mov     x1, x28
        mov     x0, x22
        bl      L41e0
        ldr     x26, [sp, #136]
        mov     x0, x22
        mov     x1, x26
        bl      L41e0
        mov     x0, x21
        bl      L1940
        mov     x0, x22
        bl      L4190
        ldr     x0, [sp, #120]
        mov     x1, x21
        bl      L16f0
        ldr     x0, [sp, #120]
        mov     x1, x22
        add     x0, x0, #0x580
        bl      L1e74
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
        b.ne    L0ea4
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
L0ea4:
        bl      L0830
        nop
        nop

// mlkem1024_indcpa_dec (0x158 bytes)
L0eb0:
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
        bl      L1730
        add     x1, x23, #0x580
        mov     x0, x21
        bl      L20b0
        add     x23, x19, #0x1, lsl #12
        mov     x1, x22
        mov     x0, x19
        bl      L17b0
        mov     x0, x20
        bl      L17f0
        mov     x3, #0x1400
        mov     x1, x20
        add     x22, x19, x3
        mov     x0, x23
        bl      L1900
        mov     x3, x23
        mov     x2, x20
        mov     x1, x19
        mov     x0, x22
        bl      L1850
        mov     x0, x22
        bl      L4394
        mov     x1, x22
        mov     x0, x21
        bl      L4210
        mov     x0, x21
        bl      L4190
        mov     x1, x21
        mov     x0, x24
        bl      L2340
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
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #6232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L1004
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x1860
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        add     sp, sp, x12
        ret
L1004:
        bl      L0830
        nop
        nop

// mlkem1024_check_pk (0x138 bytes)
L1010:
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
        bl      L17b0
        mov     x0, x20
        bl      L1940
        mov     x0, x21
        mov     x1, x20
        bl      L1770
        movi    v2.4s, #0x0
        mov     x0, x19
        mov     x2, x21
        add     x1, x20, #0xe00
        mov     v3.16b, v2.16b
        nop
L1078:
        ldr     q0, [x0], #16
        ldr     q1, [x2], #16
        eor     v0.16b, v0.16b, v1.16b
        orr     v3.16b, v3.16b, v0.16b
        eor     v2.16b, v2.16b, v0.16b
        cmp     x1, x2
        b.ne    L1078
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
        b.ne    L1144
        ldp     x21, x30, [sp, #16]
        mov     w0, w19
        ldp     x19, x20, [sp]
        add     sp, sp, #0xe40
        ret
L1144:
        bl      L0830
        nop
        nop

// mlkem1024_check_sk (0xe8 bytes)
L1150:
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
        bl      L2650
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
        b.ne    L1234
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #96
        ret
L1234:
        bl      L0830
        nop
        nop

// mlkem1024_keypair_derand (0x94 bytes)
L1240:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        mov     x21, x0
        str     x30, [sp, #32]
        bl      L09a0
        mov     x2, #0x620
        mov     w20, w0
        cbnz    w0,L12a4
        mov     x1, x21
        add     x0, x19, #0x600
        bl      L0810
        mov     x1, x21
        add     x0, x19, #0xc20
        mov     x2, #0x620
        bl      L2650
        ldp     q0, q1, [x22, #32]
        add     x19, x19, #0xc40
        mov     w0, w20
        stp     q0, q1, [x19]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L12a4:
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
L12d4:
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
        cbnz    w0,L1354
        mov     x1, x21
        mov     x0, x20
        mov     x2, x19
        bl      L1240
L1320:
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xd00000e1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #120]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L135c
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #128
        ret
L1354:
        mov     w0, #0xfffffffd
        b       L1320
L135c:
        bl      L0830

// mlkem1024_enc_derand (0xe0 bytes)
L1360:
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
        bl      L1010
        cbz     w0,L13f0
L13ac:
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
        b.ne    L143c
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #224
        ret
L13f0:
        ldp     q0, q1, [x22]
        mov     x1, x21
        add     x0, x19, #0x60
        mov     x2, #0x620
        stp     q0, q1, [x20]
        bl      L2650
        mov     x1, x20
        mov     x0, x19
        mov     x2, #0x40
        bl      L26f4
        mov     x2, x21
        mov     x0, x24
        add     x3, x19, #0x20
        mov     x1, x20
        bl      L0be0
        cbnz    w0,L13ac
        ldp     q0, q1, [x19]
        stp     q0, q1, [x23]
        b       L13ac
L143c:
        bl      L0830

// mlkem1024_enc (0x98 bytes)
L1440:
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
        cbnz    w0,L14cc
        mov     x2, x22
        mov     x1, x21
        mov     x0, x20
        mov     x3, x19
        bl      L1360
L1498:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xd00000e1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #104]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L14d4
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret
L14cc:
        mov     w0, #0xfffffffd
        b       L1498
L14d4:
        bl      L0830
        nop
        nop

// mlkem1024_dec (0x20c bytes)
L14e0:
        sub     sp, sp, #0x720
        .inst   0xd00000e3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x5f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        stp     x23, x24, [sp, #32]
        mov     x24, x0
        mov     x23, x2
        stp     x25, x30, [sp, #48]
        mov     x25, x1
        mov     x0, x2
        ldr     x1, [x3]
        str     x1, [sp, #1816]
        mov     x1, #0x0
        bl      L1150
        cbz     w0,L1590
        mov     w20, w0
        add     x22, x19, #0x680
        add     x21, x19, #0x640
L1534:
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
        b.ne    L16e8
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        add     sp, sp, #0x720
        ret
L1590:
        add     x22, x19, #0x680
        mov     x2, x23
        mov     x0, x22
        mov     x1, x25
        add     x21, x19, #0x640
        bl      L0eb0
        mov     w20, w0
        cbnz    w0,L1534
        ldr     q0, [x23, #3104]
        add     x3, x19, #0x6a0
        ldr     q1, [x23, #3120]
        mov     x1, x22
        mov     x0, x21
        mov     x2, #0x40
        stp     q0, q1, [x3]
        bl      L26f4
        add     x3, x19, #0x660
        add     x2, x23, #0x600
        mov     x1, x22
        mov     x0, x19
        bl      L0be0
        mov     w20, w0
        cbnz    w0,L1534
        movi    v2.4s, #0x0
        mov     x0, x19
        mov     x1, x25
        add     x2, x19, #0x620
        mov     v3.16b, v2.16b
L1600:
        ldr     q0, [x1], #16
        ldr     q1, [x0], #16
        eor     v0.16b, v0.16b, v1.16b
        orr     v3.16b, v3.16b, v0.16b
        eor     v2.16b, v2.16b, v0.16b
        cmp     x0, x2
        b.ne    L1600
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
        ldr     q0, [x23, #3136]
        and     w0, w0, #0xff
        ldr     q1, [x23, #3152]
        mov     x2, #0x620
        eor     w23, w0, w1
        mov     x1, x25
        add     x0, x19, #0x20
        stp     q0, q1, [x19]
        bl      L0810
        mov     x0, x24
        mov     x2, x19
        mov     x3, #0x640
        mov     x1, #0x20
        bl      L2570
        neg     w4, w23
        sub     x24, x24, #0x1
        mov     x0, #0x1
        nop
L16b8:
        add     x2, x21, x0
        mov     w1, w4
        ldurb   w2, [x2, #-1]
        ldrb    w3, [x24, x0]
        eor     w3, w2, w3
        and     w1, w3, w1, asr #16
        eor     w2, w2, w1
        strb    w2, [x24, x0]
        add     x0, x0, #0x1
        cmp     x0, #0x21
        b.ne    L16b8
        b       L1534
L16e8:
        bl      L0830
        nop

// mlkem1024_polyvec_compress_du (0x3c bytes)
L16f0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x580
L1704:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x160
        bl      L1f74
        add     x20, x20, #0x200
        cmp     x19, x21
        b.ne    L1704
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop

// mlkem1024_polyvec_decompress_du (0x3c bytes)
L1730:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x30, [sp, #16]
        add     x21, x1, #0x580
L1744:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x160
        bl      L2170
        add     x20, x20, #0x200
        cmp     x19, x21
        b.ne    L1744
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop

// mlkem1024_polyvec_tobytes (0x3c bytes)
L1770:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x600
L1784:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x180
        bl      L2260
        add     x20, x20, #0x200
        cmp     x19, x21
        b.ne    L1784
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop

// mlkem1024_polyvec_frombytes (0x3c bytes)
L17b0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x1
        mov     x20, x0
        stp     x21, x30, [sp, #16]
        add     x21, x1, #0x600
L17c4:
        mov     x1, x19
        mov     x0, x20
        add     x19, x19, #0x180
        bl      L22a0
        add     x20, x20, #0x200
        cmp     x19, x21
        b.ne    L17c4
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop

// mlkem1024_polyvec_ntt (0x28 bytes)
L17f0:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L42b4
        add     x0, x19, #0x200
        bl      L42b4
        add     x0, x19, #0x400
        bl      L42b4
        add     x0, x19, #0x600
        ldp     x19, x30, [sp], #16
        b       L42b4
        nop
        nop

// mlkem1024_polyvec_invntt_tomont (0x28 bytes)
L1820:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L4394
        add     x0, x19, #0x200
        bl      L4394
        add     x0, x19, #0x400
        bl      L4394
        add     x0, x19, #0x600
        ldp     x19, x30, [sp], #16
        b       L4394
        nop
        nop

// mlkem1024_polyvec_basemul_acc_montgomery_cached (0xac bytes)
L1850:
        add     x7, x0, #0x2
        mov     x6, x1
        add     x5, x2, #0x2
        add     x12, x3, #0x100
        mov     w9, #0xfffff301
        mov     w8, #0xfffff2ff
L1868:
        mov     x1, x3
        add     x11, x6, #0x2
        sub     x10, x5, #0x2
        mov     x0, #0x0
        mov     w4, #0x0
        mov     w2, #0x0
L1880:
        ldrsh   w17, [x11, x0]
        add     x1, x1, #0x100
        ldrsh   w16, [x6, x0]
        ldrsh   w13, [x10, x0]
        ldrsh   w14, [x5, x0]
        add     x0, x0, #0x200
        ldursh  w15, [x1, #-256]
        mul     w18, w16, w13
        mul     w13, w17, w13
        madd    w15, w15, w17, w18
        madd    w13, w14, w16, w13
        add     w2, w2, w15
        add     w4, w4, w13
        cmp     x0, #0x800
        b.ne    L1880
        mul     w1, w2, w9
        add     x3, x3, #0x2
        mul     w0, w4, w9
        add     x6, x6, #0x4
        add     x5, x5, #0x4
        sxth    w1, w1
        sxth    w0, w0
        madd    w1, w1, w8, w2
        madd    w0, w0, w8, w4
        asr     w1, w1, #16
        sturh   w1, [x7, #-2]
        asr     w0, w0, #16
        strh    w0, [x7], #4
        cmp     x12, x3
        b.ne    L1868
        ret
        nop

// mlkem1024_polyvec_mulcache_compute (0x3c bytes)
L1900:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        stp     x21, x30, [sp, #16]
        add     x21, x0, #0x400
L1914:
        mov     x1, x20
        mov     x0, x19
        add     x19, x19, #0x100
        bl      L4240
        add     x20, x20, #0x200
        cmp     x19, x21
        b.ne    L1914
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop

// mlkem1024_polyvec_reduce (0x28 bytes)
L1940:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L4190
        add     x0, x19, #0x200
        bl      L4190
        add     x0, x19, #0x400
        bl      L4190
        add     x0, x19, #0x600
        ldp     x19, x30, [sp], #16
        b       L4190
        nop
        nop

// mlkem1024_polyvec_add (0x38 bytes)
L1970:
        stp     x19, x20, [sp, #-32]!
        mov     x20, x1
        mov     x19, #0x0
        stp     x21, x30, [sp, #16]
        mov     x21, x0
L1984:
        add     x1, x20, x19
        add     x0, x21, x19
        add     x19, x19, #0x200
        bl      L41e0
        cmp     x19, #0x800
        b.ne    L1984
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
        nop
        nop

// mlkem1024_polyvec_tomont (0x28 bytes)
L19b0:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L4140
        add     x0, x19, #0x200
        bl      L4140
        add     x0, x19, #0x400
        bl      L4140
        add     x0, x19, #0x600
        ldp     x19, x30, [sp], #16
        b       L4140
        nop
        nop

// mlkem1024_poly_getnoise_eta1_4x (0x158 bytes)
L19e0:
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
        bl      L2a20
        mov     x1, x20
        mov     x0, x24
        bl      L4e40
        mov     x1, x26
        mov     x0, x23
        bl      L4e40
        mov     x1, x25
        mov     x0, x22
        bl      L4e40
        cbz     x21,L1ac8
        mov     x1, x27
        mov     x0, x21
        bl      L4e40
L1ac8:
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
        b.ne    L1b34
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x30, [sp, #80]
        add     sp, sp, #0x380
        ret
L1b34:
        bl      L0830
        nop
        nop

// mlkem1024_poly_getnoise_eta2 (0xa4 bytes)
L1b40:
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
        bl      L2570
        mov     x1, x19
        mov     x0, x21
        bl      L4e40
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
        b.ne    L1be0
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #240
        ret
L1be0:
        bl      L0830
        nop
        nop
        nop

// mlkem_poly_compress_d4 (0xdc bytes)
L1bf0:
        .inst   0xd00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        mov     x10, x1
        mov     w12, #0xafb0
        ldr     x1, [x2]
        str     x1, [sp, #24]
        mov     x1, #0x0
        add     x13, sp, #0x10
        movk    w12, #0x13, lsl #16
        mov     w11, #0x8000000
        nop
L1c20:
        sub     w3, w1, #0x1
        mov     x2, #0x1
        str     xzr, [sp, #16]
        nop
L1c30:
        add     w4, w3, w2
        add     x5, x13, x2
        add     x2, x2, #0x1
        ldrsh   w4, [x10, x4, lsl #1]
        madd    w4, w4, w12, w11
        lsr     w4, w4, #28
        sturb   w4, [x5, #-1]
        cmp     x2, #0x9
        b.ne    L1c30
        ldrb    w9, [sp, #16]
        add     w1, w1, #0x8
        ldrb    w8, [sp, #18]
        add     x0, x0, #0x4
        ldrb    w7, [sp, #20]
        ldrb    w6, [sp, #22]
        ldrb    w5, [sp, #17]
        ldrb    w4, [sp, #19]
        ldrb    w3, [sp, #21]
        ldrb    w2, [sp, #23]
        orr     w5, w9, w5, lsl #4
        orr     w4, w8, w4, lsl #4
        sturb   w5, [x0, #-4]
        orr     w3, w7, w3, lsl #4
        sturb   w4, [x0, #-3]
        orr     w2, w6, w2, lsl #4
        sturb   w3, [x0, #-2]
        sturb   w2, [x0, #-1]
        cmp     w1, #0x100
        b.ne    L1c20
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L1cc8
        ldr     x30, [sp], #32
        ret
L1cc8:
        bl      L0830
        nop

// mlkem_poly_compress_d10 (0xd4 bytes)
L1cd0:
        .inst   0xd00000e3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        str     x30, [sp, #-32]!
        mov     x8, #0xbc00
        mov     x6, x1
        add     x12, sp, #0x10
        mov     x2, x0
        movk    x8, #0x9d7d, lsl #16
        ldr     x0, [x3]
        str     x0, [sp, #24]
        mov     x0, #0x0
        mov     x7, #0x100000000
        mov     w3, #0x4
        nop
L1d08:
        sub     w1, w3, #0x4
        mov     x4, x12
L1d10:
        ldrsh   x0, [x6, w1, uxtw #1]
        add     w1, w1, #0x1
        madd    x0, x0, x8, x7
        ubfx    x0, x0, #33, #10
        strh    w0, [x4], #2
        cmp     w3, w1
        b.ne    L1d10
        ldrh    w4, [sp, #18]
        add     w3, w3, #0x4
        ldrh    w1, [sp, #20]
        add     x2, x2, #0x5
        ldrh    w0, [sp, #22]
        ldrh    w5, [sp, #16]
        lsl     w9, w4, #2
        lsl     w11, w1, #4
        sturb   w5, [x2, #-5]
        lsl     w10, w0, #6
        orr     w4, w11, w4, lsr #6
        orr     w1, w10, w1, lsr #4
        lsr     w0, w0, #2
        orr     w5, w9, w5, lsr #8
        sturb   w5, [x2, #-4]
        sturb   w4, [x2, #-3]
        sturb   w1, [x2, #-2]
        sturb   w0, [x2, #-1]
        cmp     w3, #0x104
        b.ne    L1d08
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L1da0
        ldr     x30, [sp], #32
        ret
L1da0:
        bl      L0830

// mlkem_poly_decompress_d4 (0x4c bytes)
L1da4:
        add     x4, x0, #0x200
        mov     w3, #0xd01
        nop
L1db0:
        ldrb    w2, [x1]
        add     x0, x0, #0x4
        and     w2, w2, #0xf
        mul     w2, w2, w3
        add     w2, w2, #0x8
        lsr     w2, w2, #4
        sturh   w2, [x0, #-4]
        ldrb    w2, [x1], #1
        lsr     w2, w2, #4
        mul     w2, w2, w3
        add     w2, w2, #0x8
        lsr     w2, w2, #4
        sturh   w2, [x0, #-2]
        cmp     x4, x0
        b.ne    L1db0
        ret

// mlkem_poly_decompress_d10 (0x84 bytes)
L1df0:
        mov     x5, x0
        .inst   0xb0000020  // adrp x0, 0x6000
        movi    v2.4s, #0x2, lsl #8
        add     x7, x1, #0x140
        ldr     q3, [x0, #512]
        nop
L1e08:
        add     x1, x1, #0x5
        ldurb   w2, [x1, #-3]
        ldurb   w3, [x1, #-4]
        ldurh   w0, [x1, #-5]
        lsl     w6, w2, #6
        ldurb   w4, [x1, #-2]
        orr     w3, w6, w3, lsr #2
        and     w0, w0, #0x3ff
        fmov    s0, w0
        and     w0, w3, #0x3ff
        lsl     w6, w4, #4
        ldurb   w3, [x1, #-1]
        mov     v0.h[1], w0
        orr     w2, w6, w2, lsr #4
        and     w2, w2, #0x3ff
        ubfx    x4, x4, #6, #16
        mov     v1.16b, v2.16b
        orr     w0, w4, w3, lsl #2
        mov     v0.h[2], w2
        mov     v0.h[3], w0
        uxtl    v0.4s, v0.4h
        mla     v1.4s, v0.4s, v3.4s
        shrn    v0.4h, v1.4s, #10
        str     d0, [x5], #8
        cmp     x1, x7
        b.ne    L1e08
        ret

// mlkem_poly_compress_d5 (0x100 bytes)
L1e74:
        .inst   0xd00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        mov     x12, x1
        mov     w14, #0xafc0
        ldr     x1, [x2]
        str     x1, [sp, #24]
        mov     x1, #0x0
        add     x15, sp, #0x10
        mov     w6, #0x0
        movk    w14, #0x13, lsl #16
        mov     w13, #0x4000000
        nop
L1ea8:
        sub     w2, w6, #0x1
        mov     x1, #0x1
        str     xzr, [sp, #16]
        nop
L1eb8:
        add     w3, w2, w1
        add     x4, x15, x1
        add     x1, x1, #0x1
        ldrsh   w3, [x12, x3, lsl #1]
        madd    w3, w3, w14, w13
        lsr     w3, w3, #27
        sturb   w3, [x4, #-1]
        cmp     x1, #0x9
        b.ne    L1eb8
        ldrb    w3, [sp, #19]
        add     w6, w6, #0x8
        ldrb    w1, [sp, #18]
        add     x0, x0, #0x5
        ldrb    w5, [sp, #22]
        lsl     w4, w3, #7
        ldrb    w2, [sp, #20]
        ldrb    w8, [sp, #21]
        orr     w1, w4, w1, lsl #2
        ldrb    w9, [sp, #16]
        lsl     w11, w5, #6
        ldrb    w4, [sp, #17]
        lsl     w10, w2, #4
        ldrb    w7, [sp, #23]
        lsr     w5, w5, #2
        orr     w8, w11, w8, lsl #1
        orr     w3, w10, w3, lsr #1
        orr     w1, w1, w4, lsr #3
        orr     w2, w8, w2, lsr #4
        orr     w5, w5, w7, lsl #3
        orr     w4, w9, w4, lsl #5
        sturb   w4, [x0, #-5]
        sturb   w1, [x0, #-4]
        sturb   w3, [x0, #-3]
        sturb   w2, [x0, #-2]
        sturb   w5, [x0, #-1]
        cmp     w6, #0x100
        b.ne    L1ea8
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L1f70
        ldr     x30, [sp], #32
        ret
L1f70:
        bl      L0830

// mlkem_poly_compress_d11 (0x134 bytes)
L1f74:
        .inst   0xd00000e3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        str     x30, [sp, #-48]!
        mov     x13, #0x7800
        mov     x2, x0
        movk    x13, #0x3afb, lsl #16
        mov     x11, x1
        ldr     x0, [x3]
        str     x0, [sp, #40]
        mov     x0, #0x0
        add     x10, sp, #0x18
        mov     w8, #0x8
        movk    x13, #0x1, lsl #32
        mov     x12, #0x100000000
        nop
L1fb0:
        sub     w0, w8, #0x8
        mov     x1, x10
L1fb8:
        ldrsh   x3, [x11, w0, uxtw #1]
        add     w0, w0, #0x1
        madd    x3, x3, x13, x12
        ubfx    x3, x3, #33, #11
        strh    w3, [x1], #2
        cmp     w8, w0
        b.ne    L1fb8
        ldrh    w5, [sp, #26]
        add     w8, w8, #0x8
        ldrh    w6, [sp, #24]
        add     x2, x2, #0xb
        ldrh    w1, [sp, #28]
        fmov    s0, w1
        lsl     w0, w5, #3
        orr     w0, w0, w6, lsr #8
        ldrh    w4, [sp, #30]
        ushr    v2.2s, v0.2s, #2
        fmov    d0, x6
        lsl     w7, w1, #6
        ldrh    w3, [sp, #32]
        mov     v0.b[1], w0
        orr     w7, w7, w5, lsr #5
        lsl     w5, w4, #1
        ldrh    w0, [sp, #34]
        orr     w1, w5, w1, lsr #10
        lsl     w5, w3, #4
        orr     w4, w5, w4, lsr #7
        fmov    s1, w0
        mov     v0.b[2], w7
        lsl     w7, w0, #7
        orr     w3, w7, w3, lsr #4
        ushr    v1.2s, v1.2s, #1
        ldrh    w6, [sp, #36]
        ldrh    w5, [sp, #38]
        mov     v0.b[3], v2.b[0]
        lsl     w9, w6, #2
        lsl     w7, w5, #5
        orr     w0, w9, w0, lsr #9
        orr     w6, w7, w6, lsr #6
        lsr     w5, w5, #3
        mov     v0.b[4], w1
        sturb   w0, [x2, #-3]
        sturb   w6, [x2, #-2]
        sturb   w5, [x2, #-1]
        mov     v0.b[5], w4
        mov     v0.b[6], w3
        mov     v0.b[7], v1.b[0]
        stur    d0, [x2, #-11]
        cmp     w8, #0x108
        b.ne    L1fb0
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #40]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L20a4
        ldr     x30, [sp], #48
        ret
L20a4:
        bl      L0830
        nop
        nop

// mlkem_poly_decompress_d5 (0xc0 bytes)
L20b0:
        mov     x6, x0
        .inst   0x90000020  // adrp x0, 0x6000
        movi    v2.4s, #0x10
        add     x9, x1, #0xa0
        ldr     q3, [x0, #528]
        nop
L20c8:
        add     x1, x1, #0x5
        ldurb   w0, [x1, #-4]
        ldurb   w2, [x1, #-5]
        mov     v4.16b, v2.16b
        ldurb   w3, [x1, #-3]
        lsl     w4, w0, #3
        and     w5, w2, #0x1f
        orr     w2, w4, w2, lsr #5
        fmov    s0, w5
        and     w4, w2, #0x1f
        ubfx    x7, x0, #2, #5
        lsl     w2, w3, #1
        ldurb   w5, [x1, #-1]
        mov     v0.b[1], w4
        orr     w2, w2, w0, lsr #7
        ldurb   w0, [x1, #-2]
        and     w2, w2, #0x1f
        fmov    s1, w5
        mov     v0.b[2], w7
        lsl     w8, w0, #4
        orr     w3, w8, w3, lsr #4
        ubfx    x4, x0, #1, #5
        and     w3, w3, #0x1f
        lsl     w8, w5, #2
        orr     w0, w8, w0, lsr #6
        ushr    v1.2s, v1.2s, #3
        mov     v0.b[3], w2
        and     w0, w0, #0x1f
        mov     v0.b[4], w3
        mov     v0.b[5], w4
        mov     v0.b[6], w0
        mov     v0.b[7], v1.b[0]
        mov     v1.16b, v2.16b
        uxtl    v0.8h, v0.8b
        umlal   v1.4s, v0.4h, v3.4h
        umlal2  v4.4s, v0.8h, v3.8h
        shrn    v0.4h, v1.4s, #5
        shrn2   v0.8h, v4.4s, #5
        str     q0, [x6], #16
        cmp     x1, x9
        b.ne    L20c8
        ret

// mlkem_poly_decompress_d11 (0xec bytes)
L2170:
        mov     x8, x0
        .inst   0x90000020  // adrp x0, 0x6000
        movi    v2.4s, #0x4, lsl #8
        add     x9, x1, #0x160
        ldr     q3, [x0, #528]
        nop
L2188:
        add     x1, x1, #0xb
        ldurb   w5, [x1, #-9]
        ldurb   w6, [x1, #-10]
        ldurb   w4, [x1, #-7]
        lsl     w2, w5, #5
        ldurh   w0, [x1, #-11]
        orr     w6, w2, w6, lsr #3
        ldurb   w2, [x1, #-8]
        and     w6, w6, #0x7ff
        and     w0, w0, #0x7ff
        fmov    s0, w0
        lsl     w0, w4, #10
        orr     w0, w0, w2, lsl #2
        ldurb   w3, [x1, #-6]
        mov     v0.h[1], w6
        orr     w5, w0, w5, lsr #6
        and     w5, w5, #0x7ff
        ldurb   w2, [x1, #-5]
        lsl     w0, w3, #7
        ldurb   w7, [x1, #-4]
        mov     v1.16b, v2.16b
        orr     w4, w0, w4, lsr #1
        mov     v0.h[2], w5
        and     w4, w4, #0x7ff
        ldurb   w0, [x1, #-3]
        lsl     w6, w2, #4
        orr     w3, w6, w3, lsr #4
        ldurb   w5, [x1, #-2]
        and     w3, w3, #0x7ff
        ldurb   w6, [x1, #-1]
        mov     v0.h[3], w4
        lsl     w10, w0, #9
        mov     v4.16b, v2.16b
        orr     w4, w10, w7, lsl #1
        orr     w2, w4, w2, lsr #7
        lsl     w4, w5, #6
        and     w2, w2, #0x7ff
        orr     w0, w4, w0, lsr #2
        mov     v0.h[4], w3
        and     w0, w0, #0x7ff
        ubfx    x5, x5, #5, #16
        orr     w3, w5, w6, lsl #3
        mov     v0.h[5], w2
        mov     v0.h[6], w0
        mov     v0.h[7], w3
        umlal   v1.4s, v0.4h, v3.4h
        umlal2  v4.4s, v0.8h, v3.8h
        shrn    v0.4h, v1.4s, #11
        shrn2   v0.8h, v4.4s, #11
        str     q0, [x8], #16
        cmp     x9, x1
        b.ne    L2188
        ret
        nop

// mlkem_poly_tobytes (0x3c bytes)
L2260:
        add     x4, x0, #0x180
        nop
L2268:
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
        b.ne    L2268
        ret
        nop

// mlkem_poly_frombytes (0x3c bytes)
L22a0:
        add     x6, x1, #0x180
        nop
L22a8:
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
        cmp     x6, x1
        b.ne    L22a8
        ret
        nop

// mlkem_poly_frommsg (0x5c bytes)
L22e0:
        mov     x6, x0
        mov     x5, x1
        mov     x3, #0x0
        mov     w8, #0x1
        mov     w7, #0x681
        nop
L22f8:
        lsl     w4, w3, #3
        mov     w1, #0x0
L2300:
        lsl     w0, w8, w1
        ldrb    w2, [x5, x3]
        and     w0, w0, #0xff
        and     w0, w0, w2
        neg     w0, w0
        add     w2, w1, w4
        and     w0, w7, w0, asr #16
        add     w1, w1, #0x1
        strh    w0, [x6, x2, lsl #1]
        cmp     w1, #0x8
        b.ne    L2300
        add     x3, x3, #0x1
        cmp     x3, #0x20
        b.ne    L22f8
        ret
        nop

// mlkem_poly_tomsg (0x64 bytes)
L2340:
        mov     w8, #0xafb8
        mov     x4, x0
        mov     x6, x1
        mov     x3, #0x0
        movk    w8, #0x13, lsl #16
        mov     w7, #0x40000000
L2358:
        lsl     w5, w3, #3
        mov     w2, #0x0
        mov     w1, #0x0
        strb    wzr, [x4, x3]
L2368:
        add     w0, w1, w5
        ldrsh   w0, [x6, x0, lsl #1]
        madd    w0, w0, w8, w7
        lsr     w0, w0, #31
        lsl     w0, w0, w1
        orr     w2, w2, w0
        and     w2, w2, #0xff
        add     w1, w1, #0x1
        strb    w2, [x4, x3]
        cmp     w1, #0x8
        b.ne    L2368
        add     x3, x3, #0x1
        cmp     x3, #0x20
        b.ne    L2358
        ret
        nop
        nop
        nop

// mlk_keccak_absorb_once (0x118 bytes)
L23b0:
        movi    v0.4s, #0x0
        stp     x19, x20, [sp, #-64]!
        mov     x19, x0
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     x20, x3
        stp     x23, x30, [sp, #32]
        mov     x21, x2
        mov     x23, x22
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        strb    w4, [sp, #63]
        stp     q0, q0, [x0, #64]
        stp     q0, q0, [x0, #96]
        stp     q0, q0, [x0, #128]
        stp     q0, q0, [x0, #160]
        str     xzr, [x0, #192]
        cmp     x3, x22
        b.cc    L242c
        nop
L2400:
        mov     x1, x21
        mov     w3, w23
        mov     w2, #0x0
        mov     x0, x19
        bl      L2c90
        sub     x20, x20, x22
        mov     x0, x19
        bl      L2dd0
        add     x21, x21, x22
        cmp     x20, x22
        b.cs    L2400
L242c:
        sub     w23, w23, #0x1
        mov     w22, w20
        cbnz    x20,L247c
L2438:
        add     x20, sp, #0x3f
        mov     w2, w22
        mov     x1, x20
        mov     x0, x19
        mov     w3, #0x1
        bl      L2c90
        mov     w4, #0xffffff80
        mov     x1, x20
        mov     w2, w23
        mov     x0, x19
        mov     w3, #0x1
        strb    w4, [sp, #63]
        bl      L2c90
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #64
        ret
L247c:
        mov     x1, x21
        mov     w3, w20
        mov     x0, x19
        mov     w2, #0x0
        bl      L2c90
        cmp     x20, w23, uxtw
        b.ne    L2438
        ldrb    w4, [sp, #63]
        mov     w2, w20
        mov     x0, x19
        add     x1, sp, #0x3f
        orr     w4, w4, #0xffffff80
        mov     w3, #0x1
        strb    w4, [sp, #63]
        bl      L2c90
        ldp     x21, x22, [sp, #16]
        ldp     x23, x30, [sp, #32]
        ldp     x19, x20, [sp], #64
        ret
        nop
        nop

// mlkem_shake128_absorb_once (0x14 bytes)
L24d0:
        mov     x3, x2
        mov     w4, #0x1f
        mov     x2, x1
        mov     w1, #0xa8
        b       L23b0

// mlkem_shake128_squeezeblocks (0x54 bytes)
L24e4:
        cbz     x1,L2534
        stp     x19, x20, [sp, #-32]!
        mov     x20, x0
        mov     x19, x1
        stp     x21, x30, [sp, #16]
        mov     x21, x2
        nop
L2500:
        mov     x0, x21
        bl      L2dd0
        mov     x1, x20
        mov     x0, x21
        mov     w3, #0xa8
        mov     w2, #0x0
        bl      L2c60
        add     x20, x20, #0xa8
        subs    x19, x19, #0x1
        b.ne    L2500
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #32
        ret
L2534:
        ret
        nop
        nop

// mlkem_shake128_init (0x4 bytes)
L2540:
        ret

// mlkem_shake128_release (0x24 bytes)
L2544:
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
L2570:
        stp     x19, x20, [sp, #-304]!
        mov     x19, x1
        .inst   0xb00000e4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        stp     x21, x22, [sp, #16]
        add     x21, sp, #0x4f
        str     x30, [sp, #40]
        and     x21, x21, #0xffffffffffffffe0
        mov     x22, x0
        mov     x0, x21
        ldr     x1, [x4]
        str     x1, [sp, #296]
        mov     x1, #0x0
        mov     w4, #0x1f
        mov     w1, #0x88
        bl      L23b0
        cbz     x19,L25f4
        str     x23, [sp, #32]
        mov     x23, #0x88
        nop
L25c0:
        mov     x0, x21
        bl      L2dd0
        cmp     x19, #0x88
        mov     x1, x22
        csel    x20, x19, x23, ls
        mov     x0, x21
        mov     w3, w20
        mov     w2, #0x0
        bl      L2c60
        add     x22, x22, x20
        subs    x19, x19, x20
        b.ne    L25c0
        ldr     x23, [sp, #32]
L25f4:
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x21, #64]
        stp     q0, q0, [x21, #96]
        stp     q0, q0, [x21, #128]
        stp     q0, q0, [x21, #160]
        stp     q0, q0, [x21, #192]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L2640
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #40]
        ldp     x19, x20, [sp], #304
        ret
L2640:
        str     x23, [sp, #32]
        bl      L0830
        nop
        nop

// mlkem_sha3_256 (0xa4 bytes)
L2650:
        stp     x19, x20, [sp, #-240]!
        mov     x3, x2
        mov     x2, x1
        .inst   0xb00000e5  // adrp x5, 0x1f000
        ldr     x5, [x5, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x20
        mov     w4, #0x6
        mov     x20, x0
        mov     w1, #0x88
        ldr     x0, [x5]
        str     x0, [sp, #232]
        mov     x0, #0x0
        mov     x0, x19
        bl      L23b0
        mov     x0, x19
        bl      L2dd0
        mov     x1, x20
        mov     x0, x19
        mov     w3, #0x20
        mov     w2, #0x0
        bl      L2c60
        str     xzr, [x19, #192]
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L26f0
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #240
        ret
L26f0:
        bl      L0830

// mlkem_sha3_512 (0xa4 bytes)
L26f4:
        stp     x19, x20, [sp, #-240]!
        mov     x3, x2
        mov     x2, x1
        .inst   0xb00000e5  // adrp x5, 0x1f000
        ldr     x5, [x5, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x20
        mov     w4, #0x6
        mov     x20, x0
        mov     w1, #0x48
        ldr     x0, [x5]
        str     x0, [sp, #232]
        mov     x0, #0x0
        mov     x0, x19
        bl      L23b0
        mov     x0, x19
        bl      L2dd0
        mov     x1, x20
        mov     x0, x19
        mov     w3, #0x40
        mov     w2, #0x0
        bl      L2c60
        str     xzr, [x19, #192]
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L2794
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #240
        ret
L2794:
        bl      L0830
        nop
        nop

// mlk_keccak_absorb_once_x4.constprop.0 (0x16c bytes)
L27a0:
        stp     x19, x20, [sp, #-96]!
        mov     w19, w1
        mov     x20, x6
        .inst   0xb00000e7  // adrp x7, 0x1f000
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
        b.hi    L283c
L27f8:
        mov     x4, x26
        mov     x3, x23
        mov     x2, x22
        mov     x1, x21
        mov     w6, w25
        mov     w5, #0x0
        mov     x0, x24
        bl      L2d50
        mov     x0, x24
        sub     x20, x20, x19
        bl      L33a0
        add     x26, x26, x19
        add     x23, x23, x19
        add     x22, x22, x19
        add     x21, x21, x19
        cmp     x20, x19
        b.cs    L27f8
L283c:
        sub     w25, w25, #0x1
        mov     w27, w20
        cbnz    x20,L28c8
L2848:
        add     x19, sp, #0x57
        mov     w5, w27
        mov     x4, x19
        mov     x0, x24
        mov     x3, x19
        mov     x2, x19
        mov     x1, x19
        mov     w6, #0x1
        bl      L2d50
        mov     w5, w25
        mov     x0, x24
        mov     x4, x19
        mov     w7, #0xffffff80
L287c:
        mov     x2, x4
        mov     x1, x4
        mov     x3, x4
        mov     w6, #0x1
        strb    w7, [sp, #87]
        bl      L2d50
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #88]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L2908
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        ldp     x19, x20, [sp], #96
        ret
L28c8:
        mov     x4, x26
        mov     x3, x23
        mov     x2, x22
        mov     x1, x21
        mov     w6, w20
        mov     x0, x24
        mov     w5, #0x0
        bl      L2d50
        cmp     x20, w25, uxtw
        b.ne    L2848
        ldrb    w7, [sp, #87]
        add     x4, sp, #0x57
        mov     w5, w20
        mov     x0, x24
        orr     w7, w7, #0xffffff80
        b       L287c
L2908:
        bl      L0830
        nop

// mlkem_shake128x4_absorb_once (0x64 bytes)
L2910:
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
        b       L27a0

// mlkem_shake128x4_squeezeblocks (0x84 bytes)
L2974:
        cbz     x4,L29f4
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
L29a0:
        mov     x0, x24
        bl      L33a0
        mov     x4, x19
        mov     x3, x20
        mov     x2, x21
        mov     x1, x22
        mov     x0, x24
        mov     w6, #0xa8
        mov     w5, #0x0
        bl      L2cd0
        add     x19, x19, #0xa8
        add     x20, x20, #0xa8
        add     x21, x21, #0xa8
        add     x22, x22, #0xa8
        subs    x23, x23, #0x1
        b.ne    L29a0
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L29f4:
        ret
        nop
        nop

// mlkem_shake128x4_init (0x4 bytes)
L2a00:
        ret

// mlkem_shake128x4_release (0x1c bytes)
L2a04:
        stp     x19, x30, [sp, #-16]!
        mov     x2, #0x320
        mov     x19, x0
        mov     w1, #0x0
        bl      L0840
        ldp     x19, x30, [sp], #16
        ret

// mlkem_shake256x4 (0x23c bytes)
L2a20:
        sub     sp, sp, #0x5d0
        .inst   0xb00000e8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        stp     x25, x26, [sp, #48]
        mov     x26, #0xf0f0f0f0f0f0f0f0
        movk    x26, #0xf0f1
        stp     x19, x20, [sp]
        add     x20, sp, #0x8f
        and     x20, x20, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        umulh   x26, x4, x26
        mov     x19, x5
        stp     x23, x24, [sp, #32]
        mov     x21, x6
        mov     x22, x3
        stp     x27, x28, [sp, #64]
        mov     x25, x0
        mov     x27, x4
        str     x30, [sp, #80]
        mov     x24, x1
        str     x7, [sp, #104]
        mov     x23, x2
        ldr     x28, [sp, #1488]
        ldr     x1, [x8]
        str     x1, [sp, #1480]
        mov     x1, #0x0
        mov     x2, #0x320
        mov     x0, x20
        bl      L0840
        lsr     x26, x26, #7
        ldr     x4, [sp, #104]
        mov     x5, x28
        ldr     x6, [sp, #1496]
        mov     x3, x21
        mov     x2, x19
        mov     x0, x20
        mov     w1, #0x88
        bl      L27a0
        cmp     x27, #0x87
        b.ls    L2afc
        mov     x21, x26
        mov     x19, #0x0
L2ac8:
        mov     x0, x20
        bl      L33a0
        add     x4, x22, x19
        add     x3, x23, x19
        add     x2, x24, x19
        add     x1, x25, x19
        mov     x0, x20
        mov     w6, #0x88
        mov     w5, #0x0
        bl      L2cd0
        add     x19, x19, #0x88
        subs    x21, x21, #0x1
        b.ne    L2ac8
L2afc:
        mov     x19, #0xf0f0f0f0f0f0f0f0
        movk    x19, #0xf0f1
        umulh   x19, x27, x19
        lsr     x19, x19, #7
        add     x19, x19, x19, lsl #4
        subs    x19, x27, x19, lsl #3
        b.ne    L2bc8
        add     x21, sp, #0x540
        add     x27, sp, #0x4b8
        add     x26, sp, #0x430
        add     x28, sp, #0x3a8
L2b28:
        mov     x0, x20
        mov     x2, #0x320
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        str     xzr, [x28, #128]
        stp     q0, q0, [x28]
        stp     q0, q0, [x28, #32]
        stp     q0, q0, [x28, #64]
        stp     q0, q0, [x28, #96]
        stp     q0, q0, [x26]
        stp     q0, q0, [x26, #32]
        stp     q0, q0, [x26, #64]
        stp     q0, q0, [x26, #96]
        str     xzr, [x26, #128]
        stp     q0, q0, [x27]
        stp     q0, q0, [x27, #32]
        stp     q0, q0, [x27, #64]
        stp     q0, q0, [x27, #96]
        str     xzr, [x27, #128]
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x21, #64]
        stp     q0, q0, [x21, #96]
        str     xzr, [x21, #128]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1480]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L2c58
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x5d0
        ret
L2bc8:
        add     x26, x26, x26, lsl #4
        mov     x0, x20
        add     x21, sp, #0x540
        add     x27, sp, #0x4b8
        lsl     x1, x26, #3
        add     x28, sp, #0x3a8
        add     x26, sp, #0x430
        str     x1, [sp, #104]
        bl      L33a0
        mov     x4, x21
        mov     x3, x27
        mov     w6, #0x88
        mov     w5, #0x0
        mov     x2, x26
        mov     x1, x28
        mov     x0, x20
        bl      L2cd0
        ldr     x0, [sp, #104]
        mov     x2, x19
        mov     x1, x28
        add     x0, x25, x0
        bl      L0810
        ldr     x25, [sp, #104]
        mov     x2, x19
        mov     x1, x26
        add     x0, x24, x25
        bl      L0810
        mov     x2, x19
        mov     x1, x27
        add     x0, x23, x25
        bl      L0810
        mov     x2, x19
        mov     x1, x21
        add     x0, x22, x25
        bl      L0810
        b       L2b28
L2c58:
        bl      L0830
        nop

// mlkem_keccakf1600_extract_bytes (0x30 bytes)
L2c60:
        mov     w2, w2
        cbz     w3,L2c8c
        mov     w3, w3
        add     x4, x0, x2
        mov     x0, #0x0
        nop
L2c78:
        ldrb    w2, [x4, x0]
        strb    w2, [x1, x0]
        add     x0, x0, #0x1
        cmp     x3, x0
        b.ne    L2c78
L2c8c:
        ret

// mlkem_keccakf1600_xor_bytes (0x38 bytes)
L2c90:
        mov     w2, w2
        cbz     w3,L2cc4
        mov     w5, w3
        add     x3, x0, x2
        mov     x0, #0x0
        nop
L2ca8:
        ldrb    w2, [x3, x0]
        ldrb    w4, [x1, x0]
        eor     w2, w2, w4
        strb    w2, [x3, x0]
        add     x0, x0, #0x1
        cmp     x5, x0
        b.ne    L2ca8
L2cc4:
        ret
        nop
        nop

// mlkem_keccakf1600x4_extract_bytes (0x80 bytes)
L2cd0:
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
        bl      L2c60
        mov     w3, w20
        mov     w2, w19
        mov     x1, x24
        add     x0, x21, #0xc8
        bl      L2c60
        mov     w3, w20
        mov     w2, w19
        mov     x1, x23
        add     x0, x21, #0x190
        bl      L2c60
        ldp     x23, x24, [sp, #32]
        mov     w3, w20
        ldr     x30, [sp, #48]
        mov     w2, w19
        mov     x1, x22
        add     x0, x21, #0x258
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        b       L2c60

// mlkem_keccakf1600x4_xor_bytes (0x80 bytes)
L2d50:
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
        bl      L2c90
        mov     w3, w20
        mov     w2, w19
        mov     x1, x24
        add     x0, x21, #0xc8
        bl      L2c90
        mov     w3, w20
        mov     w2, w19
        mov     x1, x23
        add     x0, x21, #0x190
        bl      L2c90
        ldp     x23, x24, [sp, #32]
        mov     w3, w20
        ldr     x30, [sp, #48]
        mov     w2, w19
        mov     x1, x22
        add     x0, x21, #0x258
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp], #64
        b       L2c90

// mlkem_keccakf1600_permute (0x5d0 bytes)
L2dd0:
        stp     x19, x20, [sp, #-192]!
        .inst   0x90000021  // adrp x1, 0x6000
        add     x1, x1, #0x2b0
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
L2e80:
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
        b.ne    L2e80
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
L33a0:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L2dd0
        add     x0, x19, #0xc8
        bl      L2dd0
        add     x0, x19, #0x190
        bl      L2dd0
        add     x0, x19, #0x258
        ldp     x19, x30, [sp], #16
        b       L2dd0
        nop
        nop

// mlkem512_gen_matrix (0xc4 bytes)
L33d0:
        stp     x19, x30, [sp, #-304]!
        .inst   0x900000e5  // adrp x5, 0x1f000
        ldr     x5, [x5, #4088]
        add     x19, sp, #0x2f
        and     x19, x19, #0xffffffffffffffe0
        mov     x3, x19
        add     x4, x19, #0x100
        ldr     x6, [x5]
        str     x6, [sp, #296]
        mov     x6, #0x0
L33f8:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x3]
        add     x3, x3, #0x40
        cmp     x4, x3
        b.ne    L33f8
        cmp     w2, #0x0
        mov     w7, #0x101
        cset    w6, ne
        cset    w5, eq
        mov     x4, x19
        add     x3, x0, #0x600
        add     x2, x0, #0x400
        add     x1, x0, #0x200
        strh    wzr, [x19, #32]
        strb    w5, [x19, #96]
        strb    w6, [x19, #97]
        strb    w6, [x19, #160]
        strb    w5, [x19, #161]
        strh    w7, [x19, #224]
        bl      L4b30
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        stp     q0, q0, [x19, #192]
        stp     q0, q0, [x19, #224]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3490
        ldp     x19, x30, [sp], #304
        ret
L3490:
        bl      L0830

// mlkem512_indcpa_keypair_derand (0x1f4 bytes)
L3494:
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
        .inst   0x900000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        ldr     x0, [x2]
        str     x0, [sp, #5864]
        mov     x0, #0x0
        stp     q0, q1, [x22]
        mov     x0, x20
        mov     x2, #0x21
        strb    w24, [x23, #1632]
        bl      L26f4
        mov     x1, x20
        mov     x0, x19
        mov     w2, #0x0
        bl      L33d0
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
        bl      L4730
        add     x24, x19, #0xc00
        mov     x0, x21
        bl      L45a0
        mov     x0, x23
        bl      L45a0
        mov     x1, x21
        mov     x0, x25
        bl      L4694
        mov     x3, x25
        mov     x2, x21
        mov     x0, x24
        mov     x1, x19
        bl      L45e0
        mov     x3, x25
        mov     x2, x21
        add     x1, x19, #0x400
        add     x0, x19, #0xe00
        bl      L45e0
        mov     x0, x24
        bl      L4710
        mov     x1, x23
        mov     x0, x24
        bl      L46e0
        mov     x0, x24
        bl      L46c0
        mov     x0, x21
        bl      L46c0
        mov     x1, x21
        mov     x0, x27
        bl      L4540
        mov     x1, x24
        mov     x0, x26
        bl      L4540
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
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #5864]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3684
        ldp     x19, x20, [sp, #16]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x16f0
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x30, [sp, #80]
        add     sp, sp, x12
        ret
L3684:
        bl      L0830
        nop
        nop

// mlkem512_indcpa_enc (0x280 bytes)
L3690:
        mov     x12, #0x20c0
        sub     sp, sp, x12
        mov     x4, #0x1a00
        mov     x5, #0x1800
        stp     x19, x20, [sp, #16]
        mov     x20, x2
        add     x19, sp, #0x9f
        .inst   0x900000e2  // adrp x2, 0x1f000
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
        bl      L4570
        ldp     q0, q1, [x20, #768]
        mov     x1, x22
        mov     x0, x26
        add     x22, x19, #0x800
        stp     q0, q1, [x28]
        bl      L22e0
        mov     x1, x28
        mov     x0, x19
        mov     w2, #0x1
        bl      L33d0
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
        bl      L4934
        mov     x1, x21
        mov     w2, #0x4
        mov     x0, x27
        bl      L4890
        mov     x0, x20
        bl      L45a0
        mov     x1, x20
        mov     x0, x23
        bl      L4694
        mov     x7, #0x1e00
        mov     x3, x23
        add     x21, x19, x7
        mov     x2, x20
        mov     x0, x22
        mov     x1, x19
        bl      L45e0
        mov     x3, x23
        mov     x2, x20
        add     x1, x19, #0x400
        add     x0, x19, #0xa00
        bl      L45e0
        mov     x3, x23
        mov     x2, x20
        mov     x1, x24
        mov     x0, x21
        bl      L45e0
        mov     x0, x22
        bl      L45c0
        mov     x0, x21
        bl      L4394
        mov     x1, x25
        mov     x0, x22
        bl      L46e0
        mov     x1, x27
        mov     x0, x21
        bl      L41e0
        mov     x1, x26
        mov     x0, x21
        bl      L41e0
        mov     x0, x22
        bl      L46c0
        mov     x0, x21
        bl      L4190
        ldr     x0, [sp, #120]
        mov     x1, x22
        bl      L44e0
        ldr     x0, [sp, #120]
        mov     x1, x21
        add     x0, x0, #0x280
        bl      L1bf0
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
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #8376]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L390c
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
L390c:
        bl      L0830

// mlkem512_indcpa_dec (0x148 bytes)
L3910:
        sub     sp, sp, #0xe60
        .inst   0x900000e3  // adrp x3, 0x1f000
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
        bl      L4510
        add     x1, x23, #0x280
        mov     x0, x21
        bl      L1da4
        add     x23, x19, #0x800
        mov     x1, x22
        mov     x0, x19
        bl      L4570
        add     x22, x19, #0xa00
        mov     x0, x20
        bl      L45a0
        mov     x1, x20
        mov     x0, x23
        bl      L4694
        mov     x3, x23
        mov     x2, x20
        mov     x1, x19
        mov     x0, x22
        bl      L45e0
        mov     x0, x22
        bl      L4394
        mov     x1, x22
        mov     x0, x21
        bl      L4210
        mov     x0, x21
        bl      L4190
        mov     x1, x21
        mov     x0, x24
        bl      L2340
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
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #3672]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3a54
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        add     sp, sp, #0xe60
        ret
L3a54:
        bl      L0830
        nop
        nop

// mlkem512_check_pk (0x138 bytes)
L3a60:
        sub     sp, sp, #0x740
        mov     x1, x0
        .inst   0x900000e2  // adrp x2, 0x1f000
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
        bl      L4570
        mov     x0, x20
        bl      L46c0
        mov     x0, x21
        mov     x1, x20
        bl      L4540
        movi    v2.4s, #0x0
        mov     x0, x19
        mov     x2, x21
        add     x1, x20, #0x700
        mov     v3.16b, v2.16b
        nop
L3ac8:
        ldr     q0, [x0], #16
        ldr     q1, [x2], #16
        eor     v0.16b, v0.16b, v1.16b
        orr     v3.16b, v3.16b, v0.16b
        eor     v2.16b, v2.16b, v0.16b
        cmp     x1, x2
        b.ne    L3ac8
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
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1848]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3b94
        ldp     x21, x30, [sp, #16]
        mov     w0, w19
        ldp     x19, x20, [sp]
        add     sp, sp, #0x740
        ret
L3b94:
        bl      L0830
        nop
        nop

// mlkem512_check_sk (0xe8 bytes)
L3ba0:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        add     x1, x0, #0x300
        .inst   0x900000e3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x3f
        mov     x2, #0x320
        ldr     x4, [x3]
        str     x4, [sp, #88]
        mov     x4, #0x0
        and     x19, x19, #0xffffffffffffffe0
        mov     x0, x19
        bl      L2650
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
        .inst   0x900000e1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #88]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L3c84
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #96
        ret
L3c84:
        bl      L0830
        nop
        nop

// mlkem512_keypair_derand (0x94 bytes)
L3c90:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        mov     x21, x0
        str     x30, [sp, #32]
        bl      L3494
        mov     x2, #0x320
        mov     w20, w0
        cbnz    w0,L3cf4
        mov     x1, x21
        add     x0, x19, #0x300
        bl      L0810
        mov     x1, x21
        add     x0, x19, #0x620
        mov     x2, #0x320
        bl      L2650
        ldp     q0, q1, [x22, #32]
        add     x19, x19, #0x640
        mov     w0, w20
        stp     q0, q1, [x19]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L3cf4:
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
L3d24:
        stp     x19, x20, [sp, #-128]!
        mov     x20, x0
        .inst   0x900000e2  // adrp x2, 0x1f000
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
        cbnz    w0,L3da4
        mov     x1, x21
        mov     x0, x20
        mov     x2, x19
        bl      L3c90
L3d70:
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0x900000e1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #120]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L3dac
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #128
        ret
L3da4:
        mov     w0, #0xfffffffd
        b       L3d70
L3dac:
        bl      L0830

// mlkem512_enc_derand (0xe0 bytes)
L3db0:
        stp     x19, x20, [sp, #-224]!
        .inst   0x900000e4  // adrp x4, 0x1f000
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
        bl      L3a60
        cbz     w0,L3e40
L3dfc:
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        .inst   0x900000e1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #216]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L3e8c
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #224
        ret
L3e40:
        ldp     q0, q1, [x22]
        mov     x1, x21
        add     x0, x19, #0x60
        mov     x2, #0x320
        stp     q0, q1, [x20]
        bl      L2650
        mov     x1, x20
        mov     x0, x19
        mov     x2, #0x40
        bl      L26f4
        mov     x2, x21
        mov     x0, x24
        add     x3, x19, #0x20
        mov     x1, x20
        bl      L3690
        cbnz    w0,L3dfc
        ldp     q0, q1, [x19]
        stp     q0, q1, [x23]
        b       L3dfc
L3e8c:
        bl      L0830

// mlkem512_enc (0x98 bytes)
L3e90:
        stp     x19, x20, [sp, #-112]!
        mov     x20, x0
        .inst   0x900000e3  // adrp x3, 0x1f000
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
        cbnz    w0,L3f1c
        mov     x2, x22
        mov     x1, x21
        mov     x0, x20
        mov     x3, x19
        bl      L3db0
L3ee8:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0x900000e1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #104]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L3f24
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret
L3f1c:
        mov     w0, #0xfffffffd
        b       L3ee8
L3f24:
        bl      L0830
        nop
        nop

// mlkem512_dec (0x20c bytes)
L3f30:
        sub     sp, sp, #0x400
        .inst   0x900000e3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x5f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        stp     x23, x24, [sp, #32]
        mov     x24, x0
        mov     x23, x2
        stp     x25, x30, [sp, #48]
        mov     x25, x1
        mov     x0, x2
        ldr     x1, [x3]
        str     x1, [sp, #1016]
        mov     x1, #0x0
        bl      L3ba0
        cbz     w0,L3fe0
        mov     w20, w0
        add     x22, x19, #0x360
        add     x21, x19, #0x320
L3f84:
        mov     x0, x19
        mov     x2, #0x320
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x22]
        stp     q0, q0, [x22, #32]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1016]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4138
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        add     sp, sp, #0x400
        ret
L3fe0:
        add     x22, x19, #0x360
        mov     x2, x23
        mov     x0, x22
        mov     x1, x25
        add     x21, x19, #0x320
        bl      L3910
        mov     w20, w0
        cbnz    w0,L3f84
        ldr     q0, [x23, #1568]
        mov     x1, x22
        ldr     q1, [x23, #1584]
        mov     x0, x21
        mov     x2, #0x40
        stp     q0, q1, [x19, #896]
        bl      L26f4
        add     x3, x19, #0x340
        add     x2, x23, #0x300
        mov     x1, x22
        mov     x0, x19
        bl      L3690
        mov     w20, w0
        cbnz    w0,L3f84
        movi    v2.4s, #0x0
        mov     x0, x19
        mov     x1, x25
        add     x2, x19, #0x300
        mov     v3.16b, v2.16b
        nop
L4050:
        ldr     q0, [x1], #16
        ldr     q1, [x0], #16
        eor     v0.16b, v0.16b, v1.16b
        orr     v3.16b, v3.16b, v0.16b
        eor     v2.16b, v2.16b, v0.16b
        cmp     x0, x2
        b.ne    L4050
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
        ldr     q0, [x23, #1600]
        and     w0, w0, #0xff
        ldr     q1, [x23, #1616]
        mov     x2, #0x300
        eor     w23, w0, w1
        mov     x1, x25
        add     x0, x19, #0x20
        stp     q0, q1, [x19]
        bl      L0810
        mov     x0, x24
        mov     x2, x19
        mov     x3, #0x320
        mov     x1, #0x20
        bl      L2570
        neg     w4, w23
        sub     x24, x24, #0x1
        mov     x0, #0x1
        nop
L4108:
        add     x2, x21, x0
        mov     w1, w4
        ldurb   w2, [x2, #-1]
        ldrb    w3, [x24, x0]
        eor     w3, w2, w3
        and     w1, w3, w1, asr #16
        eor     w2, w2, w1
        strb    w2, [x24, x0]
        add     x0, x0, #0x1
        cmp     x0, #0x21
        b.ne    L4108
        b       L3f84
L4138:
        bl      L0830
        nop

// mlkem_poly_tomont (0x48 bytes)
L4140:
        .inst   0xd0000002  // adrp x2, 0x6000
        .inst   0xd0000001  // adrp x1, 0x6000
        mvni    v3.8h, #0xd, lsl #8
        ldr     q5, [x2, #560]
        ldr     q4, [x1, #544]
        add     x1, x0, #0x200
L4158:
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
        b.ne    L4158
        ret
        nop
        nop

// mlkem_poly_reduce (0x4c bytes)
L4190:
        add     x5, x0, #0x200
        mov     w7, #0x4ebf
        mov     w6, #0x2000000
        mov     w4, #0xfffff2ff
L41a0:
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
        b.ne    L41a0
        ret
        nop

// mlkem_poly_add (0x28 bytes)
L41e0:
        mov     x2, #0x0
        nop
L41e8:
        ldr     q0, [x0, x2]
        ldr     q1, [x1, x2]
        add     v0.8h, v0.8h, v1.8h
        str     q0, [x0, x2]
        add     x2, x2, #0x10
        cmp     x2, #0x200
        b.ne    L41e8
        ret
        nop
        nop

// mlkem_poly_sub (0x28 bytes)
L4210:
        mov     x2, #0x0
        nop
L4218:
        ldr     q0, [x0, x2]
        ldr     q1, [x1, x2]
        sub     v0.8h, v0.8h, v1.8h
        str     q0, [x0, x2]
        add     x2, x2, #0x10
        cmp     x2, #0x200
        b.ne    L4218
        ret
        nop
        nop

// mlkem_poly_mulcache_compute (0x74 bytes)
L4240:
        .inst   0xd0000008  // adrp x8, 0x6000
        add     x8, x8, #0x380
        add     x5, x8, #0x80
        add     x4, x0, #0x2
        add     x2, x1, #0x2
        add     x8, x8, #0x100
        mov     w7, #0xfffff301
        mov     w6, #0xfffff2ff
L4260:
        ldrsh   w0, [x5], #2
        add     x2, x2, #0x8
        ldursh  w1, [x2, #-8]
        neg     w3, w0
        sxth    w3, w3
        mul     w1, w1, w0
        mul     w0, w1, w7
        sxth    w0, w0
        madd    w0, w0, w6, w1
        asr     w0, w0, #16
        sturh   w0, [x4, #-2]
        ldursh  w1, [x2, #-4]
        mul     w1, w1, w3
        mul     w0, w1, w7
        sxth    w0, w0
        madd    w0, w0, w6, w1
        asr     w0, w0, #16
        strh    w0, [x4], #4
        cmp     x8, x5
        b.ne    L4260
        ret

// mlkem_poly_ntt (0xe0 bytes)
L42b4:
        .inst   0xd000000c  // adrp x12, 0x6000
        mov     x13, x0
        add     x12, x12, #0x380
        add     x14, x0, #0x2
        mov     w7, #0x0
        mov     w8, #0xfffffd0a
        mov     w16, #0x1
        mov     w17, #0x100
        mov     w11, #0xfffff301
        mov     w10, #0xfffff2ff
        nop
L42e0:
        add     w15, w7, #0x1
        mov     w4, #0x0
        lsl     w7, w16, w7
        lsr     w6, w17, w15
        lsl     w9, w6, #1
        nop
L42f8:
        add     w7, w7, #0x1
        cmp     w6, w4
        b.ls    L4360
        sub     w2, w6, w4
        mov     w0, w4
        sub     w2, w2, #0x1
        mov     w3, w6
        add     x2, x2, x0
        sub     x3, x3, x0
        add     x1, x13, w4, uxtw #1
        add     x2, x14, x2, lsl #1
        nop
L4328:
        ldrsh   w5, [x1, x3, lsl #1]
        ldrh    w18, [x1]
        mul     w5, w5, w8
        mul     w0, w5, w11
        sxth    w0, w0
        madd    w0, w0, w10, w5
        asr     w0, w0, #16
        sub     w5, w18, w0
        strh    w5, [x1, x3, lsl #1]
        ldrh    w5, [x1]
        add     w0, w0, w5
        strh    w0, [x1], #2
        cmp     x2, x1
        b.ne    L4328
L4360:
        add     w4, w4, w9
        add     w6, w6, w9
        cmp     w4, #0xff
        b.hi    L4378
        ldrsh   w8, [x12, w7, uxtw #1]
        b       L42f8
L4378:
        cmp     w15, #0x7
        b.eq    L4390
        lsl     w0, w16, w15
        mov     w7, w15
        ldrsh   w8, [x12, x0, lsl #1]
        b       L42e0
L4390:
        ret

// mlkem_poly_invntt_tomont (0x148 bytes)
L4394:
        mov     x15, x0
        .inst   0xd0000000  // adrp x0, 0x6000
        mvni    v3.8h, #0xd, lsl #8
        add     x1, x15, #0x200
        ldr     q4, [x0, #576]
        .inst   0xd0000000  // adrp x0, 0x6000
        stp     x19, x30, [sp, #-16]!
        ldr     q5, [x0, #560]
        mov     x0, x15
L43b8:
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
        b.ne    L43b8
        .inst   0xd000000e  // adrp x14, 0x6000
        add     x16, x15, #0x2
        add     x14, x14, #0x380
        mov     w9, #0x65c
        mov     w17, #0x7
        mov     w30, #0x100
        mov     w18, #0x1
        mov     w13, #0x4ebf
        mov     w12, #0x2000000
        mov     w8, #0xfffff2ff
        mov     w11, #0xfffff301
L4410:
        lsr     w5, w30, w17
        mov     w6, #0x0
        lsl     w7, w18, w17
        lsl     w10, w5, #1
        sub     w7, w7, #0x1
        nop
L4428:
        sub     w7, w7, #0x1
        cmp     w6, w5
        b.cs    L44a4
        sub     w3, w5, w6
        mov     w0, w5
        sub     w3, w3, #0x1
        mov     w4, w6
        add     x3, x3, x0
        sub     x4, x4, x0
        add     x2, x15, w5, uxtw #1
        add     x3, x16, x3, lsl #1
        nop
L4458:
        ldrsh   w19, [x2, x4, lsl #1]
        ldrh    w0, [x2]
        add     w0, w19, w0
        sxth    w0, w0
        madd    w1, w0, w13, w12
        asr     w1, w1, #26
        madd    w0, w1, w8, w0
        strh    w0, [x2, x4, lsl #1]
        ldrh    w0, [x2]
        sub     w0, w0, w19
        sxth    w0, w0
        mul     w0, w0, w9
        mul     w1, w0, w11
        sxth    w1, w1
        madd    w0, w1, w8, w0
        asr     w0, w0, #16
        strh    w0, [x2], #2
        cmp     x2, x3
        b.ne    L4458
L44a4:
        add     w6, w6, w10
        add     w5, w5, w10
        cmp     w6, #0xff
        b.hi    L44bc
        ldrsh   w9, [x14, w7, uxtw #1]
        b       L4428
L44bc:
        subs    w17, w17, #0x1
        b.eq    L44d4
        lsl     w0, w18, w17
        sub     w0, w0, #0x1
        ldrsh   w9, [x14, x0, lsl #1]
        b       L4410
L44d4:
        ldp     x19, x30, [sp], #16
        ret
        nop

// mlkem512_polyvec_compress_du (0x28 bytes)
L44e0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L1cd0
        ldr     x30, [sp, #16]
        add     x1, x20, #0x200
        add     x0, x19, #0x140
        ldp     x19, x20, [sp], #32
        b       L1cd0
        nop
        nop

// mlkem512_polyvec_decompress_du (0x28 bytes)
L4510:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L1df0
        ldr     x30, [sp, #16]
        add     x1, x20, #0x140
        add     x0, x19, #0x200
        ldp     x19, x20, [sp], #32
        b       L1df0
        nop
        nop

// mlkem512_polyvec_tobytes (0x28 bytes)
L4540:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L2260
        ldr     x30, [sp, #16]
        add     x1, x20, #0x200
        add     x0, x19, #0x180
        ldp     x19, x20, [sp], #32
        b       L2260
        nop
        nop

// mlkem512_polyvec_frombytes (0x28 bytes)
L4570:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L22a0
        ldr     x30, [sp, #16]
        add     x1, x20, #0x180
        add     x0, x19, #0x200
        ldp     x19, x20, [sp], #32
        b       L22a0
        nop
        nop

// mlkem512_polyvec_ntt (0x18 bytes)
L45a0:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L42b4
        add     x0, x19, #0x200
        ldp     x19, x30, [sp], #16
        b       L42b4
        nop
        nop

// mlkem512_polyvec_invntt_tomont (0x18 bytes)
L45c0:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L4394
        add     x0, x19, #0x200
        ldp     x19, x30, [sp], #16
        b       L4394
        nop
        nop

// mlkem512_polyvec_basemul_acc_montgomery_cached (0xb4 bytes)
L45e0:
        mov     x4, x1
        mov     x7, x0
        mov     x5, x2
        mov     x6, x3
        add     x13, x1, #0x200
        mov     w12, #0xfffff301
        mov     w11, #0xfffff2ff
        nop
L4600:
        ldrsh   w16, [x4, #2]
        add     x4, x4, #0x4
        ldrsh   w0, [x5]
        add     x6, x6, #0x2
        ldrsh   w1, [x5, #512]
        add     x7, x7, #0x4
        ldursh  w10, [x4, #-4]
        add     x5, x5, #0x4
        ldrsh   w15, [x4, #510]
        ldrsh   w14, [x4, #508]
        ldursh  w3, [x6, #-2]
        ldrsh   w9, [x6, #254]
        mul     w18, w10, w0
        ldrsh   w2, [x5, #510]
        mul     w0, w16, w0
        ldursh  w8, [x5, #-2]
        mul     w17, w14, w1
        mul     w1, w15, w1
        madd    w3, w3, w16, w18
        madd    w2, w2, w14, w1
        madd    w0, w8, w10, w0
        madd    w9, w9, w15, w17
        add     w2, w2, w0
        add     w3, w3, w9
        mul     w0, w2, w12
        mul     w1, w3, w12
        sxth    w0, w0
        sxth    w1, w1
        madd    w0, w0, w11, w2
        madd    w1, w1, w11, w3
        asr     w0, w0, #16
        sturh   w0, [x7, #-2]
        asr     w1, w1, #16
        sturh   w1, [x7, #-4]
        cmp     x4, x13
        b.ne    L4600
        ret

// mlkem512_polyvec_mulcache_compute (0x28 bytes)
L4694:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L4240
        ldr     x30, [sp, #16]
        add     x1, x20, #0x200
        add     x0, x19, #0x100
        ldp     x19, x20, [sp], #32
        b       L4240
        nop

// mlkem512_polyvec_reduce (0x18 bytes)
L46c0:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L4190
        add     x0, x19, #0x200
        ldp     x19, x30, [sp], #16
        b       L4190
        nop
        nop

// mlkem512_polyvec_add (0x28 bytes)
L46e0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L41e0
        ldr     x30, [sp, #16]
        add     x1, x20, #0x200
        add     x0, x19, #0x200
        ldp     x19, x20, [sp], #32
        b       L41e0
        nop
        nop

// mlkem512_polyvec_tomont (0x18 bytes)
L4710:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L4140
        add     x0, x19, #0x200
        ldp     x19, x30, [sp], #16
        b       L4140
        nop
        nop

// mlkem512_poly_getnoise_eta1_4x (0x158 bytes)
L4730:
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
        .inst   0xf00000c4  // adrp x4, 0x1f000
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
        bl      L2a20
        mov     x1, x20
        mov     x0, x24
        bl      L4ec4
        mov     x1, x26
        mov     x0, x23
        bl      L4ec4
        mov     x1, x25
        mov     x0, x22
        bl      L4ec4
        cbz     x21,L4818
        mov     x1, x27
        mov     x0, x21
        bl      L4ec4
L4818:
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
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1144]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4884
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x30, [sp, #80]
        add     sp, sp, #0x480
        ret
L4884:
        bl      L0830
        nop
        nop

// mlkem512_poly_getnoise_eta2 (0xa4 bytes)
L4890:
        stp     x19, x20, [sp, #-240]!
        mov     x3, #0x21
        add     x19, sp, #0x3f
        stp     x21, x30, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        .inst   0xf00000c4  // adrp x4, 0x1f000
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
        bl      L2570
        mov     x1, x19
        mov     x0, x21
        bl      L4e40
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     xzr, xzr, [x19, #128]
        stp     xzr, xzr, [x20, #16]
        strb    wzr, [x20, #32]
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4930
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #240
        ret
L4930:
        bl      L0830

// mlkem512_poly_getnoise_eta1122_4x (0x154 bytes)
L4934:
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
        .inst   0xf00000c4  // adrp x4, 0x1f000
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
        bl      L2a20
        mov     x1, x20
        mov     x0, x24
        bl      L4ec4
        mov     x1, x27
        mov     x0, x23
        bl      L4ec4
        mov     x1, x26
        mov     x0, x22
        bl      L4e40
        mov     x1, x25
        mov     x0, x21
        bl      L4e40
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
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1144]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4a84
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x30, [sp, #80]
        add     sp, sp, #0x480
        ret
L4a84:
        bl      L0830
        nop
        nop

// mlk_rej_uniform_c.constprop.0 (0x9c bytes)
L4a90:
        mov     x8, x0
        mov     w0, w1
        cmp     w1, #0xff
        b.hi    L4b28
        mov     w9, #0x3
        mov     w11, #0xd00
        sub     w9, w9, w2
        mov     w10, #0xff
        b       L4ae4
L4ab4:
        cmp     w1, #0xd00
        mov     w5, w0
        ccmp    w0, w10, #0x2, le
        b.hi    L4ad4
L4ac4:
        add     w0, w5, #0x1
        strh    w1, [x8, w5, uxtw #1]
        cmp     w0, #0x100
        b.eq    L4b28
L4ad4:
        add     x2, x2, #0x3
        add     w1, w9, w2
        cmp     w3, w1
        b.cc    L4b28
L4ae4:
        ldrb    w4, [x2, #1]
        add     w5, w0, #0x1
        ldrb    w7, [x2]
        ldrb    w1, [x2, #2]
        lsr     w6, w4, #4
        orr     w4, w7, w4, lsl #8
        and     w4, w4, #0xfff
        orr     w1, w6, w1, lsl #4
        cmp     w4, #0xd00
        b.gt    L4ab4
        strh    w4, [x8, w0, uxtw #1]
        cmp     w5, #0xff
        ccmp    w1, w11, #0x0, ls
        mov     w0, w5
        b.le    L4ac4
        cmp     w0, #0x100
        b.ne    L4ad4
L4b28:
        ret
        nop

// mlkem_poly_rej_uniform_x4 (0x208 bytes)
L4b30:
        sub     sp, sp, #0xbc0
        .inst   0xf00000c5  // adrp x5, 0x1f000
        ldr     x5, [x5, #4088]
        stp     x19, x20, [sp]
        mov     x20, x1
        mov     x19, x4
        stp     x21, x22, [sp, #16]
        add     x22, sp, #0x9f
        and     x22, x22, #0xffffffffffffffe0
        stp     x23, x24, [sp, #32]
        mov     x21, x2
        add     x23, x22, #0x600
        stp     x25, x26, [sp, #48]
        add     x26, x22, #0x800
        add     x24, x22, #0x400
        stp     x27, x28, [sp, #64]
        mov     x27, x3
        mov     x28, x0
        str     x30, [sp, #80]
        add     x25, x22, #0x200
        stp     x0, x1, [sp, #96]
        mov     x0, x26
        stp     x2, x3, [sp, #112]
        ldr     x1, [x5]
        str     x1, [sp, #3000]
        mov     x1, #0x0
        bl      L2a00
        add     x4, x19, #0xc0
        add     x3, x19, #0x80
        add     x2, x19, #0x40
        mov     x1, x19
        mov     x0, x26
        mov     x5, #0x22
        bl      L2910
        mov     x5, x26
        mov     x4, #0x3
        mov     x3, x23
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L2974
        mov     w3, #0x1f8
        mov     x2, x22
        mov     x0, x28
        mov     w1, #0x0
        bl      L4a90
        mov     w19, w0
        mov     x2, x25
        mov     x0, x20
        mov     w1, #0x0
        bl      L4a90
        mov     x2, x24
        mov     w20, w0
        mov     w1, #0x0
        mov     x0, x21
        bl      L4a90
        mov     w21, w0
        mov     w1, #0x0
        mov     x0, x27
        mov     x2, x23
        bl      L4a90
        cmp     w21, #0xff
        mov     w27, #0xff
        ccmp    w0, w27, #0x0, hi
        mov     w28, w0
        cset    w0, ls
        cmp     w20, w27
        ccmp    w19, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbz     w0,L4ce0
        nop
L4c50:
        mov     x5, x26
        mov     x4, #0x1
        mov     x3, x23
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L2974
        ldr     x0, [sp, #96]
        mov     w3, #0xa8
        mov     w1, w19
        mov     x2, x22
        bl      L4a90
        mov     w19, w0
        ldr     x0, [sp, #104]
        mov     w1, w20
        mov     x2, x25
        bl      L4a90
        mov     w20, w0
        ldr     x0, [sp, #112]
        mov     w1, w21
        mov     x2, x24
        bl      L4a90
        mov     w21, w0
        ldr     x0, [sp, #120]
        mov     w1, w28
        mov     x2, x23
        bl      L4a90
        cmp     w0, #0xff
        ccmp    w21, w27, #0x0, hi
        mov     w28, w0
        cset    w0, ls
        cmp     w19, #0xff
        ccmp    w20, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbnz    w0,L4c50
L4ce0:
        mov     x0, x26
        bl      L2a04
        mov     x0, x22
        mov     x2, #0x800
        mov     w1, #0x0
        bl      L0840
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #3000]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4d34
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0xbc0
        ret
L4d34:
        bl      L0830
        nop
        nop

// mlkem_poly_rej_uniform (0xfc bytes)
L4d40:
        sub     sp, sp, #0x330
        .inst   0xf00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        stp     x19, x20, [sp]
        mov     x19, x1
        add     x20, sp, #0x4f
        stp     x21, x22, [sp, #16]
        and     x20, x20, #0xffffffffffffffe0
        add     x22, x20, #0x200
        str     x30, [sp, #32]
        mov     x21, x0
        mov     x0, x22
        ldr     x1, [x2]
        str     x1, [sp, #808]
        mov     x1, #0x0
        bl      L2540
        mov     x1, x19
        mov     x0, x22
        mov     x2, #0x22
        bl      L24d0
        mov     x2, x22
        mov     x0, x20
        mov     x1, #0x3
        bl      L24e4
        mov     x2, x20
        mov     x0, x21
        mov     w3, #0x1f8
        mov     w1, #0x0
        bl      L4a90
        cmp     w0, #0xff
        b.hi    L4df0
        mov     w19, w0
L4dc0:
        mov     x2, x22
        mov     x0, x20
        mov     x1, #0x1
        bl      L24e4
        mov     w1, w19
        mov     x2, x20
        mov     x0, x21
        mov     w3, #0xa8
        bl      L4a90
        mov     w19, w0
        cmp     w0, #0xff
        b.ls    L4dc0
L4df0:
        mov     x0, x22
        bl      L2544
        mov     x0, x20
        mov     x2, #0x1f8
        mov     w1, #0x0
        bl      L0840
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #808]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4e38
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        add     sp, sp, #0x330
        ret
L4e38:
        bl      L0830
        nop

// mlkem_poly_cbd2 (0x84 bytes)
L4e40:
        mov     x5, x0
        .inst   0xd0000000  // adrp x0, 0x6000
        .inst   0xd0000002  // adrp x2, 0x6000
        mov     x4, x1
        ldr     q7, [x0, #608]
        .inst   0xd0000000  // adrp x0, 0x6000
        ldr     q16, [x2, #592]
        mov     x1, #0x0
        ldr     q6, [x0, #624]
        .inst   0xd0000000  // adrp x0, 0x6000
        movi    v3.8h, #0x3
        ldr     q5, [x0, #640]
L4e70:
        lsl     x2, x1, #4
        ldr     w0, [x4, x1, lsl #2]
        add     x1, x1, #0x1
        and     w3, w0, #0x55555555
        lsr     w0, w0, #1
        and     w0, w0, #0x55555555
        add     w0, w0, w3
        dup     v0.4s, w0
        ushl    v1.4s, v0.4s, v16.4s
        ushl    v4.4s, v0.4s, v7.4s
        ushl    v2.4s, v0.4s, v6.4s
        ushl    v0.4s, v0.4s, v5.4s
        uzp1    v1.8h, v1.8h, v4.8h
        uzp1    v2.8h, v2.8h, v0.8h
        and     v0.16b, v1.16b, v3.16b
        and     v1.16b, v2.16b, v3.16b
        sub     v0.8h, v0.8h, v1.8h
        str     q0, [x5, x2]
        cmp     x1, #0x20
        b.ne    L4e70
        ret

// mlkem_poly_cbd3 (0x8c bytes)
L4ec4:
        mov     x2, x1
        mov     x4, x0
        .inst   0xd0000001  // adrp x1, 0x6000
        .inst   0xd0000000  // adrp x0, 0x6000
        movi    v2.4h, #0x7
        mov     w3, #0x9249
        ldr     q4, [x1, #656]
        add     x6, x2, #0xc0
        ldr     q3, [x0, #672]
        movk    w3, #0x24, lsl #16
        nop
L4ef0:
        ldrb    w0, [x2, #2]
        add     x2, x2, #0x3
        ldurb   w1, [x2, #-2]
        ldurb   w5, [x2, #-3]
        lsl     w0, w0, #16
        orr     w1, w0, w1, lsl #8
        orr     w1, w1, w5
        and     w5, w1, w3
        and     w0, w3, w1, lsr #1
        and     w1, w3, w1, lsr #2
        add     w0, w0, w1
        add     w0, w0, w5
        dup     v0.4s, w0
        ushl    v1.4s, v0.4s, v4.4s
        ushl    v0.4s, v0.4s, v3.4s
        xtn     v1.4h, v1.4s
        xtn     v0.4h, v0.4s
        and     v1.8b, v1.8b, v2.8b
        and     v0.8b, v0.8b, v2.8b
        sub     v0.4h, v1.4h, v0.4h
        str     d0, [x4], #8
        cmp     x6, x2
        b.ne    L4ef0
        ret

// mlkem768_gen_matrix (0x16c bytes)
L4f50:
        stp     x19, x20, [sp, #-320]!
        mov     x20, x0
        .inst   0xf00000c4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        add     x19, sp, #0x3f
        str     x30, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        mov     x3, x19
        add     x0, x19, #0x100
        ldr     x5, [x4]
        str     x5, [sp, #312]
        mov     x5, #0x0
L4f80:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x3]
        add     x3, x3, #0x40
        cmp     x3, x0
        b.ne    L4f80
        strh    wzr, [x19, #32]
        cbnz    w2,L5074
        mov     w7, #0x1
        mov     w6, #0x2
        mov     w5, #0x100
        mov     x4, x19
        add     x3, x20, #0x600
        add     x2, x20, #0x400
        add     x1, x20, #0x200
        mov     x0, x20
        strh    w7, [x19, #96]
        strh    w6, [x19, #160]
        strh    w5, [x19, #224]
        bl      L4b30
        mov     w7, #0x2
        mov     w5, w7
        mov     w8, #0x0
        mov     w6, #0x1
L4fdc:
        mov     w9, #0x101
        mov     x4, x19
        add     x3, x20, #0xe00
        add     x2, x20, #0xc00
        add     x1, x20, #0xa00
        add     x0, x20, #0x800
        strh    w9, [x19, #32]
        strb    w5, [x19, #96]
        strb    w6, [x19, #97]
        strb    w8, [x19, #160]
        strb    w7, [x19, #161]
        strb    w6, [x19, #224]
        strb    w5, [x19, #225]
        bl      L4b30
        mov     w2, #0x202
        add     x0, x20, #0x1, lsl #12
        mov     x1, x19
        strh    w2, [x19, #32]
        bl      L4d40
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        stp     q0, q0, [x19, #192]
        stp     q0, q0, [x19, #224]
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #312]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L50b8
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #320
        ret
L5074:
        mov     w7, #0x100
        mov     w6, #0x200
        mov     w5, #0x1
        mov     x4, x19
        add     x3, x20, #0x600
        add     x2, x20, #0x400
        add     x1, x20, #0x200
        mov     x0, x20
        strh    w7, [x19, #96]
        strh    w6, [x19, #160]
        strh    w5, [x19, #224]
        bl      L4b30
        mov     w8, #0x2
        mov     w7, #0x0
        mov     w6, w8
        mov     w5, #0x1
        b       L4fdc
L50b8:
        bl      L0830
        nop

// mlkem768_indcpa_keypair_derand (0x248 bytes)
L50c0:
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
        .inst   0xd00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        ldr     x0, [x2]
        str     x0, [sp, #10248]
        mov     x0, #0x0
        stp     q0, q1, [x23]
        mov     x0, x21
        mov     x2, #0x21
        strb    w27, [x25, #1888]
        bl      L26f4
        mov     x1, x21
        mov     x0, x19
        mov     w2, #0x0
        bl      L4f50
        strb    w22, [sp]
        mov     x4, x28
        add     x2, x20, #0x400
        add     x1, x20, #0x200
        mov     x0, x20
        mov     w7, #0x2
        mov     w6, #0x1
        mov     w5, #0x0
        mov     x3, #0x0
        bl      L60a0
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
        bl      L60a0
        mov     x0, x20
        bl      L5f00
        mov     x0, x26
        bl      L5f00
        mov     x25, x24
        mov     x28, x19
        mov     x1, x20
        mov     x0, x27
        mov     w22, #0x0
        bl      L5ff0
L51e4:
        mov     x1, x28
        mov     x0, x25
        mov     x3, x27
        mov     x2, x20
        add     w22, w22, #0x1
        bl      L5f40
        add     x28, x28, #0x600
        add     x25, x25, #0x200
        cmp     w22, #0x3
        b.ne    L51e4
        mov     x0, x24
        bl      L6080
        mov     x1, x26
        mov     x0, x24
        bl      L6044
        mov     x0, x24
        bl      L6024
        mov     x0, x20
        bl      L6024
        ldr     x0, [sp, #120]
        mov     x1, x20
        bl      L5e90
        ldr     x22, [sp, #112]
        mov     x1, x24
        mov     x0, x22
        bl      L5e90
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
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #10248]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L5304
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
L5304:
        bl      L0830
        nop
        nop

// mlkem768_indcpa_enc (0x2c8 bytes)
L5310:
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
        .inst   0xd00000c2  // adrp x2, 0x1f000
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
        bl      L5ec4
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
        bl      L22e0
        mov     x1, x25
        mov     x0, x19
        mov     w2, #0x1
        bl      L4f50
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
        bl      L60a0
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
        bl      L60a0
        mov     w21, #0x0
        mov     x0, x20
        bl      L5f00
        mov     x1, x20
        mov     x0, x23
        bl      L5ff0
L544c:
        mov     x1, x26
        mov     x0, x27
        mov     x3, x23
        mov     x2, x20
        add     w21, w21, #0x1
        bl      L5f40
        add     x26, x26, #0x600
        add     x27, x27, #0x200
        cmp     w21, #0x3
        b.ne    L544c
        ldr     x27, [sp, #128]
        mov     x3, x23
        mov     x2, x20
        mov     x0, #0x3100
        mov     x1, x27
        add     x21, x19, x0
        mov     x0, x21
        bl      L5f40
        mov     x0, x22
        bl      L5f20
        mov     x0, x21
        bl      L4394
        mov     x1, x24
        mov     x0, x22
        bl      L6044
        mov     x1, x28
        mov     x0, x21
        bl      L41e0
        ldr     x26, [sp, #136]
        mov     x0, x21
        mov     x1, x26
        bl      L41e0
        mov     x0, x22
        bl      L6024
        mov     x0, x21
        bl      L4190
        ldr     x0, [sp, #120]
        mov     x1, x22
        bl      L5e20
        ldr     x0, [sp, #120]
        mov     x1, x21
        add     x0, x0, #0x3c0
        bl      L1bf0
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
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #13256]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L55d4
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
L55d4:
        bl      L0830
        nop
        nop

// mlkem768_indcpa_dec (0x154 bytes)
L55e0:
        mov     x12, #0x1360
        sub     sp, sp, x12
        .inst   0xd00000c3  // adrp x3, 0x1f000
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
        bl      L5e54
        add     x1, x23, #0x3c0
        mov     x0, x21
        bl      L1da4
        add     x23, x19, #0xc00
        mov     x1, x22
        mov     x0, x19
        bl      L5ec4
        add     x22, x19, #0xf00
        mov     x0, x20
        bl      L5f00
        mov     x1, x20
        mov     x0, x23
        bl      L5ff0
        mov     x3, x23
        mov     x2, x20
        mov     x1, x19
        mov     x0, x22
        bl      L5f40
        mov     x0, x22
        bl      L4394
        mov     x1, x22
        mov     x0, x21
        bl      L4210
        mov     x0, x21
        bl      L4190
        mov     x1, x21
        mov     x0, x24
        bl      L2340
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
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4952]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L5730
        ldp     x19, x20, [sp]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x1360
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        add     sp, sp, x12
        ret
L5730:
        bl      L0830
        nop
        nop
        nop

// mlkem768_check_pk (0x138 bytes)
L5740:
        sub     sp, sp, #0xac0
        mov     x1, x0
        .inst   0xd00000c2  // adrp x2, 0x1f000
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
        bl      L5ec4
        mov     x0, x20
        bl      L6024
        mov     x0, x21
        mov     x1, x20
        bl      L5e90
        movi    v2.4s, #0x0
        mov     x0, x19
        mov     x2, x21
        add     x1, x20, #0xa80
        mov     v3.16b, v2.16b
        nop
L57a8:
        ldr     q0, [x0], #16
        ldr     q1, [x2], #16
        eor     v0.16b, v0.16b, v1.16b
        orr     v3.16b, v3.16b, v0.16b
        eor     v2.16b, v2.16b, v0.16b
        cmp     x1, x2
        b.ne    L57a8
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
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #2744]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L5874
        ldp     x21, x30, [sp, #16]
        mov     w0, w19
        ldp     x19, x20, [sp]
        add     sp, sp, #0xac0
        ret
L5874:
        bl      L0830
        nop
        nop

// mlkem768_check_sk (0xe8 bytes)
L5880:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        add     x1, x0, #0x480
        .inst   0xd00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x3f
        mov     x2, #0x4a0
        ldr     x4, [x3]
        str     x4, [sp, #88]
        mov     x4, #0x0
        and     x19, x19, #0xffffffffffffffe0
        mov     x0, x19
        bl      L2650
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
        .inst   0xd00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #88]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L5964
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #96
        ret
L5964:
        bl      L0830
        nop
        nop

// mlkem768_keypair_derand (0x94 bytes)
L5970:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        mov     x21, x0
        str     x30, [sp, #32]
        bl      L50c0
        mov     x2, #0x4a0
        mov     w20, w0
        cbnz    w0,L59d4
        mov     x1, x21
        add     x0, x19, #0x480
        bl      L0810
        mov     x1, x21
        add     x0, x19, #0x920
        mov     x2, #0x4a0
        bl      L2650
        ldp     q0, q1, [x22, #32]
        add     x19, x19, #0x940
        mov     w0, w20
        stp     q0, q1, [x19]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L59d4:
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
L5a04:
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
        cbnz    w0,L5a84
        mov     x1, x21
        mov     x0, x20
        mov     x2, x19
        bl      L5970
L5a50:
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xd00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #120]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L5a8c
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #128
        ret
L5a84:
        mov     w0, #0xfffffffd
        b       L5a50
L5a8c:
        bl      L0830

// mlkem768_enc_derand (0xe0 bytes)
L5a90:
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
        bl      L5740
        cbz     w0,L5b20
L5adc:
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
        b.ne    L5b6c
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #224
        ret
L5b20:
        ldp     q0, q1, [x22]
        mov     x1, x21
        add     x0, x19, #0x60
        mov     x2, #0x4a0
        stp     q0, q1, [x20]
        bl      L2650
        mov     x1, x20
        mov     x0, x19
        mov     x2, #0x40
        bl      L26f4
        mov     x2, x21
        mov     x0, x24
        add     x3, x19, #0x20
        mov     x1, x20
        bl      L5310
        cbnz    w0,L5adc
        ldp     q0, q1, [x19]
        stp     q0, q1, [x23]
        b       L5adc
L5b6c:
        bl      L0830

// mlkem768_enc (0x98 bytes)
L5b70:
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
        cbnz    w0,L5bfc
        mov     x2, x22
        mov     x1, x21
        mov     x0, x20
        mov     x3, x19
        bl      L5a90
L5bc8:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xd00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #104]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L5c04
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret
L5bfc:
        mov     w0, #0xfffffffd
        b       L5bc8
L5c04:
        bl      L0830
        nop
        nop

// mlkem768_dec (0x20c bytes)
L5c10:
        sub     sp, sp, #0x540
        .inst   0xd00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x5f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #16]
        stp     x23, x24, [sp, #32]
        mov     x24, x0
        mov     x23, x2
        stp     x25, x30, [sp, #48]
        mov     x25, x1
        mov     x0, x2
        ldr     x1, [x3]
        str     x1, [sp, #1336]
        mov     x1, #0x0
        bl      L5880
        cbz     w0,L5cc0
        mov     w20, w0
        add     x22, x19, #0x4a0
        add     x21, x19, #0x460
L5c64:
        mov     x0, x19
        mov     x2, #0x460
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x22]
        stp     q0, q0, [x22, #32]
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1336]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L5e18
        ldp     x21, x22, [sp, #16]
        mov     w0, w20
        ldp     x19, x20, [sp]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        add     sp, sp, #0x540
        ret
L5cc0:
        add     x22, x19, #0x4a0
        mov     x2, x23
        mov     x0, x22
        mov     x1, x25
        add     x21, x19, #0x460
        bl      L55e0
        mov     w20, w0
        cbnz    w0,L5c64
        ldr     q0, [x23, #2336]
        add     x3, x19, #0x4c0
        ldr     q1, [x23, #2352]
        mov     x1, x22
        mov     x0, x21
        mov     x2, #0x40
        stp     q0, q1, [x3]
        bl      L26f4
        add     x3, x19, #0x480
        add     x2, x23, #0x480
        mov     x1, x22
        mov     x0, x19
        bl      L5310
        mov     w20, w0
        cbnz    w0,L5c64
        movi    v2.4s, #0x0
        mov     x0, x19
        mov     x1, x25
        add     x2, x19, #0x440
        mov     v3.16b, v2.16b
L5d30:
        ldr     q0, [x1], #16
        ldr     q1, [x0], #16
        eor     v0.16b, v0.16b, v1.16b
        orr     v3.16b, v3.16b, v0.16b
        eor     v2.16b, v2.16b, v0.16b
        cmp     x0, x2
        b.ne    L5d30
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
        ldr     q0, [x23, #2368]
        and     w0, w0, #0xff
        ldr     q1, [x23, #2384]
        mov     x2, #0x440
        eor     w23, w0, w1
        mov     x1, x25
        add     x0, x19, #0x20
        stp     q0, q1, [x19]
        bl      L0810
        mov     x0, x24
        mov     x2, x19
        mov     x3, #0x460
        mov     x1, #0x20
        bl      L2570
        neg     w4, w23
        sub     x24, x24, #0x1
        mov     x0, #0x1
        nop
L5de8:
        add     x2, x21, x0
        mov     w1, w4
        ldurb   w2, [x2, #-1]
        ldrb    w3, [x24, x0]
        eor     w3, w2, w3
        and     w1, w3, w1, asr #16
        eor     w2, w2, w1
        strb    w2, [x24, x0]
        add     x0, x0, #0x1
        cmp     x0, #0x21
        b.ne    L5de8
        b       L5c64
L5e18:
        bl      L0830
        nop

// mlkem768_polyvec_compress_du (0x34 bytes)
L5e20:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L1cd0
        add     x1, x20, #0x200
        add     x0, x19, #0x140
        bl      L1cd0
        ldr     x30, [sp, #16]
        add     x1, x20, #0x400
        add     x0, x19, #0x280
        ldp     x19, x20, [sp], #32
        b       L1cd0

// mlkem768_polyvec_decompress_du (0x34 bytes)
L5e54:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L1df0
        add     x1, x20, #0x140
        add     x0, x19, #0x200
        bl      L1df0
        ldr     x30, [sp, #16]
        add     x1, x20, #0x280
        add     x0, x19, #0x400
        ldp     x19, x20, [sp], #32
        b       L1df0
        nop
        nop

// mlkem768_polyvec_tobytes (0x34 bytes)
L5e90:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L2260
        add     x1, x20, #0x200
        add     x0, x19, #0x180
        bl      L2260
        ldr     x30, [sp, #16]
        add     x1, x20, #0x400
        add     x0, x19, #0x300
        ldp     x19, x20, [sp], #32
        b       L2260

// mlkem768_polyvec_frombytes (0x34 bytes)
L5ec4:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L22a0
        add     x1, x20, #0x180
        add     x0, x19, #0x200
        bl      L22a0
        ldr     x30, [sp, #16]
        add     x1, x20, #0x300
        add     x0, x19, #0x400
        ldp     x19, x20, [sp], #32
        b       L22a0
        nop
        nop

// mlkem768_polyvec_ntt (0x20 bytes)
L5f00:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L42b4
        add     x0, x19, #0x200
        bl      L42b4
        add     x0, x19, #0x400
        ldp     x19, x30, [sp], #16
        b       L42b4

// mlkem768_polyvec_invntt_tomont (0x20 bytes)
L5f20:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L4394
        add     x0, x19, #0x200
        bl      L4394
        add     x0, x19, #0x400
        ldp     x19, x30, [sp], #16
        b       L4394

// mlkem768_polyvec_basemul_acc_montgomery_cached (0xac bytes)
L5f40:
        add     x7, x0, #0x2
        mov     x6, x1
        add     x5, x2, #0x2
        add     x17, x3, #0x100
        mov     w10, #0xfffff301
        mov     w9, #0xfffff2ff
L5f58:
        mov     x1, x3
        add     x14, x6, #0x2
        sub     x13, x5, #0x2
        mov     x0, #0x0
        mov     w4, #0x0
        mov     w2, #0x0
L5f70:
        ldrsh   w16, [x14, x0]
        add     x1, x1, #0x100
        ldrsh   w15, [x6, x0]
        ldrsh   w8, [x13, x0]
        ldrsh   w11, [x5, x0]
        add     x0, x0, #0x200
        ldursh  w12, [x1, #-256]
        mul     w18, w15, w8
        mul     w8, w16, w8
        madd    w12, w12, w16, w18
        madd    w8, w11, w15, w8
        add     w2, w2, w12
        add     w4, w4, w8
        cmp     x0, #0x600
        b.ne    L5f70
        mul     w1, w2, w10
        add     x3, x3, #0x2
        mul     w0, w4, w10
        add     x6, x6, #0x4
        add     x5, x5, #0x4
        sxth    w1, w1
        sxth    w0, w0
        madd    w1, w1, w9, w2
        madd    w0, w0, w9, w4
        asr     w1, w1, #16
        sturh   w1, [x7, #-2]
        asr     w0, w0, #16
        strh    w0, [x7], #4
        cmp     x17, x3
        b.ne    L5f58
        ret
        nop

// mlkem768_polyvec_mulcache_compute (0x34 bytes)
L5ff0:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L4240
        add     x1, x20, #0x200
        add     x0, x19, #0x100
        bl      L4240
        ldr     x30, [sp, #16]
        add     x1, x20, #0x400
        add     x0, x19, #0x200
        ldp     x19, x20, [sp], #32
        b       L4240

// mlkem768_polyvec_reduce (0x20 bytes)
L6024:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L4190
        add     x0, x19, #0x200
        bl      L4190
        add     x0, x19, #0x400
        ldp     x19, x30, [sp], #16
        b       L4190

// mlkem768_polyvec_add (0x34 bytes)
L6044:
        stp     x19, x20, [sp, #-32]!
        mov     x19, x0
        mov     x20, x1
        str     x30, [sp, #16]
        bl      L41e0
        add     x1, x20, #0x200
        add     x0, x19, #0x200
        bl      L41e0
        ldr     x30, [sp, #16]
        add     x1, x20, #0x400
        add     x0, x19, #0x400
        ldp     x19, x20, [sp], #32
        b       L41e0
        nop
        nop

// mlkem768_polyvec_tomont (0x20 bytes)
L6080:
        stp     x19, x30, [sp, #-16]!
        mov     x19, x0
        bl      L4140
        add     x0, x19, #0x200
        bl      L4140
        add     x0, x19, #0x400
        ldp     x19, x30, [sp], #16
        b       L4140

// mlkem768_poly_getnoise_eta1_4x (0x158 bytes)
L60a0:
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
        .inst   0xb00000c4  // adrp x4, 0x1f000
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
        bl      L2a20
        mov     x1, x20
        mov     x0, x24
        bl      L4e40
        mov     x1, x26
        mov     x0, x23
        bl      L4e40
        mov     x1, x25
        mov     x0, x22
        bl      L4e40
        cbz     x21,L6188
        mov     x1, x27
        mov     x0, x21
        bl      L4e40
L6188:
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
        .inst   0xb00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #888]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L61f4
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x30, [sp, #80]
        add     sp, sp, #0x380
        ret
L61f4:
        bl      L0830

// Padding (0x61f8 to 0x6200)

        .quad   0x0000000000000000

// The read-only data (0x6200 to 0x6480)

        .quad   0x00000d0100000d01
        .quad   0x00000d0100000d01
        .quad   0x0d010d010d010d01
        .quad   0x0d010d010d010d01
        .quad   0x0549054905490549
        .quad   0x0549054905490549
        .quad   0xf301f301f301f301
        .quad   0xf301f301f301f301
        .quad   0x05a105a105a105a1
        .quad   0x05a105a105a105a1
        .quad   0xfffffffc00000000
        .quad   0xfffffff4fffffff8
        .quad   0xffffffecfffffff0
        .quad   0xffffffe4ffffffe8
        .quad   0xfffffffafffffffe
        .quad   0xfffffff2fffffff6
        .quad   0xffffffeaffffffee
        .quad   0xffffffe2ffffffe6
        .quad   0xfffffffa00000000
        .quad   0xffffffeefffffff4
        .quad   0xfffffff7fffffffd
        .quad   0xffffffebfffffff1
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
