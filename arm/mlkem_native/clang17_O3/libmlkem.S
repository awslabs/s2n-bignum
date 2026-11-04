// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// The code and read-only data of mlkem-native's libmlkem.so (clang 17, -O3)
//
// This is a transcription of the binary
// binaries/multilevel/clang17/O3/libmlkem.so from the binary branch of
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

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_libmlkem_clang17_O3)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_libmlkem_clang17_O3)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_libmlkem_clang17_O3):

// ELF header and dynamic linking information (0x0 to 0x7f0)

        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x0000000100b70003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x000000000003f0b0
        .quad   0x0038004000000000
        .quad   0x0018001900400005
        .quad   0x0000000500000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000010d90
        .quad   0x0000000000010d90
        .quad   0x0000000000010000
        .quad   0x0000000600000001
        .quad   0x000000000001fe38
        .quad   0x000000000002fe38
        .quad   0x000000000002fe38
        .quad   0x00000000000001c8
        .quad   0x00000000000001c8
        .quad   0x0000000000010000
        .quad   0x0000000600000002
        .quad   0x000000000001fe38
        .quad   0x000000000002fe38
        .quad   0x000000000002fe38
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
        .quad   0x000000000001fe38
        .quad   0x000000000002fe38
        .quad   0x000000000002fe38
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
        .quad   0x0000000000007dc0
        .quad   0x00000000000004d8
        .quad   0x000800120000003e
        .quad   0x00000000000014e8
        .quad   0x00000000000000e0
        .quad   0x000800120000010d
        .quad   0x0000000000007888
        .quad   0x000000000000049c
        .quad   0x00080012000001a9
        .quad   0x000000000000e9dc
        .quad   0x0000000000000228
        .quad   0x000800120000014d
        .quad   0x000000000000e4f0
        .quad   0x00000000000000e0
        .quad   0x0008001200000071
        .quad   0x0000000000001660
        .quad   0x00000000000000f4
        .quad   0x000800120000002b
        .quad   0x0000000000001398
        .quad   0x0000000000000150
        .quad   0x00080012000000a4
        .quad   0x0000000000001938
        .quad   0x000000000000009c
        .quad   0x00080012000000e4
        .quad   0x00000000000076fc
        .quad   0x0000000000000098
        .quad   0x000800120000013b
        .quad   0x000000000000e3a0
        .quad   0x0000000000000150
        .quad   0x0008001200000177
        .quad   0x000000000000e668
        .quad   0x00000000000000f4
        .quad   0x000800120000008f
        .quad   0x0000000000001754
        .quad   0x00000000000001e4
        .quad   0x000800120000015f
        .quad   0x000000000000e5d0
        .quad   0x0000000000000098
        .quad   0x0008001200000121
        .quad   0x0000000000007d24
        .quad   0x000000000000009c
        .quad   0x00080012000000d2
        .quad   0x000000000000761c
        .quad   0x00000000000000e0
        .quad   0x0008001200000188
        .quad   0x000000000000e75c
        .quad   0x00000000000001e4
        .quad   0x000800120000019c
        .quad   0x000000000000e940
        .quad   0x000000000000009c
        .quad   0x00080012000000c0
        .quad   0x0000000000007200
        .quad   0x000000000000041c
        .quad   0x00080012000000b2
        .quad   0x00000000000019d4
        .quad   0x0000000000000228
        .quad   0x00080012000000fc
        .quad   0x0000000000007794
        .quad   0x00000000000000f4
        .quad   0x0008001200000051
        .quad   0x00000000000015c8
        .quad   0x0000000000000098
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
        .quad   0x000000000002fff8
        .quad   0x0000000200000401
        .quad   0x0000000000000000
        .quad   0x000000000002ffd0
        .quad   0x0000000300000402
        .quad   0x0000000000000000
        .quad   0x000000000002ffd8
        .quad   0x0000000400000402
        .quad   0x0000000000000000
        .quad   0x000000000002ffe0
        .quad   0x0000000500000402
        .quad   0x0000000000000000
        .quad   0x000000000002ffe8
        .quad   0x0000000600000402
        .quad   0x0000000000000000

// The procedure linkage table and the code (0x7f0 to 0xf154)
// .plt
        stp     x16, x30, [sp, #-16]!
        .inst   0xf0000170  // adrp x16, 0x2f000
        ldr     x17, [x16, #4040]
        add     x16, x16, #0xfc8
        br      x17
        nop
        nop
        nop
L0810:
        .inst   0xf0000170  // adrp x16, 0x2f000
        ldr     x17, [x16, #4048]
        add     x16, x16, #0xfd0
        br      x17
L0820:
        .inst   0xf0000170  // adrp x16, 0x2f000
        ldr     x17, [x16, #4056]
        add     x16, x16, #0xfd8
        br      x17
L0830:
        .inst   0xf0000170  // adrp x16, 0x2f000
        ldr     x17, [x16, #4064]
        add     x16, x16, #0xfe0
        br      x17
L0840:
        .inst   0xf0000170  // adrp x16, 0x2f000
        ldr     x17, [x16, #4072]
        add     x16, x16, #0xfe8
        br      x17

// mlkem1024_gen_matrix (0x204 bytes)
L0850:
        stp     x29, x30, [sp, #-96]!
        stp     x28, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0x160
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xf0000168  // adrp x8, 0x2f000
        add     x9, x0, #0x800
        cmp     w2, #0x0
        add     x2, x0, #0x400
        cset    w21, ne
        cset    w22, eq
        ldr     x8, [x8, #4088]
        add     x3, x0, #0x600
        lsl     w23, w22, #1
        lsl     w25, w21, #1
        add     x4, sp, #0x40
        mov     x19, x0
        ldr     x8, [x8]
        str     x8, [sp, #344]
        add     x8, x0, #0xa00
        ldp     q0, q1, [x1]
        add     x1, x0, #0x200
        strh    wzr, [sp, #96]
        stp     x8, x9, [sp, #32]
        add     x9, x0, #0xc00
        add     x8, x0, #0xe00
        strb    w22, [sp, #160]
        strb    w21, [sp, #161]
        strb    w23, [sp, #224]
        stp     x8, x9, [sp, #16]
        mov     w8, #0x3
        csel    w10, w8, wzr, eq
        mov     w9, #0x1
        csel    w20, wzr, w8, eq
        csinc   w28, w8, wzr, eq
        csinc   w24, w8, wzr, ne
        mov     w8, #0x2
        cinc    w26, w9, eq
        cinc    w27, w9, ne
        cinc    w9, w8, eq
        cinc    w8, w8, ne
        stp     q0, q1, [sp, #64]
        stp     q0, q1, [sp, #128]
        stp     q0, q1, [sp, #192]
        stp     q0, q1, [sp, #256]
        stp     w9, w10, [sp, #56]
        str     w8, [sp, #52]
        strb    w25, [sp, #225]
        strb    w10, [sp, #288]
        strb    w20, [sp, #289]
        bl      Lc4fc
        ldp     x1, x0, [sp, #32]
        mov     w8, #0x101
        add     x4, sp, #0x40
        ldp     x3, x2, [sp, #16]
        strb    w21, [sp, #96]
        strb    w22, [sp, #97]
        strb    w26, [sp, #224]
        strh    w8, [sp, #160]
        strb    w27, [sp, #225]
        strb    w28, [sp, #288]
        strb    w24, [sp, #289]
        bl      Lc4fc
        mov     w8, #0x202
        mov     w9, #0x1200
        strb    w23, [sp, #97]
        add     x1, x19, x9
        mov     w9, #0x1600
        add     x0, x19, #0x1, lsl #12
        strh    w8, [sp, #224]
        mov     w8, #0x1400
        ldp     w23, w21, [sp, #52]
        add     x2, x19, x8
        add     x3, x19, x9
        add     x4, sp, #0x40
        strb    w25, [sp, #96]
        strb    w27, [sp, #160]
        strb    w26, [sp, #161]
        strb    w21, [sp, #288]
        strb    w23, [sp, #289]
        bl      Lc4fc
        ldr     w9, [sp, #60]
        mov     w10, #0x1e00
        mov     w8, #0x303
        add     x3, x19, x10
        add     x4, sp, #0x40
        strb    w20, [sp, #96]
        strb    w9, [sp, #97]
        mov     w9, #0x1800
        add     x0, x19, x9
        mov     w9, #0x1a00
        add     x1, x19, x9
        mov     w9, #0x1c00
        add     x2, x19, x9
        strb    w24, [sp, #160]
        strb    w28, [sp, #161]
        strb    w23, [sp, #224]
        strb    w21, [sp, #225]
        strh    w8, [sp, #288]
        bl      Lc4fc
        movi    v0.2d, #0x0
        add     x8, sp, #0x40
        stp     q0, q0, [sp, #64]
        stp     q0, q0, [sp, #96]
        stp     q0, q0, [sp, #128]
        stp     q0, q0, [sp, #160]
        stp     q0, q0, [sp, #192]
        stp     q0, q0, [sp, #224]
        stp     q0, q0, [sp, #256]
        stp     q0, q0, [sp, #288]
        .inst   0xf0000168  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #344]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L0a50
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L0a50:
        bl      L0830

// mlkem1024_indcpa_keypair_derand (0x298 bytes)
L0a54:
        stp     x29, x30, [sp, #-96]!
        stp     x28, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0x3, lsl #12
        sub     x9, x9, #0xcc0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xf0000168  // adrp x8, 0x2f000
        mov     x20, x1
        mov     x19, x0
        add     x23, sp, #0x3, lsl #12
        add     x0, sp, #0x3, lsl #12
        add     x1, sp, #0x3, lsl #12
        ldr     x8, [x8, #4088]
        add     x23, x23, #0xc20
        add     x0, x0, #0xc60
        add     x1, x1, #0xc20
        add     x22, sp, #0x3, lsl #12
        add     x24, sp, #0x3, lsl #12
        ldr     x8, [x8]
        add     x22, x22, #0xc60
        add     x21, x22, #0x20
        add     x24, x24, #0xc20
        str     x8, [sp, #15544]
        mov     w8, #0x4
        ldp     q0, q1, [x2]
        mov     w2, #0x21
        strb    w8, [x23, #32]
        str     q0, [sp, #15392]
        str     q1, [sp, #15408]
        bl      L5468
        add     x0, sp, #0x1, lsl #12
        add     x1, sp, #0x3, lsl #12
        add     x0, x0, #0xc20
        add     x1, x1, #0xc60
        mov     w2, wzr
        add     x25, sp, #0x1, lsl #12
        add     x25, x25, #0xc20
        bl      L0850
        add     x26, sp, #0x420
        mov     w8, #0x3
        add     x1, x26, #0x200
        add     x2, x26, #0x400
        add     x3, x26, #0x600
        add     x0, sp, #0x420
        mov     x4, x21
        mov     w5, wzr
        mov     w6, #0x1
        mov     w7, #0x2
        strb    w8, [sp]
        bl      L2078
        add     x27, sp, #0x1, lsl #12
        add     x0, sp, #0x1, lsl #12
        add     x27, x27, #0x420
        mov     w8, #0x7
        add     x1, x27, #0x200
        add     x2, x27, #0x400
        add     x3, x27, #0x600
        add     x0, x0, #0x420
        mov     x4, x21
        mov     w5, #0x4
        mov     w6, #0x5
        mov     w7, #0x6
        strb    w8, [sp]
        bl      L2078
        add     x0, sp, #0x420
        bl      L1cfc
        add     x0, sp, #0x1, lsl #12
        add     x0, x0, #0x420
        bl      L1cfc
        add     x0, sp, #0x20
        add     x1, sp, #0x420
        add     x28, sp, #0x20
        bl      L1fa8
        add     x1, sp, #0x1, lsl #12
        add     x0, sp, #0xc20
        add     x1, x1, #0xc20
        add     x2, sp, #0x420
        add     x3, sp, #0x20
        add     x21, sp, #0xc20
        bl      L1d4c
        add     x0, x21, #0x200
        add     x1, x25, #0x800
        add     x2, sp, #0x420
        add     x3, sp, #0x20
        bl      L1d4c
        add     x0, x21, #0x400
        add     x1, x25, #0x1, lsl #12
        add     x2, sp, #0x420
        add     x3, sp, #0x20
        bl      L1d4c
        mov     w8, #0x1800
        add     x0, x21, #0x600
        add     x1, x25, x8
        add     x2, sp, #0x420
        add     x3, sp, #0x20
        bl      L1d4c
        add     x0, sp, #0xc20
        bl      L2050
        add     x1, sp, #0x1, lsl #12
        add     x0, sp, #0xc20
        add     x1, x1, #0x420
        bl      L2010
        add     x0, sp, #0xc20
        bl      L1fe8
        add     x0, sp, #0x420
        bl      L1fe8
        add     x1, sp, #0x420
        mov     x0, x20
        bl      L1c7c
        add     x1, sp, #0xc20
        mov     x0, x19
        bl      L1c7c
        ldr     q0, [sp, #15456]
        add     x0, sp, #0x20
        ldr     q1, [sp, #15472]
        mov     w1, wzr
        mov     w2, #0x400
        str     q0, [x19, #1536]
        str     q1, [x19, #1552]
        bl      L0840
        add     x0, sp, #0x420
        mov     w1, wzr
        mov     w2, #0x800
        bl      L0840
        add     x0, sp, #0xc20
        mov     w1, wzr
        mov     w2, #0x800
        bl      L0840
        add     x0, sp, #0x1, lsl #12
        add     x0, x0, #0x420
        mov     w1, wzr
        mov     w2, #0x800
        bl      L0840
        add     x0, sp, #0x1, lsl #12
        add     x0, x0, #0xc20
        mov     w1, wzr
        mov     w2, #0x2000
        bl      L0840
        movi    v0.2d, #0x0
        strb    wzr, [x23, #32]
        .inst   0xf0000168  // adrp x8, 0x2f000
        str     q0, [sp, #15408]
        str     q0, [sp, #15392]
        str     q0, [sp, #15504]
        str     q0, [sp, #15488]
        str     q0, [sp, #15472]
        str     q0, [sp, #15456]
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #15544]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L0ce8
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L0ce8:
        bl      L0830

// mlkem1024_indcpa_enc (0x478 bytes)
L0cec:
        stp     x29, x30, [sp, #-96]!
        stp     x28, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0x4, lsl #12
        sub     x9, x9, #0xa60
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xf0000168  // adrp x8, 0x2f000
        mov     x19, x0
        add     x0, sp, #0x1, lsl #12
        mov     x22, x1
        add     x0, x0, #0xa20
        mov     x1, x2
        ldr     x8, [x8, #4088]
        add     x23, sp, #0x1, lsl #12
        mov     x20, x3
        mov     x21, x2
        add     x23, x23, #0xa20
        ldr     x8, [x8]
        str     x8, [sp, #19032]
        bl      L1cbc
        ldr     q0, [x21, #1536]
        add     x0, sp, #0x620
        ldr     q1, [x21, #1552]
        mov     x1, x22
        add     x26, sp, #0x620
        str     q0, [sp, #18976]
        str     q1, [sp, #18992]
        bl      L45c0
        add     x0, sp, #0x2, lsl #12
        add     x1, sp, #0x4, lsl #12
        add     x0, x0, #0xa20
        add     x1, x1, #0xa20
        mov     w2, #0x1
        add     x22, sp, #0x2, lsl #12
        add     x22, x22, #0xa20
        bl      L0850
        add     x24, sp, #0x2, lsl #12
        add     x0, sp, #0x2, lsl #12
        add     x24, x24, #0x220
        mov     w8, #0x3
        add     x1, x24, #0x200
        add     x2, x24, #0x400
        add     x3, x24, #0x600
        add     x0, x0, #0x220
        mov     x4, x20
        mov     w5, wzr
        mov     w6, #0x1
        mov     w7, #0x2
        strb    w8, [sp]
        bl      L2078
        add     x25, sp, #0x1, lsl #12
        add     x0, sp, #0x1, lsl #12
        add     x25, x25, #0x220
        mov     w8, #0x7
        add     x1, x25, #0x200
        add     x2, x25, #0x400
        add     x3, x25, #0x600
        add     x0, x0, #0x220
        mov     x4, x20
        mov     w5, #0x4
        mov     w6, #0x5
        mov     w7, #0x6
        strb    w8, [sp]
        bl      L2078
        add     x0, sp, #0x420
        mov     x1, x20
        mov     w2, #0x8
        add     x28, sp, #0x420
        bl      L2204
        add     x0, sp, #0x2, lsl #12
        add     x0, x0, #0x220
        bl      L1cfc
        add     x1, sp, #0x2, lsl #12
        add     x0, sp, #0x20
        add     x1, x1, #0x220
        add     x21, sp, #0x20
        bl      L1fa8
        add     x1, sp, #0x2, lsl #12
        add     x2, sp, #0x2, lsl #12
        add     x0, sp, #0xa20
        add     x1, x1, #0xa20
        add     x2, x2, #0x220
        add     x3, sp, #0x20
        add     x20, sp, #0xa20
        bl      L1d4c
        add     x2, sp, #0x2, lsl #12
        add     x0, x20, #0x200
        add     x1, x22, #0x800
        add     x2, x2, #0x220
        add     x3, sp, #0x20
        bl      L1d4c
        add     x2, sp, #0x2, lsl #12
        add     x0, x20, #0x400
        add     x1, x22, #0x1, lsl #12
        add     x2, x2, #0x220
        add     x3, sp, #0x20
        bl      L1d4c
        mov     w8, #0x1800
        add     x2, sp, #0x2, lsl #12
        add     x0, x20, #0x600
        add     x1, x22, x8
        add     x2, x2, #0x220
        add     x3, sp, #0x20
        bl      L1d4c
        add     x1, sp, #0x1, lsl #12
        add     x2, sp, #0x2, lsl #12
        add     x0, sp, #0x820
        add     x1, x1, #0xa20
        add     x2, x2, #0x220
        add     x3, sp, #0x20
        add     x27, sp, #0x820
        bl      L1d4c
        add     x0, sp, #0xa20
        bl      L1d24
        add     x0, sp, #0x820
        bl      La46c
        add     x1, sp, #0x1, lsl #12
        add     x0, sp, #0xa20
        add     x1, x1, #0x220
        bl      L2010
        add     x0, sp, #0x820
        add     x1, sp, #0x420
        bl      L837c
        add     x0, sp, #0x820
        add     x1, sp, #0x620
        bl      L837c
        add     x0, sp, #0xa20
        bl      L1fe8
        add     x0, sp, #0x820
        bl      L832c
        add     x1, sp, #0xa20
        mov     x0, x19
        bl      L1bfc
        add     x0, x19, #0x580
        add     x1, sp, #0x820
        bl      L3390
        add     x0, sp, #0x20
        mov     w1, wzr
        mov     w2, #0x400
        bl      L0840
        movi    v0.2d, #0x0
        add     x0, sp, #0xa20
        mov     w1, wzr
        mov     w2, #0x800
        str     q0, [sp, #1552]
        str     q0, [sp, #1536]
        str     q0, [sp, #1520]
        str     q0, [sp, #1504]
        str     q0, [sp, #1488]
        str     q0, [sp, #1472]
        str     q0, [sp, #1456]
        str     q0, [sp, #1440]
        str     q0, [sp, #1424]
        str     q0, [sp, #1408]
        str     q0, [sp, #1392]
        str     q0, [sp, #1376]
        str     q0, [sp, #1360]
        str     q0, [sp, #1344]
        str     q0, [sp, #1328]
        str     q0, [sp, #1312]
        str     q0, [sp, #1296]
        str     q0, [sp, #1280]
        str     q0, [sp, #1264]
        str     q0, [sp, #1248]
        str     q0, [sp, #1232]
        str     q0, [sp, #1216]
        str     q0, [sp, #1200]
        str     q0, [sp, #1184]
        str     q0, [sp, #1168]
        str     q0, [sp, #1152]
        str     q0, [sp, #1136]
        str     q0, [sp, #1120]
        str     q0, [sp, #1104]
        str     q0, [sp, #1088]
        str     q0, [sp, #1072]
        str     q0, [sp, #1056]
        str     q0, [sp, #2064]
        str     q0, [sp, #2048]
        str     q0, [sp, #2032]
        str     q0, [sp, #2016]
        str     q0, [sp, #2000]
        str     q0, [sp, #1984]
        str     q0, [sp, #1968]
        str     q0, [sp, #1952]
        str     q0, [sp, #1936]
        str     q0, [sp, #1920]
        str     q0, [sp, #1904]
        str     q0, [sp, #1888]
        str     q0, [sp, #1872]
        str     q0, [sp, #1856]
        str     q0, [sp, #1840]
        str     q0, [sp, #1824]
        str     q0, [sp, #1808]
        str     q0, [sp, #1792]
        str     q0, [sp, #1776]
        str     q0, [sp, #1760]
        str     q0, [sp, #1744]
        str     q0, [sp, #1728]
        str     q0, [sp, #1712]
        str     q0, [sp, #1696]
        str     q0, [sp, #1680]
        str     q0, [sp, #1664]
        str     q0, [sp, #1648]
        str     q0, [sp, #1632]
        str     q0, [sp, #1616]
        str     q0, [sp, #1600]
        str     q0, [sp, #1584]
        str     q0, [sp, #1568]
        str     q0, [sp, #2576]
        str     q0, [sp, #2560]
        str     q0, [sp, #2544]
        str     q0, [sp, #2528]
        str     q0, [sp, #2512]
        str     q0, [sp, #2496]
        str     q0, [sp, #2480]
        str     q0, [sp, #2464]
        str     q0, [sp, #2448]
        str     q0, [sp, #2432]
        str     q0, [sp, #2416]
        str     q0, [sp, #2400]
        str     q0, [sp, #2384]
        str     q0, [sp, #2368]
        str     q0, [sp, #2352]
        str     q0, [sp, #2336]
        str     q0, [sp, #2320]
        str     q0, [sp, #2304]
        str     q0, [sp, #2288]
        str     q0, [sp, #2272]
        str     q0, [sp, #2256]
        str     q0, [sp, #2240]
        str     q0, [sp, #2224]
        str     q0, [sp, #2208]
        str     q0, [sp, #2192]
        str     q0, [sp, #2176]
        str     q0, [sp, #2160]
        str     q0, [sp, #2144]
        str     q0, [sp, #2128]
        str     q0, [sp, #2112]
        str     q0, [sp, #2096]
        str     q0, [sp, #2080]
        bl      L0840
        add     x0, sp, #0x1, lsl #12
        add     x0, x0, #0x220
        mov     w1, wzr
        mov     w2, #0x800
        bl      L0840
        add     x0, sp, #0x1, lsl #12
        add     x0, x0, #0xa20
        mov     w1, wzr
        mov     w2, #0x800
        bl      L0840
        add     x0, sp, #0x2, lsl #12
        add     x0, x0, #0x220
        mov     w1, wzr
        mov     w2, #0x800
        bl      L0840
        add     x0, sp, #0x2, lsl #12
        add     x0, x0, #0xa20
        mov     w1, wzr
        mov     w2, #0x2000
        bl      L0840
        movi    v0.2d, #0x0
        add     x8, sp, #0x4, lsl #12
        add     x8, x8, #0xa20
        str     q0, [sp, #18992]
        str     q0, [sp, #18976]
        .inst   0xd0000168  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #19032]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L1160
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L1160:
        bl      L0830

// mlkem1024_indcpa_dec (0x234 bytes)
L1164:
        stp     x29, x30, [sp, #-80]!
        str     x28, [sp, #16]
        stp     x24, x23, [sp, #32]
        stp     x22, x21, [sp, #48]
        stp     x20, x19, [sp, #64]
        mov     x29, sp
        sub     x9, sp, #0x1, lsl #12
        sub     x9, x9, #0x810
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd0000168  // adrp x8, 0x2f000
        mov     x21, x0
        add     x0, sp, #0x1, lsl #12
        mov     x19, x2
        mov     x20, x1
        add     x22, sp, #0x1, lsl #12
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #6152]
        bl      L1c3c
        add     x1, x20, #0x580
        add     x0, sp, #0x600
        add     x20, sp, #0x600
        bl      L3564
        add     x0, sp, #0x800
        mov     x1, x19
        add     x19, sp, #0x800
        bl      L1cbc
        add     x0, sp, #0x1, lsl #12
        bl      L1cfc
        mov     x0, sp
        add     x1, sp, #0x1, lsl #12
        mov     x24, sp
        bl      L1fa8
        add     x0, sp, #0x400
        add     x1, sp, #0x800
        add     x2, sp, #0x1, lsl #12
        mov     x3, sp
        add     x23, sp, #0x400
        bl      L1d4c
        add     x0, sp, #0x400
        bl      La46c
        add     x0, sp, #0x600
        add     x1, sp, #0x400
        bl      L84fc
        add     x0, sp, #0x600
        bl      L832c
        add     x1, sp, #0x600
        mov     x0, x21
        bl      L46a0
        mov     x0, sp
        mov     w1, wzr
        mov     w2, #0x400
        bl      L0840
        movi    v0.2d, #0x0
        add     x0, sp, #0x800
        mov     w1, wzr
        mov     w2, #0x800
        str     q0, [sp, #1520]
        str     q0, [sp, #1504]
        str     q0, [sp, #1488]
        str     q0, [sp, #1472]
        str     q0, [sp, #1456]
        str     q0, [sp, #1440]
        str     q0, [sp, #1424]
        str     q0, [sp, #1408]
        str     q0, [sp, #1392]
        str     q0, [sp, #1376]
        str     q0, [sp, #1360]
        str     q0, [sp, #1344]
        str     q0, [sp, #1328]
        str     q0, [sp, #1312]
        str     q0, [sp, #1296]
        str     q0, [sp, #1280]
        str     q0, [sp, #1264]
        str     q0, [sp, #1248]
        str     q0, [sp, #1232]
        str     q0, [sp, #1216]
        str     q0, [sp, #1200]
        str     q0, [sp, #1184]
        str     q0, [sp, #1168]
        str     q0, [sp, #1152]
        str     q0, [sp, #1136]
        str     q0, [sp, #1120]
        str     q0, [sp, #1104]
        str     q0, [sp, #1088]
        str     q0, [sp, #1072]
        str     q0, [sp, #1056]
        str     q0, [sp, #1040]
        str     q0, [sp, #1024]
        str     q0, [sp, #2032]
        str     q0, [sp, #2016]
        str     q0, [sp, #2000]
        str     q0, [sp, #1984]
        str     q0, [sp, #1968]
        str     q0, [sp, #1952]
        str     q0, [sp, #1936]
        str     q0, [sp, #1920]
        str     q0, [sp, #1904]
        str     q0, [sp, #1888]
        str     q0, [sp, #1872]
        str     q0, [sp, #1856]
        str     q0, [sp, #1840]
        str     q0, [sp, #1824]
        str     q0, [sp, #1808]
        str     q0, [sp, #1792]
        str     q0, [sp, #1776]
        str     q0, [sp, #1760]
        str     q0, [sp, #1744]
        str     q0, [sp, #1728]
        str     q0, [sp, #1712]
        str     q0, [sp, #1696]
        str     q0, [sp, #1680]
        str     q0, [sp, #1664]
        str     q0, [sp, #1648]
        str     q0, [sp, #1632]
        str     q0, [sp, #1616]
        str     q0, [sp, #1600]
        str     q0, [sp, #1584]
        str     q0, [sp, #1568]
        str     q0, [sp, #1552]
        str     q0, [sp, #1536]
        bl      L0840
        add     x0, sp, #0x1, lsl #12
        mov     w1, wzr
        mov     w2, #0x800
        bl      L0840
        .inst   0xd0000168  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #6152]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L1394
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #64]
        ldp     x22, x21, [sp, #48]
        ldp     x24, x23, [sp, #32]
        ldr     x28, [sp, #16]
        ldp     x29, x30, [sp], #80
        ret
L1394:
        bl      L0830

// mlkem1024_check_pk (0x150 bytes)
L1398:
        stp     x29, x30, [sp, #-48]!
        stp     x28, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0xe10
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd0000168  // adrp x8, 0x2f000
        mov     x19, x0
        add     x0, sp, #0x600
        mov     x1, x19
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #3592]
        bl      L1cbc
        add     x0, sp, #0x600
        bl      L1fe8
        mov     x0, sp
        add     x1, sp, #0x600
        mov     x20, sp
        bl      L1c7c
        movi    v0.2d, #0x0
        mov     x8, xzr
        movi    v1.2d, #0x0
        movi    v2.2d, #0x0
        movi    v3.2d, #0x0
L13fc:
        add     x9, x19, x8
        add     x10, x20, x8
        add     x8, x8, #0x20
        cmp     x8, #0x600
        ldp     q4, q5, [x9]
        ldp     q6, q7, [x10]
        eor     v4.16b, v6.16b, v4.16b
        orr     v2.16b, v4.16b, v2.16b
        eor     v5.16b, v7.16b, v5.16b
        orr     v3.16b, v5.16b, v3.16b
        eor     v0.16b, v4.16b, v0.16b
        eor     v1.16b, v5.16b, v1.16b
        b.ne    L13fc
        orr     v2.16b, v3.16b, v2.16b
        mov     w20, wzr
        ext     v3.16b, v2.16b, v2.16b, #8
        mov     x0, sp
        eor     v0.16b, v1.16b, v0.16b
        mov     w1, w20
        mov     w2, #0x600
        mov     w8, #0xfffffffc
        mov     x21, sp
        orr     v1.8b, v2.8b, v3.8b
        ext     v2.16b, v0.16b, v0.16b, #8
        fmov    x9, d1
        orr     x9, x9, x9, lsr #32
        lsr     x10, x9, #16
        eor     v0.8b, v0.8b, v2.8b
        orr     w9, w9, w10
        fmov    x10, d0
        orr     w9, w9, w9, lsr #8
        eor     x10, x10, x10, lsr #32
        sub     w9, w20, w9, uxtb
        eor     x10, x10, x10, lsr #16
        lsr     x11, x10, #8
        eor     w10, w10, w11
        eor     w9, w10, w9, lsr #16
        and     w9, w9, #0xff
        cmp     w9, w10, uxtb
        csel    w19, w20, w8, eq
        bl      L0840
        add     x0, sp, #0x600
        mov     w1, w20
        mov     w2, #0x800
        add     x20, sp, #0x600
        bl      L0840
        .inst   0xd0000168  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #3592]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L14e4
        mov     w0, w19
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldp     x28, x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L14e4:
        bl      L0830

// mlkem1024_check_sk (0xe0 bytes)
L14e8:
        stp     x29, x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x29, sp
        sub     x9, sp, #0x40
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd0000168  // adrp x8, 0x2f000
        mov     x19, x0
        add     x1, x0, #0x600
        mov     x0, sp
        mov     w2, #0x620
        mov     x20, sp
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #56]
        bl      L53c4
        ldp     q1, q2, [sp]
        mov     w8, wzr
        ldr     q0, [x19, #3120]
        ldr     q3, [x19, #3104]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v1.16b, v3.16b
        orr     v2.16b, v1.16b, v0.16b
        ext     v3.16b, v2.16b, v2.16b, #8
        eor     v0.16b, v1.16b, v0.16b
        ext     v1.16b, v0.16b, v0.16b, #8
        orr     v2.8b, v2.8b, v3.8b
        fmov    x9, d2
        eor     v0.8b, v0.8b, v1.8b
        fmov    x11, d0
        orr     x9, x9, x9, lsr #32
        lsr     x10, x9, #16
        orr     w9, w9, w10
        eor     x10, x11, x11, lsr #32
        movi    v0.2d, #0x0
        orr     w9, w9, w9, lsr #8
        eor     x10, x10, x10, lsr #16
        sub     w9, w8, w9, uxtb
        lsr     x11, x10, #8
        eor     w10, w10, w11
        eor     w9, w10, w9, lsr #16
        .inst   0xd000016b  // adrp x11, 0x2f000
        stp     q0, q0, [sp]
        and     w9, w9, #0xff
        ldr     x11, [x11, #4088]
        cmp     w9, w10, uxtb
        ldr     x12, [sp, #56]
        mov     w9, #0xfffffffb
        csel    w0, w8, w9, eq
        ldr     x11, [x11]
        cmp     x11, x12
        b.ne    L15c4
        mov     sp, x29
        ldp     x20, x19, [sp, #16]
        ldp     x29, x30, [sp], #32
        ret
L15c4:
        bl      L0830

// mlkem1024_keypair_derand (0x98 bytes)
L15c8:
        str     x30, [sp, #-48]!
        stp     x22, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x22, x2
        mov     x19, x1
        mov     x21, x0
        bl      L0a54
        mov     w20, w0
        cbz     w0, L1620
        mov     x0, x21
        mov     w1, wzr
        mov     w2, #0x620
        bl      L0840
        mov     x0, x19
        mov     w1, wzr
        mov     w2, #0xc60
        bl      L0840
        mov     w0, w20
        ldp     x20, x19, [sp, #32]
        ldp     x22, x21, [sp, #16]
        ldr     x30, [sp], #48
        ret
L1620:
        add     x0, x19, #0x600
        mov     x1, x21
        mov     w2, #0x620
        bl      L0810
        add     x0, x19, #0xc20
        mov     x1, x21
        mov     w2, #0x620
        bl      L53c4
        ldp     q1, q0, [x22, #32]
        str     q1, [x19, #3136]
        str     q0, [x19, #3152]
        mov     w0, w20
        ldp     x20, x19, [sp, #32]
        ldp     x22, x21, [sp, #16]
        ldr     x30, [sp], #48
        ret

// mlkem1024_keypair (0xf4 bytes)
L1660:
        stp     x29, x30, [sp, #-48]!
        str     x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0x50
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd0000168  // adrp x8, 0x2f000
        mov     x19, x1
        mov     x21, x0
        mov     x0, sp
        mov     w1, #0x40
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #72]
        bl      L0820
        cbz     w0, L16a8
        mov     w20, #0xfffffffd
        b       L1710
L16a8:
        mov     x2, sp
        mov     x0, x21
        mov     x1, x19
        bl      L0a54
        mov     w20, w0
        cbz     w0, L16e4
        mov     x0, x21
        mov     w1, wzr
        mov     w2, #0x620
        bl      L0840
        mov     x0, x19
        mov     w1, wzr
        mov     w2, #0xc60
        bl      L0840
        b       L1710
L16e4:
        add     x0, x19, #0x600
        mov     x1, x21
        mov     w2, #0x620
        bl      L0810
        add     x0, x19, #0xc20
        mov     x1, x21
        mov     w2, #0x620
        bl      L53c4
        ldp     q0, q1, [sp, #32]
        str     q0, [x19, #3136]
        str     q1, [x19, #3152]
L1710:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        .inst   0xd0000168  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #72]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L1750
        mov     w0, w20
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldr     x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L1750:
        bl      L0830

// mlkem1024_enc_derand (0x1e4 bytes)
L1754:
        stp     x29, x30, [sp, #-96]!
        str     x28, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0xe20
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd0000168  // adrp x8, 0x2f000
        mov     x19, x1
        mov     x21, x0
        add     x0, sp, #0x600
        mov     x1, x2
        mov     x22, x3
        ldr     x8, [x8, #4088]
        mov     x20, x2
        ldr     x8, [x8]
        str     x8, [sp, #3608]
        bl      L1cbc
        add     x0, sp, #0x600
        bl      L1fe8
        mov     x0, sp
        add     x1, sp, #0x600
        mov     x23, sp
        bl      L1c7c
        movi    v0.2d, #0x0
        mov     x8, xzr
        movi    v1.2d, #0x0
        movi    v2.2d, #0x0
        movi    v3.2d, #0x0
L17d0:
        add     x9, x20, x8
        add     x10, x23, x8
        add     x8, x8, #0x20
        cmp     x8, #0x600
        ldp     q4, q5, [x9]
        ldp     q6, q7, [x10]
        eor     v4.16b, v6.16b, v4.16b
        orr     v2.16b, v4.16b, v2.16b
        eor     v5.16b, v7.16b, v5.16b
        orr     v3.16b, v5.16b, v3.16b
        eor     v0.16b, v4.16b, v0.16b
        eor     v1.16b, v5.16b, v1.16b
        b.ne    L17d0
        orr     v2.16b, v3.16b, v2.16b
        mov     w23, wzr
        ext     v3.16b, v2.16b, v2.16b, #8
        mov     x0, sp
        eor     v0.16b, v1.16b, v0.16b
        mov     w1, wzr
        mov     w2, #0x600
        mov     x24, sp
        orr     v1.8b, v2.8b, v3.8b
        ext     v2.16b, v0.16b, v0.16b, #8
        fmov    x8, d1
        orr     x8, x8, x8, lsr #32
        lsr     x9, x8, #16
        eor     v0.8b, v0.8b, v2.8b
        orr     w8, w8, w9
        fmov    x9, d0
        orr     w8, w8, w8, lsr #8
        eor     x9, x9, x9, lsr #32
        sub     w8, w23, w8, uxtb
        eor     x9, x9, x9, lsr #16
        lsr     x10, x9, #8
        eor     w25, w9, w10
        eor     w8, w25, w8, lsr #16
        and     w26, w8, #0xff
        bl      L0840
        add     x0, sp, #0x600
        mov     w1, wzr
        mov     w2, #0x800
        add     x23, sp, #0x600
        bl      L0840
        cmp     w26, w25, uxtb
        b.ne    L18d4
        ldp     q0, q1, [x22]
        add     x0, x23, #0x20
        mov     x1, x20
        mov     w2, #0x620
        str     q0, [sp, #1536]
        str     q1, [sp, #1552]
        bl      L53c4
        mov     x0, sp
        add     x1, sp, #0x600
        mov     w2, #0x40
        bl      L5468
        add     x3, x24, #0x20
        add     x1, sp, #0x600
        mov     x0, x21
        mov     x2, x20
        bl      L0cec
        cbnz    w0, L18d8
        ldp     q0, q1, [sp]
        stp     q0, q1, [x19]
        b       L18d8
L18d4:
        mov     w0, #0xfffffffc
L18d8:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        str     q0, [sp, #1584]
        add     x8, sp, #0x600
        str     q0, [sp, #1568]
        str     q0, [sp, #1552]
        str     q0, [sp, #1536]
        .inst   0xd0000168  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #3608]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L1934
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldr     x28, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L1934:
        bl      L0830

// mlkem1024_enc (0x9c bytes)
L1938:
        stp     x29, x30, [sp, #-48]!
        str     x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0x30
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd0000168  // adrp x8, 0x2f000
        mov     x20, x1
        mov     x21, x0
        mov     x0, sp
        mov     w1, #0x20
        mov     x19, x2
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #40]
        bl      L0820
        cbz     w0, L1984
        mov     w0, #0xfffffffd
        b       L1998
L1984:
        mov     x3, sp
        mov     x0, x21
        mov     x1, x20
        mov     x2, x19
        bl      L1754
L1998:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        .inst   0xd0000168  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #40]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L19d0
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldr     x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L19d0:
        bl      L0830

// mlkem1024_dec (0x228 bytes)
L19d4:
        stp     x29, x30, [sp, #-64]!
        stp     x28, x23, [sp, #16]
        stp     x22, x21, [sp, #32]
        stp     x20, x19, [sp, #48]
        mov     x29, sp
        sub     x9, sp, #0x6e0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd0000168  // adrp x8, 0x2f000
        mov     x19, x0
        mov     x0, x2
        mov     x21, x2
        mov     x20, x1
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #1752]
        bl      L14e8
        mov     w22, w0
        cbnz    w0, L1b84
        add     x0, sp, #0x680
        mov     x1, x20
        mov     x2, x21
        bl      L1164
        mov     w22, w0
        cbnz    w0, L1b84
        ldr     q0, [x21, #3104]
        add     x0, sp, #0x640
        ldr     q1, [x21, #3120]
        add     x1, sp, #0x680
        mov     w2, #0x40
        add     x22, x21, #0x600
        str     q0, [sp, #1696]
        add     x23, sp, #0x640
        str     q1, [sp, #1712]
        bl      L5468
        add     x3, x23, #0x20
        mov     x0, sp
        add     x1, sp, #0x680
        mov     x2, x22
        mov     x23, sp
        bl      L0cec
        mov     w22, w0
        cbnz    w0, L1b84
        movi    v0.2d, #0x0
        mov     x8, xzr
        movi    v1.2d, #0x0
        movi    v2.2d, #0x0
        movi    v3.2d, #0x0
L1a90:
        add     x9, x20, x8
        add     x10, x23, x8
        add     x8, x8, #0x20
        cmp     x8, #0x620
        ldp     q4, q5, [x9]
        ldp     q6, q7, [x10]
        eor     v4.16b, v6.16b, v4.16b
        orr     v2.16b, v4.16b, v2.16b
        eor     v5.16b, v7.16b, v5.16b
        orr     v3.16b, v5.16b, v3.16b
        eor     v0.16b, v4.16b, v0.16b
        eor     v1.16b, v5.16b, v1.16b
        b.ne    L1a90
        orr     v2.16b, v3.16b, v2.16b
        mov     w22, wzr
        ext     v3.16b, v2.16b, v2.16b, #8
        mov     x8, sp
        eor     v0.16b, v1.16b, v0.16b
        add     x0, x8, #0x20
        ext     v1.16b, v0.16b, v0.16b, #8
        mov     x1, x20
        mov     w2, #0x620
        orr     v2.8b, v2.8b, v3.8b
        fmov    x9, d2
        eor     v0.8b, v0.8b, v1.8b
        fmov    x11, d0
        orr     x9, x9, x9, lsr #32
        lsr     x10, x9, #16
        orr     w9, w9, w10
        eor     x10, x11, x11, lsr #32
        orr     w9, w9, w9, lsr #8
        eor     x10, x10, x10, lsr #16
        sub     w9, w22, w9, uxtb
        lsr     x11, x10, #8
        eor     w10, w10, w11
        eor     w9, w10, w9, lsr #16
        ldr     q0, [x21, #3136]
        ldr     q1, [x21, #3152]
        eor     w21, w9, w10
        stp     q0, q1, [sp]
        bl      L0810
        mov     x2, sp
        mov     x0, x19
        mov     w1, #0x20
        mov     w3, #0x640
        bl      L52f0
        mov     x8, xzr
        sub     w9, w22, w21, uxtb
        add     x10, sp, #0x640
L1b54:
        ldrb    w11, [x19, x8]
        mov     w12, w9
        ldrb    w13, [x10, x8]
        lsr     w12, w12, #16
        and     w11, w11, w12
        bic     w13, w13, w12
        orr     w11, w11, w13
        strb    w11, [x19, x8]
        add     x8, x8, #0x1
        cmp     x8, #0x20
        b.ne    L1b54
        mov     w22, wzr
L1b84:
        mov     x0, sp
        mov     w1, wzr
        mov     w2, #0x640
        mov     x19, sp
        bl      L0840
        movi    v0.2d, #0x0
        add     x8, sp, #0x640
        str     q0, [sp, #1648]
        str     q0, [sp, #1632]
        str     q0, [sp, #1616]
        str     q0, [sp, #1600]
        str     q0, [sp, #1712]
        add     x8, sp, #0x680
        str     q0, [sp, #1696]
        str     q0, [sp, #1680]
        str     q0, [sp, #1664]
        .inst   0xd0000168  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #1752]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L1bf8
        mov     w0, w22
        mov     sp, x29
        ldp     x20, x19, [sp, #48]
        ldp     x22, x21, [sp, #32]
        ldp     x28, x23, [sp, #16]
        ldp     x29, x30, [sp], #64
        ret
L1bf8:
        bl      L0830

// mlkem1024_polyvec_compress_du (0x40 bytes)
L1bfc:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L345c
        add     x0, x20, #0x160
        add     x1, x19, #0x200
        bl      L345c
        add     x0, x20, #0x2c0
        add     x1, x19, #0x400
        bl      L345c
        add     x0, x20, #0x420
        add     x1, x19, #0x600
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L345c

// mlkem1024_polyvec_decompress_du (0x40 bytes)
L1c3c:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L3f74
        add     x0, x20, #0x200
        add     x1, x19, #0x160
        bl      L3f74
        add     x0, x20, #0x400
        add     x1, x19, #0x2c0
        bl      L3f74
        add     x0, x20, #0x600
        add     x1, x19, #0x420
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L3f74

// mlkem1024_polyvec_tobytes (0x40 bytes)
L1c7c:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L4080
        add     x0, x20, #0x180
        add     x1, x19, #0x200
        bl      L4080
        add     x0, x20, #0x300
        add     x1, x19, #0x400
        bl      L4080
        add     x0, x20, #0x480
        add     x1, x19, #0x600
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L4080

// mlkem1024_polyvec_frombytes (0x40 bytes)
L1cbc:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L42d0
        add     x0, x20, #0x200
        add     x1, x19, #0x180
        bl      L42d0
        add     x0, x20, #0x400
        add     x1, x19, #0x300
        bl      L42d0
        add     x0, x20, #0x600
        add     x1, x19, #0x480
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L42d0

// mlkem1024_polyvec_ntt (0x28 bytes)
L1cfc:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L8c28
        add     x0, x19, #0x200
        bl      L8c28
        add     x0, x19, #0x400
        bl      L8c28
        add     x0, x19, #0x600
        ldp     x30, x19, [sp], #16
        b       L8c28

// mlkem1024_polyvec_invntt_tomont (0x28 bytes)
L1d24:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      La46c
        add     x0, x19, #0x200
        bl      La46c
        add     x0, x19, #0x400
        bl      La46c
        add     x0, x19, #0x600
        ldp     x30, x19, [sp], #16
        b       La46c

// mlkem1024_polyvec_basemul_acc_montgomery_cached (0x25c bytes)
L1d4c:
        add     x8, x3, #0x400
        add     x10, x0, #0x200
        cmp     x8, x0
        add     x9, x2, #0x800
        ccmp    x10, x3, #0x0, hi
        add     x11, x1, #0x800
        cset    w8, hi
        cmp     x9, x0
        ccmp    x10, x2, #0x0, hi
        cset    w9, hi
        cmp     x10, x1
        ccmp    x11, x0, #0x0, hi
        b.hi    L1ec4
        tbnz    w8, #0, L1ec4
        cbnz    w9, L1ec4
        mov     w9, #0xf3010000
        mov     x8, xzr
        mvni    v1.4s, #0xd, lsl #8
        dup     v0.4s, w9
L1d98:
        add     x10, x1, x8
        add     x9, x2, x8
        add     x11, x10, #0x200
        ldr     q20, [x3]
        ldr     q23, [x3, #256]
        ld2     {v6.8h-v7.8h}, [x10]
        ld2     {v16.8h-v17.8h}, [x9]
        ld2     {v18.8h-v19.8h}, [x11]
        add     x11, x9, #0x200
        smull   v3.4s, v16.4h, v6.4h
        smull2  v2.4s, v16.8h, v6.8h
        ld2     {v21.8h-v22.8h}, [x11]
        smull   v5.4s, v17.4h, v6.4h
        add     x11, x10, #0x400
        smull2  v4.4s, v17.8h, v6.8h
        add     x10, x10, #0x600
        smlal   v3.4s, v20.4h, v7.4h
        smlal2  v2.4s, v20.8h, v7.8h
        ld2     {v24.8h-v25.8h}, [x11]
        smlal   v5.4s, v16.4h, v7.4h
        add     x11, x9, #0x400
        smlal2  v4.4s, v16.8h, v7.8h
        add     x9, x9, #0x600
        smlal   v3.4s, v23.4h, v19.4h
        smlal2  v2.4s, v23.8h, v19.8h
        ld2     {v6.8h-v7.8h}, [x11]
        smlal   v5.4s, v21.4h, v19.4h
        smlal2  v4.4s, v21.8h, v19.8h
        smlal   v3.4s, v21.4h, v18.4h
        ldr     q16, [x3, #512]
        smlal2  v2.4s, v21.8h, v18.8h
        ld2     {v26.8h-v27.8h}, [x10]
        smlal   v5.4s, v22.4h, v18.4h
        smlal   v3.4s, v16.4h, v25.4h
        smlal2  v4.4s, v22.8h, v18.8h
        smlal2  v2.4s, v16.8h, v25.8h
        ldr     q16, [x3, #768]
        smlal   v5.4s, v6.4h, v25.4h
        ld2     {v17.8h-v18.8h}, [x9]
        smlal   v3.4s, v6.4h, v24.4h
        add     x9, x0, x8
        smlal2  v4.4s, v6.8h, v25.8h
        add     x8, x8, #0x20
        smlal2  v2.4s, v6.8h, v24.8h
        add     x3, x3, #0x10
        smlal   v5.4s, v7.4h, v24.4h
        cmp     x8, #0x200
        smlal   v3.4s, v16.4h, v27.4h
        smlal2  v4.4s, v7.8h, v24.8h
        smlal2  v2.4s, v16.8h, v27.8h
        smlal   v5.4s, v17.4h, v27.4h
        smlal   v3.4s, v17.4h, v26.4h
        smlal2  v4.4s, v17.8h, v27.8h
        smlal2  v2.4s, v17.8h, v26.8h
        smlal   v5.4s, v18.4h, v26.4h
        mul     v6.4s, v3.4s, v0.4s
        smlal2  v4.4s, v18.8h, v26.8h
        mul     v7.4s, v2.4s, v0.4s
        mul     v16.4s, v5.4s, v0.4s
        sshr    v6.4s, v6.4s, #16
        mul     v17.4s, v4.4s, v0.4s
        mul     v6.4s, v6.4s, v1.4s
        sshr    v7.4s, v7.4s, #16
        sshr    v16.4s, v16.4s, #16
        mul     v7.4s, v7.4s, v1.4s
        addhn   v18.4h, v6.4s, v3.4s
        mul     v3.4s, v16.4s, v1.4s
        sshr    v6.4s, v17.4s, #16
        addhn2  v18.8h, v7.4s, v2.4s
        mul     v2.4s, v6.4s, v1.4s
        addhn   v19.4h, v3.4s, v5.4s
        addhn2  v19.8h, v2.4s, v4.4s
        st2     {v18.8h-v19.8h}, [x9]
        b.ne    L1d98
        b       L1fa4
L1ec4:
        mov     x8, xzr
        mov     w9, #0xf3010000
        mov     w10, #0xfffff2ff
L1ed0:
        add     x11, x1, x8
        add     x13, x2, x8
        ldrsh   w12, [x3]
        ldrsh   w4, [x3, #256]
        ldrsh   w14, [x11, #2]
        ldrsh   w16, [x13]
        ldrsh   w15, [x11]
        ldrsh   w17, [x13, #2]
        mul     w12, w12, w14
        ldrsh   w18, [x11, #514]
        mul     w14, w16, w14
        ldrsh   w6, [x13, #512]
        madd    w12, w16, w15, w12
        ldrsh   w5, [x11, #512]
        madd    w14, w17, w15, w14
        ldrsh   w16, [x13, #514]
        madd    w12, w4, w18, w12
        ldrsh   w15, [x11, #1026]
        madd    w14, w6, w18, w14
        ldrsh   w17, [x3, #512]
        madd    w12, w6, w5, w12
        ldrsh   w4, [x13, #1024]
        madd    w14, w16, w5, w14
        ldrsh   w18, [x11, #1024]
        ldrsh   w16, [x13, #1026]
        madd    w12, w17, w15, w12
        madd    w14, w4, w15, w14
        ldrsh   w17, [x11, #1538]
        ldrsh   w15, [x3, #768]
        madd    w12, w4, w18, w12
        ldrsh   w4, [x13, #1536]
        madd    w14, w16, w18, w14
        ldrsh   w11, [x11, #1536]
        add     x3, x3, #0x2
        ldrsh   w13, [x13, #1538]
        madd    w12, w15, w17, w12
        madd    w14, w4, w17, w14
        madd    w12, w4, w11, w12
        madd    w11, w13, w11, w14
        mul     w13, w12, w9
        mul     w14, w11, w9
        asr     w13, w13, #16
        asr     w14, w14, #16
        madd    w12, w13, w10, w12
        add     x13, x0, x8
        madd    w11, w14, w10, w11
        add     x8, x8, #0x4
        lsr     w12, w12, #16
        cmp     x8, #0x200
        lsr     w11, w11, #16
        strh    w12, [x13]
        strh    w11, [x13, #2]
        b.ne    L1ed0
L1fa4:
        ret

// mlkem1024_polyvec_mulcache_compute (0x40 bytes)
L1fa8:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L867c
        add     x0, x20, #0x100
        add     x1, x19, #0x200
        bl      L867c
        add     x0, x20, #0x200
        add     x1, x19, #0x400
        bl      L867c
        add     x0, x20, #0x300
        add     x1, x19, #0x600
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L867c

// mlkem1024_polyvec_reduce (0x28 bytes)
L1fe8:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L832c
        add     x0, x19, #0x200
        bl      L832c
        add     x0, x19, #0x400
        bl      L832c
        add     x0, x19, #0x600
        ldp     x30, x19, [sp], #16
        b       L832c

// mlkem1024_polyvec_add (0x40 bytes)
L2010:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L837c
        add     x0, x20, #0x200
        add     x1, x19, #0x200
        bl      L837c
        add     x0, x20, #0x400
        add     x1, x19, #0x400
        bl      L837c
        add     x0, x20, #0x600
        add     x1, x19, #0x600
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L837c

// mlkem1024_polyvec_tomont (0x28 bytes)
L2050:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L8298
        add     x0, x19, #0x200
        bl      L8298
        add     x0, x19, #0x400
        bl      L8298
        add     x0, x19, #0x600
        ldp     x30, x19, [sp], #16
        b       L8298

// mlkem1024_poly_getnoise_eta1_4x (0x18c bytes)
L2078:
        stp     x29, x30, [sp, #-80]!
        stp     x28, x25, [sp, #16]
        stp     x24, x23, [sp, #32]
        stp     x22, x21, [sp, #48]
        stp     x20, x19, [sp, #64]
        mov     x29, sp
        sub     x9, sp, #0x330
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb0000168  // adrp x8, 0x2f000
        ldrb    w10, [x29, #80]
        add     x11, sp, #0x20
        add     x12, sp, #0x120
        add     x9, x11, #0x80
        add     x24, x12, #0x80
        ldr     x8, [x8, #4088]
        add     x25, x12, #0x100
        add     x20, x12, #0x180
        mov     x19, x3
        mov     x21, x2
        mov     x22, x1
        ldr     x8, [x8]
        mov     x23, x0
        add     x0, sp, #0x120
        mov     x1, x24
        mov     x2, x25
        mov     x3, x20
        str     x8, [sp, #808]
        add     x8, x11, #0x40
        ldp     q0, q1, [x4]
        strb    w5, [sp, #64]
        add     x11, x11, #0xc0
        strb    w6, [sp, #128]
        add     x5, sp, #0x20
        strb    w7, [sp, #192]
        mov     w4, #0x80
        strb    w10, [sp, #256]
        mov     w10, #0x21
        mov     x6, x8
        mov     x7, x9
        stp     q0, q1, [sp, #32]
        stp     q0, q1, [sp, #96]
        stp     q0, q1, [sp, #160]
        stp     q0, q1, [sp, #224]
        stp     x11, x10, [sp]
        bl      L5770
        add     x1, sp, #0x120
        mov     x0, x23
        bl      Lcc10
        mov     x0, x22
        mov     x1, x24
        bl      Lcc10
        mov     x0, x21
        mov     x1, x25
        bl      Lcc10
        cbz     x19, L2160
        mov     x0, x19
        mov     x1, x20
        bl      Lcc10
L2160:
        movi    v0.2d, #0x0
        add     x8, sp, #0x120
        stp     q0, q0, [sp, #288]
        stp     q0, q0, [sp, #320]
        stp     q0, q0, [sp, #352]
        stp     q0, q0, [sp, #384]
        stp     q0, q0, [sp, #416]
        stp     q0, q0, [sp, #448]
        stp     q0, q0, [sp, #480]
        stp     q0, q0, [sp, #512]
        stp     q0, q0, [sp, #544]
        stp     q0, q0, [sp, #576]
        stp     q0, q0, [sp, #608]
        stp     q0, q0, [sp, #640]
        stp     q0, q0, [sp, #672]
        stp     q0, q0, [sp, #704]
        stp     q0, q0, [sp, #736]
        stp     q0, q0, [sp, #768]
        stp     q0, q0, [sp, #64]
        stp     q0, q0, [sp, #96]
        add     x8, sp, #0x20
        stp     q0, q0, [sp, #32]
        stp     q0, q0, [sp, #128]
        stp     q0, q0, [sp, #160]
        stp     q0, q0, [sp, #192]
        stp     q0, q0, [sp, #224]
        stp     q0, q0, [sp, #256]
        .inst   0xb0000168  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #808]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L2200
        mov     sp, x29
        ldp     x20, x19, [sp, #64]
        ldp     x22, x21, [sp, #48]
        ldp     x24, x23, [sp, #32]
        ldp     x28, x25, [sp, #16]
        ldp     x29, x30, [sp], #80
        ret
L2200:
        bl      L0830

// mlkem1024_poly_getnoise_eta2 (0xac bytes)
L2204:
        stp     x29, x30, [sp, #-48]!
        stp     x28, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0xd0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb0000168  // adrp x8, 0x2f000
        mov     x19, x0
        add     x0, sp, #0x40
        mov     w3, #0x21
        add     x20, sp, #0x40
        mov     x21, sp
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #200]
        ldp     q0, q1, [x1]
        strb    w2, [sp, #32]
        mov     x2, sp
        mov     w1, #0x80
        stp     q0, q1, [sp]
        bl      L52f0
        add     x1, sp, #0x40
        mov     x0, x19
        bl      Lcc10
        movi    v0.2d, #0x0
        .inst   0xb0000168  // adrp x8, 0x2f000
        stp     q0, q0, [sp, #64]
        stp     q0, q0, [sp, #96]
        stp     q0, q0, [sp, #128]
        stp     q0, q0, [sp, #160]
        strb    wzr, [sp, #32]
        stp     q0, q0, [sp]
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #200]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L22ac
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldp     x28, x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L22ac:
        bl      L0830

// mlkem_poly_compress_d4 (0xa64 bytes)
L22b0:
        sub     sp, sp, #0x130
        stp     d15, d14, [sp, #224]
        stp     d13, d12, [sp, #240]
        stp     d11, d10, [sp, #256]
        stp     d9, d8, [sp, #272]
        str     x29, [sp, #288]
        add     x8, x1, #0x200
        cmp     x8, x0
        b.ls    L237c
        add     x8, x0, #0x80
        cmp     x8, x1
        b.ls    L237c
        mov     w10, #0xafb0
        mov     x8, xzr
        movk    w10, #0x13, lsl #16
        add     x9, x1, #0x8
        dup     v0.4s, w10
L22f4:
        ldurh   w10, [x9, #-8]
        sub     x11, x9, #0x4
        sub     x12, x9, #0x2
        movi    v3.4s, #0x8, lsl #24
        fmov    s1, w10
        ldurh   w10, [x9, #-6]
        movi    v4.4s, #0x8, lsl #24
        ld1     {v1.h}[1], [x11]
        mov     x11, x9
        fmov    s2, w10
        add     x10, x9, #0x6
        ld1     {v1.h}[2], [x11], #2
        ld1     {v2.h}[1], [x12]
        ld1     {v2.h}[2], [x11]
        add     x11, x9, #0x4
        add     x9, x9, #0x10
        ld1     {v1.h}[3], [x11]
        ld1     {v2.h}[3], [x10]
        sxtl    v1.4s, v1.4h
        sxtl    v2.4s, v2.4h
        mla     v4.4s, v1.4s, v0.4s
        mla     v3.4s, v2.4s, v0.4s
        ushr    v2.4s, v4.4s, #28
        ushr    v1.4s, v3.4s, #24
        xtn     v2.4h, v2.4s
        xtn     v1.4h, v1.4s
        bic     v1.4h, #0xf
        orr     v1.8b, v1.8b, v2.8b
        xtn     v1.8b, v1.8h
        str     s1, [x0, x8]
        add     x8, x8, #0x4
        cmp     x8, #0x80
        b.ne    L22f4
        b       L2cf8
L237c:
        ldp     q13, q14, [x1, #32]
        mov     w8, #0xafb0
        .inst   0xb0000069  // adrp x9, 0xf000
        movk    w8, #0x13, lsl #16
        movi    v11.4s, #0x8, lsl #24
        movi    v27.4s, #0x8, lsl #24
        dup     v26.4s, w8
        .inst   0xb0000068  // adrp x8, 0xf000
        ldp     q18, q19, [x1]
        zip1    v1.4h, v13.4h, v14.4h
        movi    v15.4s, #0x8, lsl #24
        ext     v0.8b, v13.8b, v1.8b, #4
        ldp     q22, q23, [x1, #96]
        zip1    v2.4h, v18.4h, v19.4h
        mov     v2.s[1], v0.s[1]
        ldp     q24, q25, [x1, #224]
        zip1    v3.4h, v22.4h, v23.4h
        sxtl    v2.4s, v2.4h
        ext     v0.8b, v22.8b, v3.8b, #4
        ldp     q29, q30, [x1, #160]
        zip1    v5.4h, v24.4h, v25.4h
        mla     v11.4s, v2.4s, v26.4s
        movi    v2.4s, #0x8, lsl #24
        ext     v31.8b, v24.8b, v5.8b, #4
        ldp     q16, q17, [x1, #64]
        zip1    v4.4h, v29.4h, v30.4h
        ext     v7.8b, v29.8b, v4.8b, #4
        ldp     q20, q21, [x1, #192]
        zip1    v6.4h, v16.4h, v17.4h
        mov     v6.s[1], v0.s[1]
        ldp     q8, q9, [x1, #128]
        zip1    v10.4h, v20.4h, v21.4h
        sxtl    v6.4s, v6.4h
        mov     v10.s[1], v31.s[1]
        zip1    v28.4h, v8.4h, v9.4h
        movi    v31.4s, #0x8, lsl #24
        trn2    v12.4h, v8.4h, v9.4h
        mla     v2.4s, v6.4s, v26.4s
        sxtl    v10.4s, v10.4h
        mov     v28.s[1], v7.s[1]
        movi    v7.4s, #0x8, lsl #24
        mla     v31.4s, v10.4s, v26.4s
        ushr    v10.4s, v11.4s, #28
        sxtl    v28.4s, v28.4h
        ushr    v2.4s, v2.4s, #28
        mov     v12.s[1], v4.s[1]
        mla     v7.4s, v28.4s, v26.4s
        ushr    v31.4s, v31.4s, #28
        trn2    v4.4h, v18.4h, v19.4h
        trn2    v28.4h, v20.4h, v21.4h
        uzp1    v2.8h, v10.8h, v2.8h
        trn2    v6.4h, v16.4h, v17.4h
        ushr    v7.4s, v7.4s, #28
        zip2    v10.4h, v16.4h, v17.4h
        uzp1    v7.8h, v7.8h, v31.8h
        mov     v4.s[1], v1.s[1]
        mov     v28.s[1], v5.s[1]
        mov     v6.s[1], v3.s[1]
        uzp1    v0.16b, v2.16b, v7.16b
        movi    v7.4s, #0x8, lsl #24
        sxtl    v4.4s, v4.4h
        sxtl    v5.4s, v12.4h
        str     q0, [sp, #128]
        movi    v0.4s, #0x8, lsl #24
        mla     v7.4s, v4.4s, v26.4s
        sxtl    v2.4s, v28.4h
        mov     v3.16b, v29.16b
        mla     v0.4s, v5.4s, v26.4s
        mla     v27.4s, v2.4s, v26.4s
        str     q7, [sp, #80]
        mov     v2.16b, v24.16b
        mov     v5.16b, v22.16b
        sxtl    v1.4s, v6.4h
        mov     v3.h[3], v30.h[2]
        stp     q27, q0, [sp, #96]
        mov     v2.h[3], v25.h[2]
        zip2    v6.4h, v8.4h, v9.4h
        zip2    v7.4h, v20.4h, v21.4h
        zip2    v28.4h, v18.4h, v19.4h
        mov     v5.h[3], v23.h[2]
        mov     v4.16b, v13.16b
        mov     v4.h[3], v14.h[2]
        mov     v6.s[1], v3.s[1]
        mov     v7.s[1], v2.s[1]
        mov     v10.s[1], v5.s[1]
        mov     v28.s[1], v4.s[1]
        sxtl    v2.4s, v6.4h
        sxtl    v3.4s, v7.4h
        sxtl    v5.4s, v10.4h
        movi    v6.4s, #0x8, lsl #24
        movi    v7.4s, #0x8, lsl #24
        movi    v10.4s, #0x8, lsl #24
        movi    v11.4s, #0x8, lsl #24
        sxtl    v4.4s, v28.4h
        mla     v6.4s, v2.4s, v26.4s
        mla     v7.4s, v5.4s, v26.4s
        mla     v10.4s, v3.4s, v26.4s
        mla     v11.4s, v4.4s, v26.4s
        movi    v0.4s, #0x8, lsl #24
        ushr    v2.4s, v7.4s, #28
        ushr    v3.4s, v10.4s, #28
        ushr    v4.4s, v6.4s, #28
        ushr    v5.4s, v11.4s, #28
        uzp2    v6.4h, v8.4h, v9.4h
        uzp1    v3.8h, v4.8h, v3.8h
        zip2    v4.4h, v29.4h, v30.4h
        uzp1    v2.8h, v5.8h, v2.8h
        mla     v0.4s, v1.4s, v26.4s
        uzp2    v5.4h, v6.4h, v8.4h
        mov     v27.16b, v18.16b
        uzp2    v1.4h, v20.4h, v21.4h
        mov     v28.16b, v19.16b
        str     q0, [sp, #48]
        uzp2    v6.4h, v16.4h, v17.4h
        uzp1    v0.16b, v2.16b, v3.16b
        uzp2    v2.4h, v27.4h, v28.4h
        mov     v5.s[1], v4.s[1]
        zip2    v3.4h, v24.4h, v25.4h
        uzp2    v1.4h, v1.4h, v20.4h
        zip2    v4.4h, v13.4h, v14.4h
        str     q0, [sp, #64]
        uzp2    v2.4h, v2.4h, v27.4h
        movi    v0.4s, #0x8, lsl #24
        uzp2    v6.4h, v6.4h, v16.4h
        sxtl    v5.4s, v5.4h
        mov     v1.s[1], v3.s[1]
        mov     v2.s[1], v4.s[1]
        mla     v0.4s, v5.4s, v26.4s
        zip2    v3.4h, v22.4h, v23.4h
        movi    v12.4s, #0x8, lsl #24
        sxtl    v1.4s, v1.4h
        str     q0, [sp, #32]
        ldr     q0, [x8, #352]
        sxtl    v2.4s, v2.4h
        .inst   0xb0000068  // adrp x8, 0xf000
        mov     v6.s[1], v3.s[1]
        tbl     v3.16b, {v29.16b-v30.16b}, v0.16b
        str     q0, [sp, #208]
        zip2    v4.8h, v8.8h, v9.8h
        tbl     v7.16b, {v24.16b-v25.16b}, v0.16b
        zip2    v10.8h, v20.8h, v21.8h
        mla     v12.4s, v1.4s, v26.4s
        mla     v15.4s, v2.4s, v26.4s
        tbl     v1.16b, {v13.16b-v14.16b}, v0.16b
        zip2    v2.8h, v27.8h, v28.8h
        mov     v4.s[1], v3.s[1]
        mov     v10.s[1], v7.s[1]
        tbl     v3.16b, {v22.16b-v23.16b}, v0.16b
        ldr     q0, [x8, #368]
        zip2    v7.8h, v16.8h, v17.8h
        .inst   0xb0000068  // adrp x8, 0xf000
        mov     v2.s[1], v1.s[1]
        movi    v11.4s, #0x8, lsl #24
        str     q0, [sp, #144]
        sxtl    v1.4s, v4.4h
        mov     v7.s[1], v3.s[1]
        movi    v3.4s, #0x8, lsl #24
        sxtl    v2.4s, v2.4h
        mla     v11.4s, v1.4s, v26.4s
        movi    v1.4s, #0x8, lsl #24
        mla     v3.4s, v2.4s, v26.4s
        movi    v2.4s, #0x8, lsl #24
        sxtl    v4.4s, v10.4h
        sxtl    v7.4s, v7.4h
        mla     v1.4s, v4.4s, v26.4s
        movi    v31.4s, #0x8, lsl #24
        mla     v2.4s, v7.4s, v26.4s
        sxtl    v6.4s, v6.4h
        ushr    v1.4s, v1.4s, #28
        mla     v31.4s, v6.4s, v26.4s
        ushr    v6.4s, v11.4s, #28
        ushr    v2.4s, v2.4s, #28
        ushr    v3.4s, v3.4s, #28
        uzp1    v1.8h, v6.8h, v1.8h
        uzp1    v3.8h, v3.8h, v2.8h
        zip2    v7.8h, v29.8h, v30.8h
        tbl     v10.16b, {v8.16b-v9.16b}, v0.16b
        mov     v18.16b, v16.16b
        mov     v19.16b, v17.16b
        zip2    v11.8h, v24.8h, v25.8h
        tbl     v16.16b, {v20.16b-v21.16b}, v0.16b
        tbl     v17.16b, {v27.16b-v28.16b}, v0.16b
        mov     v6.16b, v0.16b
        uzp1    v0.16b, v3.16b, v1.16b
        zip2    v2.8h, v13.8h, v14.8h
        mov     v10.s[1], v7.s[1]
        mov     v16.s[1], v11.s[1]
        str     q0, [sp, #16]
        ldr     q0, [x8, #384]
        mov     v11.16b, v19.16b
        .inst   0xb0000068  // adrp x8, 0xf000
        tbl     v6.16b, {v18.16b-v19.16b}, v6.16b
        ldr     q19, [x9, #400]
        mov     v17.s[1], v2.s[1]
        .inst   0xb0000069  // adrp x9, 0xf000
        sxtl    v5.4s, v10.4h
        str     q0, [sp, #192]
        mov     v10.16b, v18.16b
        str     q19, [sp, #160]
        movi    v18.4s, #0x8, lsl #24
        tbl     v7.16b, {v29.16b-v30.16b}, v0.16b
        tbl     v2.16b, {v8.16b-v9.16b}, v19.16b
        zip2    v4.8h, v22.8h, v23.8h
        tbl     v3.16b, {v24.16b-v25.16b}, v0.16b
        tbl     v1.16b, {v20.16b-v21.16b}, v19.16b
        mla     v18.4s, v5.4s, v26.4s
        mov     v2.s[1], v7.s[1]
        tbl     v5.16b, {v22.16b-v23.16b}, v0.16b
        tbl     v7.16b, {v10.16b-v11.16b}, v19.16b
        mov     v6.s[1], v4.s[1]
        mov     v1.s[1], v3.s[1]
        tbl     v3.16b, {v13.16b-v14.16b}, v0.16b
        ldr     q0, [x8, #416]
        tbl     v4.16b, {v27.16b-v28.16b}, v19.16b
        mov     v7.s[1], v5.s[1]
        movi    v19.4s, #0x8, lsl #24
        str     q0, [sp, #176]
        sxtl    v2.4s, v2.4h
        mov     v4.s[1], v3.s[1]
        movi    v3.4s, #0x8, lsl #24
        sxtl    v5.4s, v7.4h
        mla     v19.4s, v2.4s, v26.4s
        movi    v2.4s, #0x8, lsl #24
        mla     v3.4s, v5.4s, v26.4s
        movi    v5.4s, #0x8, lsl #24
        sxtl    v1.4s, v1.4h
        sxtl    v4.4s, v4.4h
        mla     v2.4s, v1.4s, v26.4s
        movi    v1.4s, #0x8, lsl #24
        mla     v5.4s, v4.4s, v26.4s
        sxtl    v7.4s, v16.4h
        ushr    v3.4s, v3.4s, #28
        mla     v1.4s, v7.4s, v26.4s
        ldr     q7, [x9, #432]
        ushr    v2.4s, v2.4s, #28
        ushr    v4.4s, v19.4s, #28
        ushr    v16.4s, v5.4s, #28
        movi    v19.4s, #0x8, lsl #24
        ushr    v18.4s, v18.4s, #24
        uzp1    v2.8h, v4.8h, v2.8h
        uzp1    v3.8h, v16.8h, v3.8h
        tbl     v4.16b, {v29.16b-v30.16b}, v0.16b
        tbl     v16.16b, {v8.16b-v9.16b}, v7.16b
        movi    v29.4s, #0x8, lsl #24
        sxtl    v17.4s, v17.4h
        sxtl    v6.4s, v6.4h
        mla     v19.4s, v17.4s, v26.4s
        mla     v29.4s, v6.4s, v26.4s
        mov     v16.s[1], v4.s[1]
        tbl     v4.16b, {v20.16b-v21.16b}, v7.16b
        tbl     v6.16b, {v13.16b-v14.16b}, v0.16b
        tbl     v17.16b, {v27.16b-v28.16b}, v7.16b
        tbl     v20.16b, {v22.16b-v23.16b}, v0.16b
        tbl     v21.16b, {v10.16b-v11.16b}, v7.16b
        uzp1    v2.16b, v3.16b, v2.16b
        tbl     v3.16b, {v24.16b-v25.16b}, v0.16b
        ldr     q0, [sp, #96]
        mov     v17.s[1], v6.s[1]
        mov     v21.s[1], v20.s[1]
        ushr    v20.4s, v0.4s, #24
        ldr     q0, [sp, #112]
        mov     v4.s[1], v3.s[1]
        ushr    v24.4s, v31.4s, #24
        sxtl    v6.4s, v17.4h
        sxtl    v17.4s, v21.4h
        ushr    v21.4s, v0.4s, #24
        ldp     q5, q0, [sp, #32]
        movi    v3.4s, #0x8, lsl #24
        ushr    v25.4s, v15.4s, #24
        sxtl    v16.4s, v16.4h
        sxtl    v4.4s, v4.4h
        uzp1    v20.8h, v21.8h, v20.8h
        mla     v3.4s, v16.4s, v26.4s
        ushr    v22.4s, v0.4s, #24
        ldr     q0, [sp, #80]
        movi    v16.4s, #0x8, lsl #24
        ushr    v1.4s, v1.4s, #24
        ushr    v19.4s, v19.4s, #24
        ushr    v23.4s, v0.4s, #24
        ushr    v3.4s, v3.4s, #24
        movi    v0.16b, #0xf0
        uzp1    v21.8h, v23.8h, v22.8h
        mla     v16.4s, v4.4s, v26.4s
        movi    v4.4s, #0x8, lsl #24
        movi    v22.4s, #0x8, lsl #24
        uzp1    v20.16b, v21.16b, v20.16b
        ushr    v21.4s, v12.4s, #24
        mla     v4.4s, v6.4s, v26.4s
        ushr    v23.4s, v5.4s, #24
        mla     v22.4s, v17.4s, v26.4s
        ldr     q5, [sp, #128]
        and     v6.16b, v20.16b, v0.16b
        ushr    v20.4s, v29.4s, #24
        uzp1    v21.8h, v23.8h, v21.8h
        ushr    v16.4s, v16.4s, #24
        uzp1    v23.8h, v25.8h, v24.8h
        uzp1    v1.8h, v18.8h, v1.8h
        uzp1    v18.8h, v19.8h, v20.8h
        ushr    v19.4s, v22.4s, #24
        ushr    v4.4s, v4.4s, #24
        uzp1    v3.8h, v3.8h, v16.8h
        uzp1    v4.8h, v4.8h, v19.8h
        uzp1    v17.16b, v23.16b, v21.16b
        uzp1    v1.16b, v18.16b, v1.16b
        orr     v19.16b, v6.16b, v5.16b
        uzp1    v3.16b, v4.16b, v3.16b
        ldr     q4, [sp, #64]
        and     v6.16b, v17.16b, v0.16b
        and     v1.16b, v1.16b, v0.16b
        orr     v20.16b, v6.16b, v4.16b
        ldr     q4, [sp, #16]
        movi    v5.4s, #0x8, lsl #24
        orr     v21.16b, v1.16b, v4.16b
        and     v1.16b, v3.16b, v0.16b
        orr     v22.16b, v1.16b, v2.16b
        st4     {v19.16b-v22.16b}, [x0], #64
        ldp     q20, q21, [x1, #416]
        ldp     q22, q23, [x1, #480]
        zip1    v1.4h, v20.4h, v21.4h
        ext     v6.8b, v20.8b, v1.8b, #4
        ldp     q16, q17, [x1, #288]
        zip1    v2.4h, v22.4h, v23.4h
        ext     v9.8b, v22.8b, v2.8b, #4
        ldp     q18, q19, [x1, #352]
        zip1    v3.4h, v16.4h, v17.4h
        ext     v13.8b, v16.8b, v3.8b, #4
        ldp     q10, q11, [x1, #448]
        zip1    v4.4h, v18.4h, v19.4h
        ext     v15.8b, v18.8b, v4.8b, #4
        ldp     q30, q31, [x1, #384]
        zip1    v12.4h, v10.4h, v11.4h
        mov     v12.s[1], v9.s[1]
        ldp     q24, q25, [x1, #320]
        zip1    v8.4h, v30.4h, v31.4h
        movi    v9.4s, #0x8, lsl #24
        sxtl    v12.4s, v12.4h
        mov     v8.s[1], v6.s[1]
        ldp     q28, q29, [x1, #256]
        zip1    v0.4h, v24.4h, v25.4h
        movi    v6.4s, #0x8, lsl #24
        sxtl    v8.4s, v8.4h
        mla     v9.4s, v12.4s, v26.4s
        mov     v0.s[1], v15.s[1]
        zip1    v14.4h, v28.4h, v29.4h
        mla     v6.4s, v8.4s, v26.4s
        movi    v8.4s, #0x8, lsl #24
        movi    v12.4s, #0x8, lsl #24
        mov     v14.s[1], v13.s[1]
        sxtl    v0.4s, v0.4h
        ushr    v6.4s, v6.4s, #28
        mla     v12.4s, v0.4s, v26.4s
        ushr    v0.4s, v9.4s, #28
        sxtl    v13.4s, v14.4h
        trn2    v9.4h, v30.4h, v31.4h
        mla     v8.4s, v13.4s, v26.4s
        zip2    v13.4h, v24.4h, v25.4h
        ushr    v12.4s, v12.4s, #28
        uzp1    v0.8h, v6.8h, v0.8h
        mov     v9.s[1], v1.s[1]
        ushr    v8.4s, v8.4s, #28
        trn2    v1.4h, v28.4h, v29.4h
        uzp1    v6.8h, v8.8h, v12.8h
        trn2    v8.4h, v10.4h, v11.4h
        mov     v14.16b, v18.16b
        zip2    v12.4h, v28.4h, v29.4h
        mov     v1.s[1], v3.s[1]
        uzp1    v0.16b, v6.16b, v0.16b
        mov     v8.s[1], v2.s[1]
        trn2    v2.4h, v24.4h, v25.4h
        movi    v6.4s, #0x8, lsl #24
        str     q0, [sp, #128]
        sxtl    v0.4s, v9.4h
        zip2    v9.4h, v10.4h, v11.4h
        sxtl    v3.4s, v8.4h
        mov     v2.s[1], v4.s[1]
        mov     v4.16b, v20.16b
        mla     v5.4s, v0.4s, v26.4s
        mov     v0.16b, v22.16b
        mla     v6.4s, v3.4s, v26.4s
        mov     v4.h[3], v21.h[2]
        mov     v0.h[3], v23.h[2]
        zip2    v8.4h, v30.4h, v31.4h
        mov     v3.16b, v16.16b
        stp     q6, q5, [sp, #96]
        mov     v3.h[3], v17.h[2]
        mov     v15.16b, v19.16b
        mov     v6.16b, v14.16b
        mov     v6.h[3], v15.h[2]
        mov     v8.s[1], v4.s[1]
        mov     v9.s[1], v0.s[1]
        mov     v12.s[1], v3.s[1]
        movi    v0.4s, #0x8, lsl #24
        movi    v3.4s, #0x8, lsl #24
        mov     v13.s[1], v6.s[1]
        sxtl    v4.4s, v8.4h
        sxtl    v6.4s, v9.4h
        mla     v0.4s, v4.4s, v26.4s
        mla     v3.4s, v6.4s, v26.4s
        movi    v4.4s, #0x8, lsl #24
        movi    v6.4s, #0x8, lsl #24
        sxtl    v8.4s, v12.4h
        sxtl    v9.4s, v13.4h
        mla     v4.4s, v8.4s, v26.4s
        mla     v6.4s, v9.4s, v26.4s
        movi    v5.4s, #0x8, lsl #24
        sxtl    v1.4s, v1.4h
        ushr    v3.4s, v3.4s, #28
        ushr    v0.4s, v0.4s, #28
        zip2    v12.4h, v16.4h, v17.4h
        mla     v5.4s, v1.4s, v26.4s
        ushr    v1.4s, v6.4s, #28
        uzp1    v0.8h, v0.8h, v3.8h
        ushr    v3.4s, v4.4s, #28
        movi    v4.4s, #0x8, lsl #24
        zip2    v13.4h, v14.4h, v15.4h
        uzp1    v1.8h, v3.8h, v1.8h
        sxtl    v2.4s, v2.4h
        uzp2    v3.4h, v10.4h, v11.4h
        mla     v4.4s, v2.4s, v26.4s
        uzp2    v2.4h, v30.4h, v31.4h
        uzp1    v0.16b, v1.16b, v0.16b
        uzp2    v1.4h, v24.4h, v25.4h
        uzp2    v3.4h, v3.4h, v10.4h
        zip2    v8.4h, v22.4h, v23.4h
        str     q4, [sp, #48]
        uzp2    v2.4h, v2.4h, v30.4h
        stp     q0, q5, [sp, #64]
        uzp2    v0.4h, v28.4h, v29.4h
        zip2    v4.4h, v20.4h, v21.4h
        uzp2    v1.4h, v1.4h, v24.4h
        mov     v3.s[1], v8.s[1]
        movi    v9.4s, #0x8, lsl #24
        uzp2    v0.4h, v0.4h, v28.4h
        mov     v2.s[1], v4.s[1]
        movi    v4.4s, #0x8, lsl #24
        mov     v1.s[1], v13.s[1]
        mov     v0.s[1], v12.s[1]
        sxtl    v2.4s, v2.4h
        movi    v5.4s, #0x8, lsl #24
        mla     v4.4s, v2.4s, v26.4s
        movi    v2.4s, #0x8, lsl #24
        sxtl    v0.4s, v0.4h
        sxtl    v1.4s, v1.4h
        sxtl    v3.4s, v3.4h
        mla     v2.4s, v0.4s, v26.4s
        mla     v9.4s, v1.4s, v26.4s
        ldp     q0, q1, [sp, #144]
        mla     v5.4s, v3.4s, v26.4s
        str     q2, [sp]
        zip2    v8.8h, v30.8h, v31.8h
        tbl     v27.16b, {v30.16b-v31.16b}, v0.16b
        stp     q5, q4, [sp, #16]
        ldr     q2, [sp, #208]
        tbl     v18.16b, {v30.16b-v31.16b}, v1.16b
        tbl     v5.16b, {v30.16b-v31.16b}, v7.16b
        zip2    v30.8h, v10.8h, v11.8h
        tbl     v31.16b, {v10.16b-v11.16b}, v0.16b
        tbl     v12.16b, {v10.16b-v11.16b}, v1.16b
        tbl     v10.16b, {v10.16b-v11.16b}, v7.16b
        zip2    v11.8h, v28.8h, v29.8h
        tbl     v13.16b, {v28.16b-v29.16b}, v0.16b
        tbl     v4.16b, {v28.16b-v29.16b}, v1.16b
        tbl     v28.16b, {v28.16b-v29.16b}, v7.16b
        tbl     v29.16b, {v24.16b-v25.16b}, v0.16b
        tbl     v0.16b, {v22.16b-v23.16b}, v2.16b
        tbl     v3.16b, {v24.16b-v25.16b}, v1.16b
        tbl     v7.16b, {v24.16b-v25.16b}, v7.16b
        zip2    v24.8h, v24.8h, v25.8h
        tbl     v25.16b, {v20.16b-v21.16b}, v2.16b
        tbl     v1.16b, {v16.16b-v17.16b}, v2.16b
        tbl     v2.16b, {v14.16b-v15.16b}, v2.16b
        mov     v30.s[1], v0.s[1]
        mov     v8.s[1], v25.s[1]
        mov     v11.s[1], v1.s[1]
        movi    v1.4s, #0x8, lsl #24
        mov     v24.s[1], v2.s[1]
        movi    v0.4s, #0x8, lsl #24
        sxtl    v25.4s, v30.4h
        sxtl    v2.4s, v8.4h
        mla     v1.4s, v25.4s, v26.4s
        movi    v25.4s, #0x8, lsl #24
        ldp     q19, q6, [sp, #176]
        mla     v0.4s, v2.4s, v26.4s
        movi    v2.4s, #0x8, lsl #24
        sxtl    v24.4s, v24.4h
        sxtl    v30.4s, v11.4h
        mla     v25.4s, v24.4s, v26.4s
        zip2    v24.8h, v20.8h, v21.8h
        mla     v2.4s, v30.4s, v26.4s
        tbl     v30.16b, {v20.16b-v21.16b}, v6.16b
        tbl     v20.16b, {v20.16b-v21.16b}, v19.16b
        zip2    v21.8h, v22.8h, v23.8h
        tbl     v8.16b, {v22.16b-v23.16b}, v6.16b
        tbl     v22.16b, {v22.16b-v23.16b}, v19.16b
        zip2    v23.8h, v16.8h, v17.8h
        tbl     v11.16b, {v16.16b-v17.16b}, v6.16b
        tbl     v16.16b, {v16.16b-v17.16b}, v19.16b
        tbl     v17.16b, {v14.16b-v15.16b}, v6.16b
        tbl     v6.16b, {v14.16b-v15.16b}, v19.16b
        zip2    v19.8h, v14.8h, v15.8h
        mov     v27.s[1], v24.s[1]
        mov     v31.s[1], v21.s[1]
        mov     v13.s[1], v23.s[1]
        mov     v29.s[1], v19.s[1]
        movi    v19.4s, #0x8, lsl #24
        movi    v21.4s, #0x8, lsl #24
        sxtl    v23.4s, v27.4h
        sxtl    v24.4s, v31.4h
        mla     v19.4s, v23.4s, v26.4s
        movi    v23.4s, #0x8, lsl #24
        mla     v21.4s, v24.4s, v26.4s
        movi    v24.4s, #0x8, lsl #24
        sxtl    v27.4s, v13.4h
        mov     v12.s[1], v8.s[1]
        sxtl    v29.4s, v29.4h
        mla     v23.4s, v27.4s, v26.4s
        mov     v18.s[1], v30.s[1]
        ldr     q30, [sp]
        movi    v27.4s, #0x8, lsl #24
        mla     v24.4s, v29.4s, v26.4s
        mov     v3.s[1], v17.s[1]
        movi    v17.4s, #0x8, lsl #24
        sxtl    v29.4s, v12.4h
        mov     v4.s[1], v11.s[1]
        sxtl    v18.4s, v18.4h
        mla     v27.4s, v29.4s, v26.4s
        movi    v29.4s, #0x8, lsl #24
        mla     v17.4s, v18.4s, v26.4s
        movi    v18.4s, #0x8, lsl #24
        sxtl    v3.4s, v3.4h
        mov     v5.s[1], v20.s[1]
        ldr     q20, [sp, #48]
        sxtl    v4.4s, v4.4h
        mla     v29.4s, v3.4s, v26.4s
        movi    v3.4s, #0x8, lsl #24
        mla     v18.4s, v4.4s, v26.4s
        mov     v10.s[1], v22.s[1]
        ldr     q22, [sp, #80]
        mov     v28.s[1], v16.s[1]
        sxtl    v4.4s, v5.4h
        movi    v5.4s, #0x8, lsl #24
        mla     v3.4s, v4.4s, v26.4s
        movi    v4.4s, #0x8, lsl #24
        mov     v7.s[1], v6.s[1]
        sxtl    v6.4s, v10.4h
        sxtl    v16.4s, v28.4h
        mla     v4.4s, v6.4s, v26.4s
        mla     v5.4s, v16.4s, v26.4s
        ldp     q6, q16, [sp, #96]
        ushr    v20.4s, v20.4s, #24
        ushr    v22.4s, v22.4s, #24
        ushr    v28.4s, v9.4s, #24
        ushr    v30.4s, v30.4s, #24
        sxtl    v7.4s, v7.4h
        ushr    v1.4s, v1.4s, #28
        ushr    v6.4s, v6.4s, #24
        ushr    v0.4s, v0.4s, #28
        ushr    v2.4s, v2.4s, #28
        ushr    v16.4s, v16.4s, #24
        ushr    v19.4s, v19.4s, #24
        uzp1    v0.8h, v0.8h, v1.8h
        ushr    v4.4s, v4.4s, #24
        uzp1    v6.8h, v16.8h, v6.8h
        uzp1    v16.8h, v22.8h, v20.8h
        ldp     q20, q22, [sp, #16]
        ushr    v3.4s, v3.4s, #24
        ushr    v5.4s, v5.4s, #24
        ushr    v18.4s, v18.4s, #28
        uzp1    v6.16b, v16.16b, v6.16b
        ushr    v20.4s, v20.4s, #24
        uzp1    v3.8h, v3.8h, v4.8h
        ushr    v22.4s, v22.4s, #24
        uzp1    v20.8h, v22.8h, v20.8h
        uzp1    v22.8h, v30.8h, v28.8h
        movi    v28.4s, #0x8, lsl #24
        uzp1    v16.16b, v22.16b, v20.16b
        ldr     q22, [sp, #64]
        movi    v20.16b, #0xf0
        mla     v28.4s, v7.4s, v26.4s
        ldr     q7, [sp, #128]
        and     v6.16b, v6.16b, v20.16b
        orr     v6.16b, v6.16b, v7.16b
        and     v16.16b, v16.16b, v20.16b
        orr     v7.16b, v16.16b, v22.16b
        ushr    v16.4s, v25.4s, #28
        ushr    v4.4s, v28.4s, #24
        uzp1    v1.8h, v2.8h, v16.8h
        ushr    v2.4s, v27.4s, #28
        ushr    v16.4s, v17.4s, #28
        ushr    v17.4s, v21.4s, #24
        uzp1    v2.8h, v16.8h, v2.8h
        uzp1    v16.8h, v19.8h, v17.8h
        ushr    v17.4s, v24.4s, #24
        ushr    v19.4s, v23.4s, #24
        uzp1    v4.8h, v5.8h, v4.8h
        uzp1    v17.8h, v19.8h, v17.8h
        ushr    v19.4s, v29.4s, #28
        uzp1    v0.16b, v1.16b, v0.16b
        uzp1    v5.8h, v18.8h, v19.8h
        uzp1    v16.16b, v17.16b, v16.16b
        uzp1    v1.16b, v4.16b, v3.16b
        uzp1    v2.16b, v5.16b, v2.16b
        and     v3.16b, v16.16b, v20.16b
        orr     v8.16b, v3.16b, v0.16b
        and     v0.16b, v1.16b, v20.16b
        orr     v9.16b, v0.16b, v2.16b
        st4     {v6.16b-v9.16b}, [x0]
L2cf8:
        ldp     d9, d8, [sp, #272]
        ldp     d11, d10, [sp, #256]
        ldp     d13, d12, [sp, #240]
        ldp     d15, d14, [sp, #224]
        ldr     x29, [sp, #288]
        add     sp, sp, #0x130
        ret

// mlkem_poly_compress_d10 (0x9c bytes)
L2d14:
        mov     w9, #0xbc00
        mov     x8, xzr
        movk    w9, #0x9d7d, lsl #16
        add     x10, x1, #0x6
        add     x11, x0, #0x2
        mov     x12, #0x100000000
L2d2c:
        add     x13, x10, x8
        add     x8, x8, #0x8
        cmp     x8, #0x200
        ldursh  x15, [x13, #-4]
        ldursh  x14, [x13, #-6]
        ldursh  x16, [x13, #-2]
        madd    x15, x15, x9, x12
        ldrsh   x13, [x13]
        madd    x14, x14, x9, x12
        madd    x16, x16, x9, x12
        lsr     x18, x15, #31
        lsr     x17, x14, #33
        ubfx    x14, x14, #41, #2
        and     w18, w18, #0xfc
        madd    x13, x13, x9, x12
        orr     w14, w18, w14
        lsr     x18, x16, #29
        ubfx    x15, x15, #39, #4
        and     w18, w18, #0xf0
        orr     w15, w18, w15
        lsr     x18, x13, #27
        ubfx    x16, x16, #37, #6
        and     w18, w18, #0xc0
        orr     w16, w18, w16
        lsr     x13, x13, #35
        sturb   w17, [x11, #-2]
        sturb   w14, [x11, #-1]
        strb    w15, [x11]
        strb    w16, [x11, #1]
        strb    w13, [x11, #2]
        add     x11, x11, #0x5
        b.ne    L2d2c
        ret

// mlkem_poly_decompress_d4 (0x3cc bytes)
L2db0:
        add     x8, x1, #0x80
        cmp     x8, x0
        b.ls    L2e10
        add     x8, x0, #0x200
        cmp     x8, x1
        b.ls    L2e10
        mov     x8, xzr
        add     x9, x0, #0x2
        mov     w10, #0xd01
        mov     w11, #0x8
L2dd8:
        ldrb    w12, [x1, x8]
        and     w12, w12, #0xf
        madd    w12, w12, w10, w11
        lsr     w12, w12, #4
        sturh   w12, [x9, #-2]
        ldrb    w12, [x1, x8]
        add     x8, x8, #0x1
        cmp     x8, #0x80
        lsr     w12, w12, #4
        madd    w12, w12, w10, w11
        lsr     w12, w12, #4
        strh    w12, [x9], #4
        b.ne    L2dd8
        ret
L2e10:
        movi    v1.16b, #0xf
        ldr     q2, [x1]
        mov     w8, #0xd01
        add     x9, x0, #0x1e0
        ushr    v3.16b, v2.16b, #4
        and     v2.16b, v2.16b, v1.16b
        dup     v0.8h, w8
        uxtl2   v4.8h, v2.16b
        mov     x8, x0
        uxtl    v2.8h, v2.8b
        uxtl2   v5.8h, v3.16b
        umull   v6.4s, v2.4h, v0.4h
        uxtl    v3.8h, v3.8b
        umull2  v2.4s, v2.8h, v0.8h
        umull2  v7.4s, v4.8h, v0.8h
        rshrn   v16.4h, v6.4s, #4
        umull   v6.4s, v3.4h, v0.4h
        umull   v4.4s, v4.4h, v0.4h
        umull2  v3.4s, v3.8h, v0.8h
        rshrn2  v16.8h, v2.4s, #4
        rshrn   v17.4h, v6.4s, #4
        umull   v2.4s, v5.4h, v0.4h
        rshrn   v18.4h, v4.4s, #4
        umull2  v4.4s, v5.8h, v0.8h
        rshrn2  v17.8h, v3.4s, #4
        rshrn2  v18.8h, v7.4s, #4
        rshrn   v19.4h, v2.4s, #4
        st2     {v16.8h-v17.8h}, [x8], #32
        rshrn2  v19.8h, v4.4s, #4
        st2     {v18.8h-v19.8h}, [x8]
        add     x8, x0, #0x40
        ldr     q2, [x1, #16]
        and     v3.16b, v2.16b, v1.16b
        ushr    v2.16b, v2.16b, #4
        uxtl2   v4.8h, v3.16b
        uxtl    v3.8h, v3.8b
        uxtl2   v5.8h, v2.16b
        umull   v6.4s, v3.4h, v0.4h
        uxtl    v2.8h, v2.8b
        umull2  v3.4s, v3.8h, v0.8h
        umull2  v7.4s, v4.8h, v0.8h
        umull   v4.4s, v4.4h, v0.4h
        rshrn   v16.4h, v6.4s, #4
        umull   v6.4s, v2.4h, v0.4h
        umull2  v2.4s, v2.8h, v0.8h
        rshrn2  v16.8h, v3.4s, #4
        rshrn   v3.4h, v4.4s, #4
        rshrn   v17.4h, v6.4s, #4
        umull   v6.4s, v5.4h, v0.4h
        umull2  v5.4s, v5.8h, v0.8h
        rshrn2  v3.8h, v7.4s, #4
        rshrn2  v17.8h, v2.4s, #4
        rshrn   v4.4h, v6.4s, #4
        st2     {v16.8h-v17.8h}, [x8]
        add     x8, x0, #0x60
        rshrn2  v4.8h, v5.4s, #4
        st2     {v3.8h-v4.8h}, [x8]
        add     x8, x0, #0x80
        ldr     q2, [x1, #32]
        and     v3.16b, v2.16b, v1.16b
        ushr    v2.16b, v2.16b, #4
        uxtl2   v4.8h, v3.16b
        uxtl    v3.8h, v3.8b
        uxtl2   v5.8h, v2.16b
        umull   v6.4s, v3.4h, v0.4h
        uxtl    v2.8h, v2.8b
        umull2  v3.4s, v3.8h, v0.8h
        umull2  v7.4s, v4.8h, v0.8h
        umull   v4.4s, v4.4h, v0.4h
        rshrn   v16.4h, v6.4s, #4
        umull   v6.4s, v2.4h, v0.4h
        umull2  v2.4s, v2.8h, v0.8h
        rshrn2  v16.8h, v3.4s, #4
        rshrn   v3.4h, v4.4s, #4
        rshrn   v17.4h, v6.4s, #4
        umull   v6.4s, v5.4h, v0.4h
        umull2  v5.4s, v5.8h, v0.8h
        rshrn2  v3.8h, v7.4s, #4
        rshrn2  v17.8h, v2.4s, #4
        rshrn   v4.4h, v6.4s, #4
        st2     {v16.8h-v17.8h}, [x8]
        add     x8, x0, #0xa0
        rshrn2  v4.8h, v5.4s, #4
        st2     {v3.8h-v4.8h}, [x8]
        add     x8, x0, #0xc0
        ldr     q2, [x1, #48]
        and     v3.16b, v2.16b, v1.16b
        ushr    v2.16b, v2.16b, #4
        uxtl2   v4.8h, v3.16b
        uxtl    v3.8h, v3.8b
        uxtl2   v5.8h, v2.16b
        umull   v6.4s, v3.4h, v0.4h
        uxtl    v2.8h, v2.8b
        umull2  v3.4s, v3.8h, v0.8h
        umull2  v7.4s, v4.8h, v0.8h
        umull   v4.4s, v4.4h, v0.4h
        rshrn   v16.4h, v6.4s, #4
        umull   v6.4s, v2.4h, v0.4h
        umull2  v2.4s, v2.8h, v0.8h
        rshrn2  v16.8h, v3.4s, #4
        rshrn   v3.4h, v4.4s, #4
        rshrn   v17.4h, v6.4s, #4
        umull   v6.4s, v5.4h, v0.4h
        umull2  v5.4s, v5.8h, v0.8h
        rshrn2  v3.8h, v7.4s, #4
        rshrn2  v17.8h, v2.4s, #4
        rshrn   v4.4h, v6.4s, #4
        st2     {v16.8h-v17.8h}, [x8]
        add     x8, x0, #0xe0
        rshrn2  v4.8h, v5.4s, #4
        st2     {v3.8h-v4.8h}, [x8]
        add     x8, x0, #0x100
        ldr     q2, [x1, #64]
        and     v3.16b, v2.16b, v1.16b
        ushr    v2.16b, v2.16b, #4
        uxtl2   v4.8h, v3.16b
        uxtl    v3.8h, v3.8b
        uxtl2   v5.8h, v2.16b
        umull   v6.4s, v3.4h, v0.4h
        uxtl    v2.8h, v2.8b
        umull2  v3.4s, v3.8h, v0.8h
        umull2  v7.4s, v4.8h, v0.8h
        umull   v4.4s, v4.4h, v0.4h
        rshrn   v16.4h, v6.4s, #4
        umull   v6.4s, v2.4h, v0.4h
        umull2  v2.4s, v2.8h, v0.8h
        rshrn2  v16.8h, v3.4s, #4
        rshrn   v3.4h, v4.4s, #4
        rshrn   v17.4h, v6.4s, #4
        umull   v6.4s, v5.4h, v0.4h
        umull2  v5.4s, v5.8h, v0.8h
        rshrn2  v3.8h, v7.4s, #4
        rshrn2  v17.8h, v2.4s, #4
        rshrn   v4.4h, v6.4s, #4
        st2     {v16.8h-v17.8h}, [x8]
        add     x8, x0, #0x120
        rshrn2  v4.8h, v5.4s, #4
        st2     {v3.8h-v4.8h}, [x8]
        add     x8, x0, #0x140
        ldr     q2, [x1, #80]
        and     v3.16b, v2.16b, v1.16b
        ushr    v2.16b, v2.16b, #4
        uxtl2   v4.8h, v3.16b
        uxtl    v3.8h, v3.8b
        uxtl2   v5.8h, v2.16b
        umull   v6.4s, v3.4h, v0.4h
        uxtl    v2.8h, v2.8b
        umull2  v3.4s, v3.8h, v0.8h
        umull2  v7.4s, v4.8h, v0.8h
        umull   v4.4s, v4.4h, v0.4h
        rshrn   v16.4h, v6.4s, #4
        umull   v6.4s, v2.4h, v0.4h
        umull2  v2.4s, v2.8h, v0.8h
        rshrn2  v16.8h, v3.4s, #4
        rshrn   v3.4h, v4.4s, #4
        rshrn   v17.4h, v6.4s, #4
        umull   v6.4s, v5.4h, v0.4h
        umull2  v5.4s, v5.8h, v0.8h
        rshrn2  v3.8h, v7.4s, #4
        rshrn2  v17.8h, v2.4s, #4
        rshrn   v4.4h, v6.4s, #4
        st2     {v16.8h-v17.8h}, [x8]
        add     x8, x0, #0x160
        rshrn2  v4.8h, v5.4s, #4
        st2     {v3.8h-v4.8h}, [x8]
        add     x8, x0, #0x180
        ldr     q2, [x1, #96]
        and     v3.16b, v2.16b, v1.16b
        ushr    v2.16b, v2.16b, #4
        uxtl2   v4.8h, v3.16b
        uxtl    v3.8h, v3.8b
        uxtl2   v5.8h, v2.16b
        umull   v6.4s, v3.4h, v0.4h
        uxtl    v2.8h, v2.8b
        umull2  v3.4s, v3.8h, v0.8h
        umull   v7.4s, v4.4h, v0.4h
        rshrn   v16.4h, v6.4s, #4
        umull   v6.4s, v2.4h, v0.4h
        umull2  v4.4s, v4.8h, v0.8h
        rshrn2  v16.8h, v3.4s, #4
        rshrn   v18.4h, v7.4s, #4
        umull2  v2.4s, v2.8h, v0.8h
        rshrn   v17.4h, v6.4s, #4
        umull   v3.4s, v5.4h, v0.4h
        rshrn2  v18.8h, v4.4s, #4
        umull2  v4.4s, v5.8h, v0.8h
        rshrn2  v17.8h, v2.4s, #4
        rshrn   v19.4h, v3.4s, #4
        st2     {v16.8h-v17.8h}, [x8]
        add     x8, x0, #0x1a0
        rshrn2  v19.8h, v4.4s, #4
        st2     {v18.8h-v19.8h}, [x8]
        add     x8, x0, #0x1c0
        ldr     q2, [x1, #112]
        and     v1.16b, v2.16b, v1.16b
        ushr    v2.16b, v2.16b, #4
        uxtl2   v3.8h, v1.16b
        uxtl    v1.8h, v1.8b
        umull2  v6.4s, v3.8h, v0.8h
        umull   v5.4s, v1.4h, v0.4h
        umull2  v1.4s, v1.8h, v0.8h
        umull   v3.4s, v3.4h, v0.4h
        uxtl2   v4.8h, v2.16b
        rshrn   v16.4h, v5.4s, #4
        uxtl    v2.8h, v2.8b
        rshrn   v18.4h, v3.4s, #4
        umull   v5.4s, v2.4h, v0.4h
        rshrn2  v16.8h, v1.4s, #4
        umull   v1.4s, v4.4h, v0.4h
        umull2  v2.4s, v2.8h, v0.8h
        umull2  v0.4s, v4.8h, v0.8h
        rshrn2  v18.8h, v6.4s, #4
        rshrn   v17.4h, v5.4s, #4
        rshrn   v19.4h, v1.4s, #4
        rshrn2  v17.8h, v2.4s, #4
        rshrn2  v19.8h, v0.4s, #4
        st2     {v16.8h-v17.8h}, [x8]
        st2     {v18.8h-v19.8h}, [x9]
        ret

// mlkem_poly_decompress_d10 (0x214 bytes)
L317c:
        add     x8, x1, #0x140
        cmp     x8, x0
        b.ls    L321c
        add     x8, x0, #0x200
        cmp     x8, x1
        b.ls    L321c
        mov     x8, xzr
        add     x9, x1, #0x2
        mov     w10, #0xd01
        mov     w11, #0x200
L31a4:
        ldurb   w12, [x9, #-2]
        ldurb   w13, [x9, #-1]
        ldrb    w14, [x9]
        ldrb    w15, [x9, #1]
        ldrb    w17, [x9, #2]
        bfi     w12, w13, #8, #2
        lsr     w13, w13, #2
        lsr     w16, w14, #4
        bfi     w13, w14, #6, #4
        lsr     w14, w15, #6
        bfi     w16, w15, #4, #6
        orr     w14, w14, w17, lsl #2
        madd    w12, w12, w10, w11
        add     x9, x9, #0x5
        madd    w13, w13, w10, w11
        madd    w15, w16, w10, w11
        lsr     w12, w12, #10
        madd    w14, w14, w10, w11
        add     x16, x0, x8
        lsr     w13, w13, #10
        lsr     w15, w15, #10
        lsr     w14, w14, #10
        add     x8, x8, #0x8
        cmp     x8, #0x200
        strh    w12, [x16]
        strh    w13, [x16, #2]
        strh    w15, [x16, #4]
        strh    w14, [x16, #6]
        b.ne    L31a4
        b       L338c
L321c:
        .inst   0x90000069  // adrp x9, 0xf000
        .inst   0x9000006a  // adrp x10, 0xf000
        .inst   0x9000006c  // adrp x12, 0xf000
        .inst   0x9000006b  // adrp x11, 0xf000
        movi    v5.4s, #0x3, lsl #8
        mov     x8, xzr
        ldr     q0, [x9, #448]
        .inst   0x90000069  // adrp x9, 0xf000
        ldr     q1, [x10, #464]
        mov     w10, #0xd01
        ldr     q3, [x12, #496]
        .inst   0x9000006c  // adrp x12, 0xf000
        ldr     q2, [x11, #480]
        mov     w11, #0x3c0
        ldr     q4, [x9, #512]
        mov     w9, #0x3f0
        dup     v6.4h, w10
        ldr     q16, [x12, #528]
        dup     v7.4s, w11
        dup     v18.4s, w10
        dup     v17.4s, w9
L3270:
        ldr     s20, [x1, #16]
        ldr     q19, [x1], #20
        umov    w9, v19.b[1]
        umov    w10, v19.b[2]
        umov    w11, v19.b[6]
        umov    w12, v19.b[3]
        tbl     v24.16b, {v19.16b-v20.16b}, v1.16b
        tbl     v25.16b, {v19.16b}, v0.16b
        fmov    s21, w9
        umov    w9, v19.b[7]
        fmov    s22, w10
        umov    w10, v19.b[8]
        fmov    s23, w12
        mov     v21.h[1], w11
        umov    w11, v19.b[11]
        tbl     v24.16b, {v24.16b}, v2.16b
        mov     v22.h[1], w9
        umov    w9, v19.b[12]
        mov     v21.h[2], w11
        mov     v23.h[1], w10
        umov    w10, v19.b[13]
        mov     v22.h[2], w9
        umov    w9, v20.b[0]
        shl     v24.4s, v24.4s, #8
        tbl     v26.16b, {v19.16b-v20.16b}, v3.16b
        and     v24.16b, v24.16b, v5.16b
        mov     v21.h[3], w9
        umov    w9, v20.b[1]
        mov     v23.h[2], w10
        orr     v24.16b, v24.16b, v25.16b
        tbl     v25.16b, {v19.16b-v20.16b}, v4.16b
        mov     v22.h[3], w9
        umov    w9, v20.b[2]
        tbl     v19.16b, {v19.16b-v20.16b}, v16.16b
        bic     v21.4h, #0xff, lsl #8
        tbl     v26.16b, {v26.16b}, v2.16b
        tbl     v25.16b, {v25.16b}, v2.16b
        mov     v23.h[3], w9
        add     x9, x0, x8
        bic     v22.4h, #0xff, lsl #8
        add     x8, x8, #0x20
        ushr    v22.4h, v22.4h, #4
        ushr    v21.4h, v21.4h, #2
        tbl     v19.16b, {v19.16b}, v2.16b
        shl     v26.4s, v26.4s, #6
        uxtl    v20.4s, v22.4h
        cmp     x8, #0x200
        shl     v22.4s, v25.4s, #4
        bic     v23.4h, #0xff, lsl #8
        uxtl    v21.4s, v21.4h
        ushr    v23.4h, v23.4h, #6
        and     v26.16b, v26.16b, v7.16b
        and     v22.16b, v22.16b, v17.16b
        orr     v21.16b, v26.16b, v21.16b
        orr     v20.16b, v22.16b, v20.16b
        uxtl    v22.4s, v23.4h
        shl     v19.4s, v19.4s, #2
        xtn     v23.4h, v24.4s
        xtn     v21.4h, v21.4s
        xtn     v20.4h, v20.4s
        orr     v19.16b, v19.16b, v22.16b
        umull   v22.4s, v23.4h, v6.4h
        umull   v21.4s, v21.4h, v6.4h
        umull   v20.4s, v20.4h, v6.4h
        mul     v19.4s, v19.4s, v18.4s
        rshrn   v22.4h, v22.4s, #10
        rshrn   v23.4h, v21.4s, #10
        rshrn   v24.4h, v20.4s, #10
        rshrn   v25.4h, v19.4s, #10
        st4     {v22.4h-v25.4h}, [x9]
        b.ne    L3270
L338c:
        ret

// mlkem_poly_compress_d5 (0xcc bytes)
L3390:
        mov     w9, #0xafc0
        mov     x8, xzr
        movk    w9, #0x13, lsl #16
        add     x10, x1, #0x8
        add     x11, x0, #0x2
        mov     w12, #0x4000000
L33a8:
        ldursh  w14, [x10, #-6]
        ldursh  w15, [x10, #-4]
        ldursh  w13, [x10, #-8]
        ldursh  w16, [x10, #-2]
        madd    w14, w14, w9, w12
        madd    w15, w15, w9, w12
        ldrsh   w17, [x10]
        madd    w13, w13, w9, w12
        ldrsh   w18, [x10, #2]
        madd    w16, w16, w9, w12
        lsr     w15, w15, #25
        and     w15, w15, #0x7c
        lsr     w0, w14, #27
        bfxil   w15, w14, #30, #2
        lsr     w14, w16, #20
        ldrsh   w1, [x10, #4]
        and     w14, w14, #0x80
        extr    w13, w0, w13, #27
        add     x0, x11, x8
        orr     w14, w15, w14
        madd    w17, w17, w9, w12
        ldrsh   w2, [x10, #6]
        madd    w18, w18, w9, w12
        madd    w15, w1, w9, w12
        sturb   w13, [x0, #-2]
        sturb   w14, [x0, #-1]
        lsr     w13, w17, #23
        lsr     w14, w18, #26
        madd    w1, w2, w9, w12
        bfxil   w13, w16, #28, #4
        and     w14, w14, #0x3e
        lsr     w16, w15, #21
        bfxil   w14, w17, #31, #1
        and     w16, w16, #0xc0
        add     x8, x8, #0x5
        orr     w14, w14, w16
        lsr     w16, w1, #24
        bfxil   w16, w15, #29, #3
        add     x10, x10, #0x10
        cmp     x8, #0xa0
        strb    w13, [x0]
        strb    w14, [x0, #1]
        strb    w16, [x0, #2]
        b.ne    L33a8
        ret

// mlkem_poly_compress_d11 (0x108 bytes)
L345c:
        mov     x9, #0x7800
        mov     x8, xzr
        movk    x9, #0x3afb, lsl #16
        add     x10, x1, #0xe
        movk    x9, #0x1, lsl #32
        add     x11, x0, #0x5
        mov     x12, #0x100000000
L3478:
        add     x13, x10, x8
        add     x8, x8, #0x10
        cmp     x8, #0x200
        ldursh  x15, [x13, #-12]
        ldursh  x14, [x13, #-14]
        ldursh  x16, [x13, #-10]
        madd    x15, x15, x9, x12
        ldursh  x0, [x13, #-4]
        madd    x14, x14, x9, x12
        ldursh  x17, [x13, #-8]
        lsr     x3, x15, #30
        madd    x16, x16, x9, x12
        lsr     x2, x14, #33
        ubfx    x14, x14, #41, #3
        and     w3, w3, #0xf8
        ldursh  x18, [x13, #-6]
        orr     w14, w3, w14
        lsr     x4, x16, #33
        madd    x0, x0, x9, x12
        ldursh  x1, [x13, #-2]
        madd    x17, x17, x9, x12
        ldrsh   x13, [x13]
        madd    x18, x18, x9, x12
        lsr     x15, x15, #38
        sturb   w14, [x11, #-4]
        lsr     x14, x16, #35
        lsr     x3, x0, #33
        bfi     w15, w4, #6, #26
        sturb   w2, [x11, #-5]
        lsr     x16, x17, #32
        lsr     x2, x18, #29
        bfxil   w16, w4, #10, #1
        ubfx    x17, x17, #40, #4
        and     w2, w2, #0xf0
        madd    x13, x13, x9, x12
        sturb   w14, [x11, #-2]
        lsr     x14, x18, #37
        madd    x1, x1, x9, x12
        sturb   w15, [x11, #-3]
        orr     w15, w2, w17
        bfi     w14, w3, #7, #25
        lsr     x17, x13, #28
        sturb   w16, [x11, #-1]
        lsr     x16, x1, #31
        ubfx    x18, x1, #39, #5
        and     w17, w17, #0xe0
        strb    w15, [x11]
        lsr     x15, x0, #34
        bfxil   w16, w3, #9, #2
        strb    w14, [x11, #1]
        orr     w14, w17, w18
        lsr     x13, x13, #36
        strb    w15, [x11, #2]
        strb    w16, [x11, #3]
        strb    w14, [x11, #4]
        strb    w13, [x11, #5]
        add     x11, x11, #0xb
        b.ne    L3478
        ret

// mlkem_poly_decompress_d5 (0xa10 bytes)
L3564:
        stp     d15, d14, [sp, #-80]!
        stp     d13, d12, [sp, #16]
        stp     d11, d10, [sp, #32]
        stp     d9, d8, [sp, #48]
        str     x29, [sp, #64]
        sub     sp, sp, #0x2c0
        add     x8, x1, #0xa0
        cmp     x8, x0
        b.ls    L3694
        add     x8, x0, #0x200
        cmp     x8, x1
        b.ls    L3694
        .inst   0x90000069  // adrp x9, 0xf000
        .inst   0x9000006a  // adrp x10, 0xf000
        mov     w11, #0xd01
        movi    d0, #0xff000000ff
        mov     x8, xzr
        ldr     d1, [x9, #1632]
        add     x9, x1, #0x2
        ldr     d2, [x10, #1640]
        dup     v3.8h, w11
L35b8:
        ldrb    w10, [x9]
        ldrb    w11, [x9, #1]
        fmov    s4, w10
        ldurb   w10, [x9, #-2]
        mov     v4.s[1], w11
        ldurb   w11, [x9, #-1]
        and     w12, w10, #0x1f
        lsr     w10, w10, #5
        dup     v5.2s, w11
        bfi     w10, w11, #3, #2
        fmov    w13, s4
        fmov    s6, w12
        mov     w14, v4.s[1]
        ldrb    w11, [x9, #2]
        ushl    v4.2s, v4.2s, v2.2s
        add     x9, x9, #0x5
        ubfiz   w13, w13, #1, #4
        and     v5.8b, v5.8b, v0.8b
        mov     v6.b[1], w10
        ushl    v5.2s, v5.2s, v1.2s
        ubfiz   w12, w14, #4, #1
        ubfiz   w10, w11, #2, #3
        dup     v7.2s, w13
        fmov    s16, w12
        orr     v7.8b, v5.8b, v7.8b
        bic     v5.2s, #0x20
        mov     w13, v7.s[1]
        fmov    s7, w10
        mov     v6.b[2], v5.b[0]
        orr     v16.8b, v4.8b, v16.8b
        bic     v4.2s, #0xe0
        lsr     w10, w14, #6
        mov     v17.16b, v7.16b
        mov     w12, v4.s[1]
        mov     v17.s[1], w11
        mov     v6.b[3], w13
        fmov    s4, w10
        and     v17.8b, v17.8b, v0.8b
        mov     v6.b[4], v16.b[0]
        ushr    v17.2s, v17.2s, #3
        orr     v4.8b, v7.8b, v4.8b
        mov     w10, v17.s[1]
        mov     v6.b[5], w12
        mov     v6.b[6], v4.b[0]
        mov     v6.b[7], w10
        uxtl    v6.8h, v6.8b
        umull   v7.4s, v6.4h, v3.4h
        umull2  v6.4s, v6.8h, v3.8h
        rshrn   v7.4h, v7.4s, #5
        rshrn2  v7.8h, v6.4s, #5
        str     q7, [x0, x8]
        add     x8, x8, #0x10
        cmp     x8, #0x200
        b.ne    L35b8
        b       L3f58
L3694:
        .inst   0x90000068  // adrp x8, 0xf000
        .inst   0x90000069  // adrp x9, 0xf000
        ldp     q5, q2, [x1, #16]
        .inst   0x9000006a  // adrp x10, 0xf000
        .inst   0x9000006b  // adrp x11, 0xf000
        movi    v24.16b, #0x1f
        ldp     q3, q7, [x1, #48]
        ldr     q0, [x8, #544]
        .inst   0x90000068  // adrp x8, 0xf000
        ldr     q4, [x1]
        ldr     q16, [x9, #560]
        .inst   0x90000069  // adrp x9, 0xf000
        str     q0, [sp, #688]
        ldr     q19, [x10, #576]
        tbl     v1.16b, {v2.16b-v3.16b}, v0.16b
        ldr     q21, [x11, #624]
        str     q16, [sp, #576]
        ldr     q20, [x8, #592]
        tbl     v0.16b, {v4.16b-v5.16b}, v16.16b
        ldr     q16, [x9, #608]
        .inst   0x90000069  // adrp x9, 0xf000
        .inst   0x90000068  // adrp x8, 0xf000
        stp     q21, q16, [sp, #544]
        .inst   0x9000006a  // adrp x10, 0xf000
        .inst   0x9000006b  // adrp x11, 0xf000
        tbl     v17.16b, {v2.16b-v3.16b}, v16.16b
        ldr     q18, [x9, #640]
        .inst   0x90000069  // adrp x9, 0xf000
        str     q19, [sp, #336]
        tbl     v6.16b, {v0.16b-v1.16b}, v19.16b
        ldr     q1, [x8, #656]
        tbl     v16.16b, {v4.16b-v5.16b}, v21.16b
        .inst   0x90000068  // adrp x8, 0xf000
        ldr     q21, [x9, #672]
        .inst   0x90000069  // adrp x9, 0xf000
        str     q20, [sp, #416]
        ldr     q30, [x11, #928]
        tbl     v0.16b, {v6.16b-v7.16b}, v20.16b
        stp     q21, q1, [sp, #480]
        tbl     v6.16b, {v16.16b-v17.16b}, v19.16b
        tbl     v17.16b, {v2.16b-v3.16b}, v1.16b
        ldr     q19, [x10, #688]
        tbl     v16.16b, {v4.16b-v5.16b}, v21.16b
        ldr     q21, [x8, #720]
        ldr     q20, [x9, #736]
        .inst   0x9000006a  // adrp x10, 0xf000
        .inst   0x90000068  // adrp x8, 0xf000
        .inst   0x90000069  // adrp x9, 0xf000
        tbl     v1.16b, {v6.16b-v7.16b}, v18.16b
        str     q18, [sp, #464]
        tbl     v6.16b, {v16.16b-v17.16b}, v19.16b
        str     q20, [sp, #528]
        tbl     v17.16b, {v2.16b-v3.16b}, v21.16b
        ldr     q18, [x10, #704]
        tbl     v16.16b, {v4.16b-v5.16b}, v20.16b
        ldr     q20, [x8, #768]
        str     q21, [sp, #512]
        ldr     q21, [x9, #784]
        mov     v22.16b, v19.16b
        .inst   0x9000006a  // adrp x10, 0xf000
        .inst   0x90000068  // adrp x8, 0xf000
        str     q19, [sp, #320]
        tbl     v19.16b, {v6.16b-v7.16b}, v18.16b
        str     q18, [sp, #400]
        tbl     v6.16b, {v16.16b-v17.16b}, v22.16b
        ldr     q18, [x10, #752]
        tbl     v17.16b, {v2.16b-v3.16b}, v20.16b
        ldr     q2, [x8, #800]
        tbl     v16.16b, {v4.16b-v5.16b}, v21.16b
        .inst   0x90000068  // adrp x8, 0xf000
        movi    v4.16b, #0x18
        str     q21, [sp, #448]
        tbl     v3.16b, {v6.16b-v7.16b}, v18.16b
        stp     q2, q18, [sp, #352]
        movi    v5.16b, #0x1e
        tbl     v6.16b, {v16.16b-v17.16b}, v2.16b
        ldr     q2, [x8, #816]
        mov     w8, #0xd01
        str     q20, [sp, #432]
        and     v29.16b, v0.16b, v24.16b
        .inst   0x90000069  // adrp x9, 0xf000
        str     q2, [sp, #384]
        .inst   0x9000006a  // adrp x10, 0xf000
        tbl     v10.16b, {v6.16b-v7.16b}, v2.16b
        shl     v2.16b, v1.16b, #3
        dup     v28.8h, w8
        .inst   0x90000068  // adrp x8, 0xf000
        and     v9.16b, v2.16b, v4.16b
        ushr    v2.16b, v1.16b, #2
        movi    v4.16b, #0x10
        ldr     q27, [x10, #896]
        and     v6.16b, v2.16b, v24.16b
        .inst   0x9000006a  // adrp x10, 0xf000
        shl     v2.16b, v3.16b, #4
        .inst   0x9000006b  // adrp x11, 0xf000
        shl     v7.16b, v10.16b, #2
        and     v2.16b, v2.16b, v4.16b
        movi    v4.16b, #0x1c
        usra    v2.16b, v19.16b, #4
        usra    v9.16b, v0.16b, #5
        add     v0.16b, v19.16b, v19.16b
        and     v17.16b, v7.16b, v4.16b
        usra    v17.16b, v3.16b, #6
        uxtl    v7.8h, v2.8b
        uxtl    v16.8h, v29.8b
        uxtl    v21.8h, v17.8b
        umull   v22.4s, v7.4h, v28.4h
        umull   v23.4s, v21.4h, v28.4h
        uxtl    v18.8h, v6.8b
        and     v19.16b, v0.16b, v5.16b
        umull   v0.4s, v16.4h, v28.4h
        rshrn   v4.4h, v22.4s, #5
        uxtl2   v22.8h, v2.16b
        rshrn   v5.4h, v23.4s, #5
        uxtl2   v2.8h, v17.16b
        uxtl    v17.8h, v9.8b
        str     q22, [sp, #144]
        umull   v20.4s, v18.4h, v28.4h
        umull   v23.4s, v17.4h, v28.4h
        usra    v19.16b, v1.16b, #7
        rshrn   v0.4h, v0.4s, #5
        rshrn   v1.4h, v20.4s, #5
        ushr    v3.16b, v3.16b, #1
        rshrn2  v0.8h, v23.4s, #5
        str     q19, [sp, #64]
        uxtl    v23.8h, v19.8b
        umull2  v20.4s, v21.8h, v28.8h
        umull   v21.4s, v22.4h, v28.4h
        umull   v22.4s, v2.4h, v28.4h
        and     v11.16b, v3.16b, v24.16b
        ldr     q24, [x9, #864]
        umull   v3.4s, v23.4h, v28.4h
        .inst   0x90000069  // adrp x9, 0xf000
        rshrn2  v5.8h, v20.4s, #5
        rshrn   v20.4h, v21.4s, #5
        umull2  v2.4s, v2.8h, v28.8h
        rshrn   v21.4h, v22.4s, #5
        rshrn2  v1.8h, v3.4s, #5
        ldr     q3, [x8, #832]
        uxtl2   v19.8h, v29.16b
        .inst   0x90000068  // adrp x8, 0xf000
        uxtl2   v6.8h, v6.16b
        rshrn2  v21.8h, v2.4s, #5
        tbl     v2.16b, {v0.16b-v1.16b}, v3.16b
        mov     v26.16b, v3.16b
        tbl     v3.16b, {v0.16b-v1.16b}, v27.16b
        umull2  v7.4s, v7.8h, v28.8h
        str     q2, [sp, #208]
        tbl     v2.16b, {v0.16b-v1.16b}, v24.16b
        tbl     v0.16b, {v0.16b-v1.16b}, v30.16b
        str     q3, [sp, #160]
        umull2  v1.4s, v16.8h, v28.8h
        umull2  v16.4s, v17.8h, v28.8h
        umull   v17.4s, v6.4h, v28.4h
        stp     q0, q2, [sp, #176]
        rshrn   v12.4h, v7.4s, #5
        umull   v0.4s, v19.4h, v28.4h
        uxtl    v25.8h, v11.8b
        umull2  v18.4s, v18.8h, v28.8h
        umull   v22.4s, v25.4h, v28.4h
        rshrn   v2.4h, v0.4s, #5
        rshrn   v3.4h, v17.4s, #5
        rshrn   v0.4h, v1.4s, #5
        umull2  v17.4s, v25.8h, v28.8h
        rshrn   v1.4h, v18.4s, #5
        ushr    v18.16b, v10.16b, #3
        rshrn2  v4.8h, v22.4s, #5
        ldr     q22, [x10, #912]
        uxtl    v10.8h, v18.8b
        str     q18, [sp, #16]
        rshrn2  v12.8h, v17.4s, #5
        ldr     q17, [x8, #848]
        rshrn2  v0.8h, v16.4s, #5
        ldr     q18, [x9, #880]
        umull   v7.4s, v10.4h, v28.4h
        str     q22, [sp, #656]
        umull2  v16.4s, v23.8h, v28.8h
        str     q17, [sp, #624]
        tbl     v23.16b, {v4.16b-v5.16b}, v17.16b
        ldr     q17, [x11, #944]
        str     q18, [sp, #672]
        .inst   0x90000068  // adrp x8, 0xf000
        tbl     v18.16b, {v4.16b-v5.16b}, v18.16b
        rshrn   v7.4h, v7.4s, #5
        tbl     v22.16b, {v4.16b-v5.16b}, v22.16b
        .inst   0x90000069  // adrp x9, 0xf000
        tbl     v4.16b, {v4.16b-v5.16b}, v17.16b
        .inst   0x9000006a  // adrp x10, 0xf000
        rshrn2  v1.8h, v16.4s, #5
        ldr     q31, [x8, #960]
        mov     v13.16b, v5.16b
        .inst   0x90000068  // adrp x8, 0xf000
        mov     v23.h[7], v7.h[0]
        str     q17, [sp, #640]
        mov     v18.h[7], v7.h[1]
        ldr     q8, [x9, #976]
        mov     v22.h[7], v7.h[2]
        ldr     q15, [x10, #992]
        mov     v4.h[7], v7.h[3]
        ldr     q17, [x8, #1008]
        tbl     v7.16b, {v0.16b-v1.16b}, v26.16b
        stp     q31, q8, [sp, #224]
        tbl     v5.16b, {v0.16b-v1.16b}, v24.16b
        stp     q18, q23, [sp, #112]
        uxtl2   v9.8h, v9.16b
        str     q17, [sp, #608]
        tbl     v14.16b, {v0.16b-v1.16b}, v30.16b
        stp     q4, q22, [sp, #80]
        tbl     v29.16b, {v12.16b-v13.16b}, v8.16b
        add     x8, sp, #0x240
        stp     q5, q7, [sp, #32]
        tbl     v7.16b, {v0.16b-v1.16b}, v27.16b
        umull   v1.4s, v9.4h, v28.4h
        umull2  v0.4s, v10.8h, v28.8h
        tbl     v10.16b, {v12.16b-v13.16b}, v31.16b
        tbl     v25.16b, {v12.16b-v13.16b}, v15.16b
        str     q7, [sp]
        rshrn2  v2.8h, v1.4s, #5
        ldr     q1, [sp, #64]
        tbl     v12.16b, {v12.16b-v13.16b}, v17.16b
        rshrn   v0.4h, v0.4s, #5
        uxtl2   v23.8h, v1.16b
        mov     v7.16b, v30.16b
        umull   v13.4s, v23.4h, v28.4h
        mov     v10.h[7], v0.h[0]
        mov     v29.h[7], v0.h[1]
        mov     v25.h[7], v0.h[2]
        mov     v12.h[7], v0.h[3]
        ldr     q0, [sp, #144]
        rshrn2  v3.8h, v13.4s, #5
        uxtl2   v13.8h, v11.16b
        umull2  v19.4s, v19.8h, v28.8h
        umull   v30.4s, v13.4h, v28.4h
        umull2  v11.4s, v0.8h, v28.8h
        mov     v4.16b, v26.16b
        mov     v16.16b, v24.16b
        mov     v5.16b, v27.16b
        stp     q16, q4, [sp, #288]
        rshrn2  v20.8h, v30.4s, #5
        stp     q7, q5, [sp, #256]
        rshrn   v0.4h, v19.4s, #5
        rshrn   v26.4h, v11.4s, #5
        tbl     v30.16b, {v2.16b-v3.16b}, v4.16b
        tbl     v19.16b, {v2.16b-v3.16b}, v16.16b
        mov     v22.16b, v16.16b
        tbl     v11.16b, {v2.16b-v3.16b}, v5.16b
        tbl     v16.16b, {v2.16b-v3.16b}, v7.16b
        ldr     q2, [sp, #16]
        umull2  v6.4s, v6.8h, v28.8h
        mov     v18.16b, v5.16b
        uxtl2   v3.8h, v2.16b
        ldr     q2, [sp, #624]
        mov     v24.16b, v4.16b
        rshrn   v1.4h, v6.4s, #5
        umull2  v6.4s, v13.8h, v28.8h
        tbl     v13.16b, {v20.16b-v21.16b}, v2.16b
        ldr     q2, [sp, #672]
        mov     v17.16b, v7.16b
        mov     v14.d[1], v12.d[1]
        tbl     v5.16b, {v20.16b-v21.16b}, v2.16b
        ldr     q2, [sp, #656]
        rshrn2  v26.8h, v6.4s, #5
        umull2  v6.4s, v9.8h, v28.8h
        umull   v9.4s, v3.4h, v28.4h
        tbl     v4.16b, {v20.16b-v21.16b}, v2.16b
        ldr     q2, [sp, #640]
        mov     v27.16b, v21.16b
        rshrn2  v0.8h, v6.4s, #5
        tbl     v20.16b, {v20.16b-v21.16b}, v2.16b
        ldr     q2, [sp, #608]
        umull2  v6.4s, v23.8h, v28.8h
        rshrn   v21.4h, v9.4s, #5
        umull2  v3.4s, v3.8h, v28.8h
        tbl     v7.16b, {v26.16b-v27.16b}, v8.16b
        mov     v13.h[7], v21.h[0]
        mov     v5.h[7], v21.h[1]
        mov     v4.h[7], v21.h[2]
        mov     v20.h[7], v21.h[3]
        rshrn2  v1.8h, v6.4s, #5
        tbl     v6.16b, {v26.16b-v27.16b}, v31.16b
        tbl     v21.16b, {v26.16b-v27.16b}, v15.16b
        tbl     v26.16b, {v26.16b-v27.16b}, v2.16b
        rshrn   v3.4h, v3.4s, #5
        tbl     v27.16b, {v0.16b-v1.16b}, v24.16b
        tbl     v9.16b, {v0.16b-v1.16b}, v22.16b
        tbl     v2.16b, {v0.16b-v1.16b}, v18.16b
        tbl     v0.16b, {v0.16b-v1.16b}, v17.16b
        ldr     q1, [sp]
        mov     v26.h[7], v3.h[3]
        mov     v21.h[7], v3.h[2]
        mov     v7.h[7], v3.h[1]
        mov     v6.h[7], v3.h[0]
        mov     v0.d[1], v26.d[1]
        mov     v2.d[1], v21.d[1]
        mov     v11.d[1], v4.d[1]
        mov     v19.d[1], v5.d[1]
        ldp     q4, q5, [sp, #32]
        stp     q2, q0, [x0, #224]
        mov     v1.d[1], v25.d[1]
        mov     v9.d[1], v7.d[1]
        mov     v4.d[1], v29.d[1]
        mov     v27.d[1], v6.d[1]
        ldp     q2, q3, [sp, #160]
        mov     v5.d[1], v10.d[1]
        stp     q1, q14, [x0, #96]
        mov     v16.d[1], v20.d[1]
        mov     v30.d[1], v13.d[1]
        stp     q27, q9, [x0, #192]
        mov     v31.16b, v15.16b
        stp     q5, q4, [x0, #64]
        ldr     q0, [sp, #80]
        stp     q11, q16, [x0, #160]
        ldr     q1, [sp, #192]
        stp     q30, q19, [x0, #128]
        mov     v3.d[1], v0.d[1]
        ldr     q0, [sp, #96]
        ldr     q6, [sp, #688]
        ldr     q16, [sp, #576]
        mov     v2.d[1], v0.d[1]
        ldp     q0, q4, [sp, #112]
        ldp     q19, q17, [sp, #320]
        mov     v1.d[1], v0.d[1]
        stp     q2, q3, [x0, #32]
        ldr     q0, [sp, #208]
        mov     v0.d[1], v4.d[1]
        stp     q0, q1, [x0]
        ldp     q5, q0, [x1, #96]
        ldp     q1, q3, [x1, #128]
        tbl     v7.16b, {v0.16b-v1.16b}, v6.16b
        ldr     q4, [x1, #80]
        tbl     v6.16b, {v4.16b-v5.16b}, v16.16b
        tbl     v2.16b, {v6.16b-v7.16b}, v17.16b
        ldp     q16, q6, [sp, #544]
        tbl     v7.16b, {v0.16b-v1.16b}, v6.16b
        tbl     v6.16b, {v4.16b-v5.16b}, v16.16b
        ldr     q16, [sp, #416]
        tbl     v16.16b, {v2.16b-v3.16b}, v16.16b
        tbl     v2.16b, {v6.16b-v7.16b}, v17.16b
        ldp     q17, q6, [sp, #480]
        tbl     v7.16b, {v0.16b-v1.16b}, v6.16b
        tbl     v6.16b, {v4.16b-v5.16b}, v17.16b
        ldr     q17, [sp, #464]
        tbl     v17.16b, {v2.16b-v3.16b}, v17.16b
        tbl     v2.16b, {v6.16b-v7.16b}, v19.16b
        ldp     q6, q18, [sp, #512]
        tbl     v7.16b, {v0.16b-v1.16b}, v6.16b
        tbl     v6.16b, {v4.16b-v5.16b}, v18.16b
        ldr     q18, [sp, #400]
        tbl     v18.16b, {v2.16b-v3.16b}, v18.16b
        tbl     v2.16b, {v6.16b-v7.16b}, v19.16b
        ldr     q6, [sp, #432]
        tbl     v1.16b, {v0.16b-v1.16b}, v6.16b
        ldr     q6, [sp, #448]
        tbl     v0.16b, {v4.16b-v5.16b}, v6.16b
        ldr     q4, [sp, #368]
        tbl     v7.16b, {v2.16b-v3.16b}, v4.16b
        ldr     q4, [sp, #352]
        tbl     v2.16b, {v0.16b-v1.16b}, v4.16b
        ldr     q0, [sp, #384]
        tbl     v4.16b, {v2.16b-v3.16b}, v0.16b
        shl     v0.16b, v17.16b, #3
        movi    v3.16b, #0x18
        movi    v2.16b, #0x1f
        and     v21.16b, v0.16b, v3.16b
        ushr    v0.16b, v17.16b, #2
        and     v1.16b, v16.16b, v2.16b
        and     v6.16b, v0.16b, v2.16b
        movi    v2.16b, #0x1e
        add     v0.16b, v18.16b, v18.16b
        movi    v3.16b, #0x1f
        usra    v21.16b, v16.16b, #5
        and     v23.16b, v0.16b, v2.16b
        movi    v2.16b, #0x10
        shl     v0.16b, v7.16b, #4
        usra    v23.16b, v17.16b, #7
        and     v16.16b, v0.16b, v2.16b
        ushr    v0.16b, v7.16b, #1
        usra    v16.16b, v18.16b, #4
        and     v5.16b, v0.16b, v3.16b
        movi    v0.16b, #0x1c
        shl     v2.16b, v4.16b, #2
        uxtl    v3.8h, v1.8b
        ushr    v4.16b, v4.16b, #3
        uxtl    v22.8h, v5.8b
        and     v0.16b, v2.16b, v0.16b
        usra    v0.16b, v7.16b, #6
        uxtl2   v7.8h, v1.16b
        uxtl    v1.8h, v16.8b
        uxtl2   v16.8h, v16.16b
        umull   v18.4s, v1.4h, v28.4h
        umull   v19.4s, v16.4h, v28.4h
        umull2  v1.4s, v1.8h, v28.8h
        umull2  v20.4s, v16.8h, v28.8h
        rshrn   v25.4h, v18.4s, #5
        uxtl    v18.8h, v0.8b
        rshrn   v8.4h, v19.4s, #5
        uxtl2   v0.8h, v0.16b
        umull   v24.4s, v18.4h, v28.4h
        umull2  v16.4s, v22.8h, v28.8h
        rshrn   v14.4h, v1.4s, #5
        uxtl2   v1.8h, v5.16b
        rshrn   v10.4h, v20.4s, #5
        rshrn   v26.4h, v24.4s, #5
        umull   v24.4s, v0.4h, v28.4h
        umull2  v0.4s, v0.8h, v28.8h
        umull2  v18.4s, v18.8h, v28.8h
        ldp     q17, q5, [sp, #224]
        rshrn   v9.4h, v24.4s, #5
        umull   v22.4s, v22.4h, v28.4h
        rshrn2  v14.8h, v16.4s, #5
        rshrn2  v9.8h, v0.4s, #5
        umull2  v0.4s, v1.8h, v28.8h
        umull   v16.4s, v1.4h, v28.4h
        rshrn2  v26.8h, v18.4s, #5
        rshrn2  v25.8h, v22.4s, #5
        rshrn2  v10.8h, v0.4s, #5
        ldr     q0, [sp, #608]
        mov     v15.16b, v26.16b
        rshrn2  v8.8h, v16.4s, #5
        st1     {v25.2d-v26.2d}, [x8]
        mov     v11.16b, v9.16b
        tbl     v1.16b, {v14.16b-v15.16b}, v17.16b
        tbl     v16.16b, {v14.16b-v15.16b}, v5.16b
        tbl     v19.16b, {v14.16b-v15.16b}, v31.16b
        tbl     v20.16b, {v14.16b-v15.16b}, v0.16b
        tbl     v22.16b, {v10.16b-v11.16b}, v17.16b
        str     q1, [sp, #688]
        tbl     v15.16b, {v10.16b-v11.16b}, v5.16b
        tbl     v12.16b, {v10.16b-v11.16b}, v31.16b
        tbl     v24.16b, {v10.16b-v11.16b}, v0.16b
        uxtl2   v11.8h, v23.16b
        uxtl    v23.8h, v23.8b
        ldr     q17, [sp, #688]
        umull2  v0.4s, v11.8h, v28.8h
        uxtl    v18.8h, v6.8b
        umull   v2.4s, v3.4h, v28.4h
        umull2  v3.4s, v3.8h, v28.8h
        str     q0, [sp, #496]
        umull   v0.4s, v23.4h, v28.4h
        umull2  v25.4s, v18.8h, v28.8h
        umull   v18.4s, v18.4h, v28.4h
        uxtl2   v6.8h, v6.16b
        uxtl    v14.8h, v4.8b
        stp     q0, q22, [sp, #544]
        umull2  v29.4s, v7.8h, v28.8h
        rshrn   v26.4h, v3.4s, #5
        rshrn   v2.4h, v2.4s, #5
        rshrn   v27.4h, v25.4s, #5
        umull   v10.4s, v6.4h, v28.4h
        rshrn   v3.4h, v18.4s, #5
        umull2  v6.4s, v6.8h, v28.8h
        umull   v0.4s, v14.4h, v28.4h
        umull2  v14.4s, v14.8h, v28.8h
        uxtl2   v18.8h, v21.16b
        uxtl    v21.8h, v21.8b
        uxtl2   v4.8h, v4.16b
        str     q0, [sp, #608]
        umull   v30.4s, v7.4h, v28.4h
        mov     v1.16b, v31.16b
        umull2  v25.4s, v18.8h, v28.8h
        umull   v18.4s, v18.4h, v28.4h
        umull2  v31.4s, v21.8h, v28.8h
        umull   v21.4s, v21.4h, v28.4h
        umull   v11.4s, v11.4h, v28.4h
        umull2  v13.4s, v23.8h, v28.8h
        umull   v7.4s, v4.4h, v28.4h
        umull2  v5.4s, v4.8h, v28.8h
        rshrn   v28.4h, v29.4s, #5
        rshrn   v29.4h, v6.4s, #5
        rshrn   v6.4h, v14.4s, #5
        rshrn   v0.4h, v30.4s, #5
        rshrn2  v26.8h, v31.4s, #5
        rshrn   v1.4h, v10.4s, #5
        mov     v17.h[7], v6.h[0]
        mov     v16.h[7], v6.h[1]
        mov     v20.h[7], v6.h[3]
        rshrn2  v27.8h, v13.4s, #5
        rshrn2  v0.8h, v18.4s, #5
        str     q17, [sp, #688]
        ldp     q14, q13, [sp, #288]
        stp     q16, q20, [sp, #512]
        mov     v16.16b, v19.16b
        rshrn2  v1.8h, v11.4s, #5
        rshrn2  v2.8h, v21.4s, #5
        tbl     v21.16b, {v26.16b-v27.16b}, v14.16b
        ldp     q4, q23, [sp, #256]
        tbl     v22.16b, {v26.16b-v27.16b}, v13.16b
        mov     v16.h[7], v6.h[2]
        tbl     v6.16b, {v0.16b-v1.16b}, v13.16b
        rshrn2  v28.8h, v25.4s, #5
        ldp     q18, q17, [sp, #656]
        tbl     v30.16b, {v26.16b-v27.16b}, v23.16b
        tbl     v26.16b, {v26.16b-v27.16b}, v4.16b
        tbl     v27.16b, {v0.16b-v1.16b}, v14.16b
        tbl     v31.16b, {v0.16b-v1.16b}, v23.16b
        tbl     v0.16b, {v0.16b-v1.16b}, v4.16b
        ldp     q20, q19, [sp, #624]
        rshrn   v1.4h, v7.4s, #5
        tbl     v25.16b, {v8.16b-v9.16b}, v17.16b
        tbl     v10.16b, {v8.16b-v9.16b}, v18.16b
        tbl     v7.16b, {v8.16b-v9.16b}, v20.16b
        mov     v30.d[1], v16.d[1]
        tbl     v8.16b, {v8.16b-v9.16b}, v19.16b
        ldr     q9, [sp, #496]
        mov     v25.h[7], v1.h[1]
        mov     v7.h[7], v1.h[0]
        rshrn2  v29.8h, v9.4s, #5
        mov     v10.h[7], v1.h[2]
        mov     v8.h[7], v1.h[3]
        rshrn   v1.4h, v5.4s, #5
        mov     v27.d[1], v25.d[1]
        mov     v6.d[1], v7.d[1]
        tbl     v5.16b, {v28.16b-v29.16b}, v13.16b
        tbl     v9.16b, {v28.16b-v29.16b}, v14.16b
        tbl     v11.16b, {v28.16b-v29.16b}, v23.16b
        tbl     v28.16b, {v28.16b-v29.16b}, v4.16b
        stp     q6, q27, [x0, #384]
        mov     v29.16b, v4.16b
        ldp     q6, q4, [sp, #544]
        mov     v24.h[7], v1.h[3]
        mov     v15.h[7], v1.h[1]
        mov     v4.h[7], v1.h[0]
        mov     v0.d[1], v8.d[1]
        mov     v28.d[1], v24.d[1]
        ld1     {v24.2d-v25.2d}, [x8]
        mov     v31.d[1], v10.d[1]
        rshrn2  v3.8h, v6.4s, #5
        mov     v9.d[1], v15.d[1]
        ldr     q6, [sp, #688]
        mov     v5.d[1], v4.d[1]
        stp     q31, q0, [x0, #416]
        mov     v12.h[7], v1.h[2]
        ldp     q1, q0, [sp, #512]
        mov     v22.d[1], v6.d[1]
        ldr     q6, [sp, #608]
        stp     q5, q9, [x0, #448]
        mov     v21.d[1], v1.d[1]
        mov     v26.d[1], v0.d[1]
        tbl     v0.16b, {v24.16b-v25.16b}, v20.16b
        tbl     v1.16b, {v24.16b-v25.16b}, v17.16b
        tbl     v4.16b, {v24.16b-v25.16b}, v18.16b
        stp     q22, q21, [x0, #320]
        tbl     v5.16b, {v24.16b-v25.16b}, v19.16b
        stp     q30, q26, [x0, #352]
        rshrn   v6.4h, v6.4s, #5
        tbl     v7.16b, {v2.16b-v3.16b}, v13.16b
        tbl     v16.16b, {v2.16b-v3.16b}, v14.16b
        tbl     v17.16b, {v2.16b-v3.16b}, v23.16b
        tbl     v2.16b, {v2.16b-v3.16b}, v29.16b
        mov     v5.h[7], v6.h[3]
        mov     v4.h[7], v6.h[2]
        mov     v1.h[7], v6.h[1]
        mov     v0.h[7], v6.h[0]
        mov     v11.d[1], v12.d[1]
        mov     v2.d[1], v5.d[1]
        mov     v17.d[1], v4.d[1]
        mov     v16.d[1], v1.d[1]
        mov     v7.d[1], v0.d[1]
        stp     q11, q28, [x0, #480]
        stp     q17, q2, [x0, #288]
        stp     q7, q16, [x0, #256]
L3f58:
        add     sp, sp, #0x2c0
        ldp     d9, d8, [sp, #48]
        ldp     d11, d10, [sp, #32]
        ldp     d13, d12, [sp, #16]
        ldr     x29, [sp, #64]
        ldp     d15, d14, [sp], #80
        ret

// mlkem_poly_decompress_d11 (0x10c bytes)
L3f74:
        mov     w9, #0xd01
        .inst   0x9000006b  // adrp x11, 0xf000
        .inst   0x9000006c  // adrp x12, 0xf000
        mov     x8, xzr
        add     x10, x1, #0x5
        dup     v1.4h, w9
        ldr     q0, [x11, #1024]
        ldr     q2, [x12, #1040]
        mov     w11, #0x400
L3f98:
        ldurb   w13, [x10, #-4]
        add     x2, x0, x8
        ldurb   w14, [x10, #-3]
        add     x8, x8, #0x10
        ldurb   w12, [x10, #-5]
        cmp     x8, #0x200
        fmov    s3, w13
        ldurb   w16, [x10, #-1]
        lsr     w13, w13, #3
        ldurb   w15, [x10, #-2]
        fmov    s4, w12
        ldrb    w17, [x10]
        mov     v3.h[1], w14
        lsr     w14, w14, #6
        orr     w14, w14, w15, lsl #2
        ldrb    w18, [x10, #1]
        mov     v4.s[1], w13
        lsr     w13, w16, #1
        ldrb    w1, [x10, #2]
        lsr     w15, w17, #4
        mov     v3.h[2], w16
        ldrb    w3, [x10, #3]
        ldrb    w12, [x10, #4]
        lsr     w16, w18, #7
        mov     v4.s[2], w14
        ldrb    w4, [x10, #5]
        lsr     w14, w3, #2
        orr     w16, w16, w1, lsl #1
        mov     v3.h[3], w17
        lsr     w17, w12, #5
        bfi     w15, w18, #4, #7
        bfi     w14, w12, #6, #5
        mov     v4.s[3], w13
        orr     w12, w17, w4, lsl #3
        bfi     w16, w3, #9, #2
        madd    w13, w15, w9, w11
        uxtl    v3.4s, v3.4h
        madd    w14, w14, w9, w11
        madd    w15, w16, w9, w11
        lsr     w13, w13, #11
        ushl    v3.4s, v3.4s, v0.4s
        madd    w12, w12, w9, w11
        lsr     w14, w14, #11
        lsr     w15, w15, #11
        and     v3.16b, v3.16b, v2.16b
        lsr     w12, w12, #11
        orr     v3.16b, v3.16b, v4.16b
        add     x10, x10, #0xb
        xtn     v3.4h, v3.4s
        strh    w13, [x2, #8]
        strh    w14, [x2, #12]
        umull   v3.4s, v3.4h, v1.4h
        strh    w15, [x2, #10]
        strh    w12, [x2, #14]
        rshrn   v3.4h, v3.4s, #11
        str     d3, [x2]
        b.ne    L3f98
        ret

// mlkem_poly_tobytes (0x250 bytes)
L4080:
        add     x8, x1, #0x200
        cmp     x8, x0
        b.ls    L40d4
        add     x8, x0, #0x180
        cmp     x8, x1
        b.ls    L40d4
        mov     x8, xzr
        add     x9, x0, #0x2
L40a0:
        add     x10, x1, x8
        add     x8, x8, #0x4
        cmp     x8, #0x200
        ldrh    w11, [x10, #2]
        ldrh    w10, [x10]
        lsl     w12, w11, #4
        lsr     w11, w11, #4
        orr     w12, w12, w10, lsr #8
        sturb   w10, [x9, #-2]
        sturb   w12, [x9, #-1]
        strb    w11, [x9], #3
        b.ne    L40a0
        ret
L40d4:
        mov     x8, x1
        add     x9, x1, #0x40
        ld2     {v0.8h-v1.8h}, [x8], #32
        ushr    v4.8h, v0.8h, #8
        shl     v5.8h, v1.8h, #4
        orr     v4.16b, v5.16b, v4.16b
        ld2     {v2.8h-v3.8h}, [x8]
        mov     x8, x0
        ushr    v5.8h, v2.8h, #8
        shl     v6.8h, v3.8h, #4
        uzp1    v16.16b, v0.16b, v2.16b
        orr     v5.16b, v6.16b, v5.16b
        uzp1    v17.16b, v4.16b, v5.16b
        shrn    v18.8b, v1.8h, #4
        shrn2   v18.16b, v3.8h, #4
        st3     {v16.16b-v18.16b}, [x8], #48
        ld2     {v0.8h-v1.8h}, [x9]
        add     x9, x1, #0x60
        ld2     {v2.8h-v3.8h}, [x9]
        add     x9, x1, #0x80
        ushr    v17.8h, v0.8h, #8
        shl     v18.8h, v1.8h, #4
        ushr    v7.8h, v2.8h, #8
        shl     v16.8h, v3.8h, #4
        uzp1    v4.16b, v0.16b, v2.16b
        orr     v7.16b, v16.16b, v7.16b
        orr     v16.16b, v18.16b, v17.16b
        uzp1    v5.16b, v16.16b, v7.16b
        shrn    v6.8b, v1.8h, #4
        shrn2   v6.16b, v3.8h, #4
        st3     {v4.16b-v6.16b}, [x8]
        add     x8, x1, #0xa0
        ld2     {v0.8h-v1.8h}, [x9]
        add     x9, x1, #0xc0
        ld2     {v2.8h-v3.8h}, [x8]
        add     x8, x0, #0x60
        ushr    v17.8h, v0.8h, #8
        shl     v18.8h, v1.8h, #4
        ushr    v7.8h, v2.8h, #8
        shl     v16.8h, v3.8h, #4
        uzp1    v4.16b, v0.16b, v2.16b
        orr     v7.16b, v16.16b, v7.16b
        orr     v16.16b, v18.16b, v17.16b
        uzp1    v5.16b, v16.16b, v7.16b
        shrn    v6.8b, v1.8h, #4
        shrn2   v6.16b, v3.8h, #4
        st3     {v4.16b-v6.16b}, [x8]
        add     x8, x1, #0xe0
        ld2     {v0.8h-v1.8h}, [x9]
        add     x9, x1, #0x100
        ld2     {v2.8h-v3.8h}, [x8]
        add     x8, x0, #0x90
        ushr    v17.8h, v0.8h, #8
        shl     v18.8h, v1.8h, #4
        ushr    v7.8h, v2.8h, #8
        shl     v16.8h, v3.8h, #4
        uzp1    v4.16b, v0.16b, v2.16b
        orr     v7.16b, v16.16b, v7.16b
        orr     v16.16b, v18.16b, v17.16b
        uzp1    v5.16b, v16.16b, v7.16b
        shrn    v6.8b, v1.8h, #4
        shrn2   v6.16b, v3.8h, #4
        st3     {v4.16b-v6.16b}, [x8]
        add     x8, x1, #0x120
        ld2     {v0.8h-v1.8h}, [x9]
        add     x9, x1, #0x140
        ld2     {v2.8h-v3.8h}, [x8]
        add     x8, x0, #0xc0
        ushr    v17.8h, v0.8h, #8
        shl     v18.8h, v1.8h, #4
        ushr    v7.8h, v2.8h, #8
        shl     v16.8h, v3.8h, #4
        uzp1    v4.16b, v0.16b, v2.16b
        orr     v7.16b, v16.16b, v7.16b
        orr     v16.16b, v18.16b, v17.16b
        uzp1    v5.16b, v16.16b, v7.16b
        shrn    v6.8b, v1.8h, #4
        shrn2   v6.16b, v3.8h, #4
        st3     {v4.16b-v6.16b}, [x8]
        add     x8, x1, #0x160
        ld2     {v0.8h-v1.8h}, [x9]
        add     x9, x1, #0x180
        ld2     {v2.8h-v3.8h}, [x8]
        add     x8, x0, #0xf0
        ushr    v17.8h, v0.8h, #8
        shl     v18.8h, v1.8h, #4
        ushr    v7.8h, v2.8h, #8
        shl     v16.8h, v3.8h, #4
        uzp1    v4.16b, v0.16b, v2.16b
        orr     v7.16b, v16.16b, v7.16b
        orr     v16.16b, v18.16b, v17.16b
        uzp1    v5.16b, v16.16b, v7.16b
        shrn    v6.8b, v1.8h, #4
        shrn2   v6.16b, v3.8h, #4
        st3     {v4.16b-v6.16b}, [x8]
        add     x8, x1, #0x1a0
        ld2     {v0.8h-v1.8h}, [x9]
        add     x9, x1, #0x1c0
        ld2     {v2.8h-v3.8h}, [x8]
        add     x8, x0, #0x120
        ushr    v17.8h, v0.8h, #8
        shl     v18.8h, v1.8h, #4
        ushr    v7.8h, v2.8h, #8
        shl     v16.8h, v3.8h, #4
        uzp1    v4.16b, v0.16b, v2.16b
        orr     v7.16b, v16.16b, v7.16b
        orr     v16.16b, v18.16b, v17.16b
        uzp1    v5.16b, v16.16b, v7.16b
        shrn    v6.8b, v1.8h, #4
        shrn2   v6.16b, v3.8h, #4
        st3     {v4.16b-v6.16b}, [x8]
        add     x8, x1, #0x1e0
        ld2     {v0.8h-v1.8h}, [x9]
        ld2     {v2.8h-v3.8h}, [x8]
        add     x8, x0, #0x150
        ushr    v17.8h, v0.8h, #8
        shl     v18.8h, v1.8h, #4
        ushr    v7.8h, v2.8h, #8
        shl     v16.8h, v3.8h, #4
        uzp1    v4.16b, v0.16b, v2.16b
        orr     v7.16b, v16.16b, v7.16b
        orr     v16.16b, v18.16b, v17.16b
        uzp1    v5.16b, v16.16b, v7.16b
        shrn    v6.8b, v1.8h, #4
        shrn2   v6.16b, v3.8h, #4
        st3     {v4.16b-v6.16b}, [x8]
        ret

// mlkem_poly_frombytes (0x2f0 bytes)
L42d0:
        add     x8, x1, #0x180
        cmp     x8, x0
        b.ls    L4324
        add     x8, x0, #0x200
        cmp     x8, x1
        b.ls    L4324
        mov     x8, xzr
        add     x9, x1, #0x2
L42f0:
        ldurb   w10, [x9, #-2]
        add     x13, x0, x8
        ldurb   w11, [x9, #-1]
        add     x8, x8, #0x4
        ldrb    w12, [x9], #3
        cmp     x8, #0x200
        bfi     w10, w11, #8, #4
        lsr     w11, w11, #4
        orr     w11, w11, w12, lsl #4
        strh    w10, [x13]
        strh    w11, [x13, #2]
        b.ne    L42f0
        ret
L4324:
        mov     x8, x1
        mov     x9, x0
        add     x10, x1, #0x150
        ld3     {v0.16b-v2.16b}, [x8], #48
        shll    v6.8h, v1.8b, #8
        ushr    v7.16b, v1.16b, #4
        uxtl    v3.8h, v0.8b
        bic     v6.8h, #0xf0, lsl #8
        uxtl    v16.8h, v7.8b
        ushll   v17.8h, v2.8b, #4
        orr     v18.16b, v6.16b, v3.16b
        orr     v19.16b, v17.16b, v16.16b
        shll2   v5.8h, v1.16b, #8
        st2     {v18.8h-v19.8h}, [x9], #32
        uxtl2   v4.8h, v0.16b
        bic     v5.8h, #0xf0, lsl #8
        uxtl2   v3.8h, v7.16b
        ushll2  v0.8h, v2.16b, #4
        orr     v1.16b, v5.16b, v4.16b
        orr     v2.16b, v0.16b, v3.16b
        st2     {v1.8h-v2.8h}, [x9]
        add     x9, x0, #0x60
        ld3     {v0.16b-v2.16b}, [x8]
        add     x8, x0, #0x40
        shll    v4.8h, v1.8b, #8
        ushr    v5.16b, v1.16b, #4
        uxtl    v3.8h, v0.8b
        ushll   v6.8h, v2.8b, #4
        bic     v4.8h, #0xf0, lsl #8
        uxtl    v7.8h, v5.8b
        orr     v3.16b, v4.16b, v3.16b
        orr     v4.16b, v6.16b, v7.16b
        st2     {v3.8h-v4.8h}, [x8]
        add     x8, x1, #0x60
        shll2   v4.8h, v1.16b, #8
        uxtl2   v3.8h, v0.16b
        ushll2  v0.8h, v2.16b, #4
        bic     v4.8h, #0xf0, lsl #8
        uxtl2   v1.8h, v5.16b
        orr     v2.16b, v4.16b, v3.16b
        orr     v3.16b, v0.16b, v1.16b
        st2     {v2.8h-v3.8h}, [x9]
        add     x9, x0, #0xa0
        ld3     {v0.16b-v2.16b}, [x8]
        add     x8, x0, #0x80
        shll    v4.8h, v1.8b, #8
        ushr    v5.16b, v1.16b, #4
        uxtl    v3.8h, v0.8b
        ushll   v6.8h, v2.8b, #4
        bic     v4.8h, #0xf0, lsl #8
        uxtl    v7.8h, v5.8b
        orr     v3.16b, v4.16b, v3.16b
        orr     v4.16b, v6.16b, v7.16b
        st2     {v3.8h-v4.8h}, [x8]
        add     x8, x1, #0x90
        shll2   v4.8h, v1.16b, #8
        uxtl2   v3.8h, v0.16b
        ushll2  v0.8h, v2.16b, #4
        bic     v4.8h, #0xf0, lsl #8
        uxtl2   v1.8h, v5.16b
        orr     v2.16b, v4.16b, v3.16b
        orr     v3.16b, v0.16b, v1.16b
        st2     {v2.8h-v3.8h}, [x9]
        add     x9, x0, #0xe0
        ld3     {v0.16b-v2.16b}, [x8]
        add     x8, x0, #0xc0
        shll    v4.8h, v1.8b, #8
        ushr    v5.16b, v1.16b, #4
        uxtl    v3.8h, v0.8b
        ushll   v6.8h, v2.8b, #4
        bic     v4.8h, #0xf0, lsl #8
        uxtl    v7.8h, v5.8b
        orr     v3.16b, v4.16b, v3.16b
        orr     v4.16b, v6.16b, v7.16b
        st2     {v3.8h-v4.8h}, [x8]
        add     x8, x1, #0xc0
        shll2   v4.8h, v1.16b, #8
        uxtl2   v3.8h, v0.16b
        ushll2  v0.8h, v2.16b, #4
        bic     v4.8h, #0xf0, lsl #8
        uxtl2   v1.8h, v5.16b
        orr     v2.16b, v4.16b, v3.16b
        orr     v3.16b, v0.16b, v1.16b
        st2     {v2.8h-v3.8h}, [x9]
        add     x9, x0, #0x120
        ld3     {v0.16b-v2.16b}, [x8]
        add     x8, x0, #0x100
        shll    v4.8h, v1.8b, #8
        ushr    v5.16b, v1.16b, #4
        uxtl    v3.8h, v0.8b
        ushll   v6.8h, v2.8b, #4
        bic     v4.8h, #0xf0, lsl #8
        uxtl    v7.8h, v5.8b
        orr     v3.16b, v4.16b, v3.16b
        orr     v4.16b, v6.16b, v7.16b
        st2     {v3.8h-v4.8h}, [x8]
        add     x8, x1, #0xf0
        shll2   v4.8h, v1.16b, #8
        uxtl2   v3.8h, v0.16b
        ushll2  v0.8h, v2.16b, #4
        bic     v4.8h, #0xf0, lsl #8
        uxtl2   v1.8h, v5.16b
        orr     v2.16b, v4.16b, v3.16b
        orr     v3.16b, v0.16b, v1.16b
        st2     {v2.8h-v3.8h}, [x9]
        add     x9, x0, #0x160
        ld3     {v0.16b-v2.16b}, [x8]
        add     x8, x0, #0x140
        shll    v4.8h, v1.8b, #8
        ushr    v5.16b, v1.16b, #4
        uxtl    v3.8h, v0.8b
        ushll   v6.8h, v2.8b, #4
        bic     v4.8h, #0xf0, lsl #8
        uxtl    v7.8h, v5.8b
        orr     v3.16b, v4.16b, v3.16b
        orr     v4.16b, v6.16b, v7.16b
        st2     {v3.8h-v4.8h}, [x8]
        add     x8, x1, #0x120
        shll2   v4.8h, v1.16b, #8
        uxtl2   v3.8h, v0.16b
        ushll2  v0.8h, v2.16b, #4
        bic     v4.8h, #0xf0, lsl #8
        uxtl2   v1.8h, v5.16b
        orr     v2.16b, v4.16b, v3.16b
        orr     v3.16b, v0.16b, v1.16b
        st2     {v2.8h-v3.8h}, [x9]
        add     x9, x0, #0x1a0
        ld3     {v0.16b-v2.16b}, [x8]
        add     x8, x0, #0x180
        shll    v6.8h, v1.8b, #8
        ushr    v7.16b, v1.16b, #4
        uxtl    v3.8h, v0.8b
        uxtl2   v4.8h, v0.16b
        shll2   v5.8h, v1.16b, #8
        ushll   v0.8h, v2.8b, #4
        bic     v6.8h, #0xf0, lsl #8
        uxtl    v1.8h, v7.8b
        ushll2  v16.8h, v2.16b, #4
        orr     v2.16b, v6.16b, v3.16b
        orr     v3.16b, v0.16b, v1.16b
        bic     v5.8h, #0xf0, lsl #8
        st2     {v2.8h-v3.8h}, [x8]
        uxtl2   v0.8h, v7.16b
        add     x8, x0, #0x1c0
        orr     v1.16b, v5.16b, v4.16b
        orr     v2.16b, v16.16b, v0.16b
        st2     {v1.8h-v2.8h}, [x9]
        add     x9, x0, #0x1e0
        ld3     {v0.16b-v2.16b}, [x10]
        shll    v6.8h, v1.8b, #8
        ushr    v7.16b, v1.16b, #4
        uxtl    v3.8h, v0.8b
        uxtl2   v4.8h, v0.16b
        shll2   v5.8h, v1.16b, #8
        ushll   v0.8h, v2.8b, #4
        bic     v6.8h, #0xf0, lsl #8
        uxtl    v1.8h, v7.8b
        ushll2  v16.8h, v2.16b, #4
        orr     v2.16b, v6.16b, v3.16b
        orr     v3.16b, v0.16b, v1.16b
        bic     v5.8h, #0xf0, lsl #8
        st2     {v2.8h-v3.8h}, [x8]
        uxtl2   v0.8h, v7.16b
        orr     v1.16b, v5.16b, v4.16b
        orr     v2.16b, v16.16b, v0.16b
        st2     {v1.8h-v2.8h}, [x9]
        ret

// mlkem_poly_frommsg (0xe0 bytes)
L45c0:
        mov     x8, xzr
        add     x9, x0, #0x8
        mov     w10, #0x681
L45cc:
        mov     w11, #0x1
        ldrb    w12, [x1, x8]
        and     w11, w11, w12
        mov     w12, #0x2
        neg     w11, w11
        and     w11, w10, w11, lsr #16
        sturh   w11, [x9, #-8]
        ldrb    w11, [x1, x8]
        and     w11, w12, w11
        mov     w12, #0x4
        neg     w11, w11
        and     w11, w10, w11, lsr #16
        sturh   w11, [x9, #-6]
        ldrb    w11, [x1, x8]
        and     w11, w12, w11
        mov     w12, #0x8
        neg     w11, w11
        and     w11, w10, w11, lsr #16
        sturh   w11, [x9, #-4]
        ldrb    w11, [x1, x8]
        and     w11, w12, w11
        mov     w12, #0x10
        neg     w11, w11
        and     w11, w10, w11, lsr #16
        sturh   w11, [x9, #-2]
        ldrb    w11, [x1, x8]
        and     w11, w12, w11
        mov     w12, #0x20
        neg     w11, w11
        and     w11, w10, w11, lsr #16
        strh    w11, [x9]
        ldrb    w11, [x1, x8]
        and     w11, w12, w11
        mov     w12, #0x40
        neg     w11, w11
        and     w11, w10, w11, lsr #16
        strh    w11, [x9, #2]
        ldrb    w11, [x1, x8]
        and     w11, w12, w11
        mov     w12, #0x80
        neg     w11, w11
        and     w11, w10, w11, lsr #16
        strh    w11, [x9, #4]
        ldrb    w11, [x1, x8]
        add     x8, x8, #0x1
        cmp     x8, #0x20
        and     w11, w12, w11
        neg     w11, w11
        and     w11, w10, w11, lsr #16
        strh    w11, [x9, #6]
        add     x9, x9, #0x10
        b.ne    L45cc
        ret

// mlkem_poly_tomsg (0xa9c bytes)
L46a0:
        sub     sp, sp, #0x110
        stp     d15, d14, [sp, #192]
        stp     d13, d12, [sp, #208]
        stp     d11, d10, [sp, #224]
        stp     d9, d8, [sp, #240]
        str     x29, [sp, #256]
        add     x8, x1, #0x200
        cmp     x8, x0
        b.ls    L479c
        add     x8, x0, #0x20
        cmp     x8, x1
        b.ls    L479c
        mov     w9, #0xafb8
        mov     x8, xzr
        movk    w9, #0x13, lsl #16
        add     x10, x1, #0x8
        mov     w11, #0x40000000
L46e4:
        strb    wzr, [x0, x8]
        ldursh  w12, [x10, #-8]
        madd    w12, w12, w9, w11
        lsr     w13, w12, #31
        strb    w13, [x0, x8]
        ldursh  w13, [x10, #-6]
        madd    w13, w13, w9, w11
        lsr     w13, w13, #30
        and     w13, w13, #0x2
        bfxil   w13, w12, #31, #1
        strb    w13, [x0, x8]
        ldursh  w12, [x10, #-4]
        madd    w12, w12, w9, w11
        lsr     w12, w12, #31
        orr     w12, w13, w12, lsl #2
        strb    w12, [x0, x8]
        ldursh  w13, [x10, #-2]
        madd    w13, w13, w9, w11
        lsr     w13, w13, #31
        orr     w12, w12, w13, lsl #3
        strb    w12, [x0, x8]
        ldrsh   w13, [x10]
        madd    w13, w13, w9, w11
        lsr     w13, w13, #31
        orr     w12, w12, w13, lsl #4
        strb    w12, [x0, x8]
        ldrsh   w13, [x10, #2]
        madd    w13, w13, w9, w11
        lsr     w13, w13, #31
        orr     w12, w12, w13, lsl #5
        strb    w12, [x0, x8]
        ldrsh   w13, [x10, #4]
        madd    w13, w13, w9, w11
        lsr     w13, w13, #31
        orr     w12, w12, w13, lsl #6
        strb    w12, [x0, x8]
        ldrsh   w13, [x10, #6]
        add     x10, x10, #0x10
        madd    w13, w13, w9, w11
        lsr     w13, w13, #31
        orr     w12, w12, w13, lsl #7
        strb    w12, [x0, x8]
        add     x8, x8, #0x1
        cmp     x8, #0x20
        b.ne    L46e4
        b       L5120
L479c:
        movi    v0.2d, #0x0
        mov     w8, #0xafb8
        movk    w8, #0x13, lsl #16
        .inst   0xf0000049  // adrp x9, 0xf000
        movi    v4.4s, #0x40, lsl #24
        movi    v1.4s, #0x40, lsl #24
        str     q0, [x0]
        dup     v22.4s, w8
        ldp     q25, q26, [x1, #32]
        movi    v2.4s, #0x40, lsl #24
        .inst   0xf0000048  // adrp x8, 0xf000
        movi    v6.4s, #0x40, lsl #24
        ldp     q23, q24, [x1]
        zip1    v5.4h, v25.4h, v26.4h
        ext     v20.8b, v25.8b, v5.8b, #4
        ldp     q29, q30, [x1, #128]
        zip1    v17.4h, v23.4h, v24.4h
        mov     v17.s[1], v20.s[1]
        ldp     q7, q8, [x1, #160]
        trn2    v0.4h, v29.4h, v30.4h
        zip1    v31.4h, v29.4h, v30.4h
        sxtl    v17.4s, v17.4h
        mla     v4.4s, v17.4s, v22.4s
        ldp     q27, q28, [x1, #192]
        zip1    v3.4h, v7.4h, v8.4h
        ushr    v4.4s, v4.4s, #31
        mov     v0.s[1], v3.s[1]
        ext     v3.8b, v7.8b, v3.8b, #4
        ldp     q11, q12, [x1, #224]
        trn2    v13.4h, v27.4h, v28.4h
        zip1    v20.4h, v27.4h, v28.4h
        mov     v31.s[1], v3.s[1]
        sxtl    v3.4s, v0.4h
        ldp     q9, q10, [x1, #96]
        zip1    v14.4h, v11.4h, v12.4h
        sxtl    v17.4s, v31.4h
        movi    v31.4s, #0x40, lsl #24
        mla     v1.4s, v17.4s, v22.4s
        mov     v13.s[1], v14.s[1]
        ldp     q18, q19, [x1, #64]
        zip1    v16.4h, v9.4h, v10.4h
        ext     v14.8b, v11.8b, v14.8b, #4
        ushr    v0.4s, v1.4s, #31
        sxtl    v17.4s, v13.4h
        zip2    v13.4h, v25.4h, v26.4h
        movi    v1.16b, #0x2
        ext     v15.8b, v9.8b, v16.8b, #4
        zip1    v21.4h, v18.4h, v19.4h
        mov     v20.s[1], v14.s[1]
        trn2    v14.4h, v23.4h, v24.4h
        mov     v21.s[1], v15.s[1]
        trn2    v15.4h, v18.4h, v19.4h
        sxtl    v20.4s, v20.4h
        mov     v14.s[1], v5.s[1]
        mla     v2.4s, v20.4s, v22.4s
        sxtl    v21.4s, v21.4h
        mov     v15.s[1], v16.s[1]
        mla     v6.4s, v21.4s, v22.4s
        ushr    v2.4s, v2.4s, #31
        movi    v16.4s, #0x40, lsl #24
        movi    v20.4s, #0x40, lsl #24
        movi    v21.4s, #0x40, lsl #24
        ushr    v5.4s, v6.4s, #31
        uzp1    v0.8h, v0.8h, v2.8h
        sxtl    v2.4s, v14.4h
        sxtl    v6.4s, v15.4h
        mla     v16.4s, v3.4s, v22.4s
        mla     v20.4s, v17.4s, v22.4s
        mla     v21.4s, v2.4s, v22.4s
        mla     v31.4s, v6.4s, v22.4s
        uzp1    v2.8h, v4.8h, v5.8h
        ushr    v3.4s, v20.4s, #30
        ushr    v4.4s, v16.4s, #30
        ushr    v6.4s, v21.4s, #30
        ushr    v5.4s, v31.4s, #30
        zip2    v16.4h, v29.4h, v30.4h
        uzp1    v3.8h, v4.8h, v3.8h
        zip2    v17.4h, v27.4h, v28.4h
        uzp1    v4.8h, v6.8h, v5.8h
        uzp1    v0.16b, v2.16b, v0.16b
        mov     v5.16b, v7.16b
        mov     v5.h[3], v8.h[2]
        uzp1    v2.16b, v4.16b, v3.16b
        mov     v3.16b, v11.16b
        mov     v3.h[3], v12.h[2]
        mov     v4.16b, v25.16b
        mov     v4.h[3], v26.h[2]
        zip2    v20.4h, v23.4h, v24.4h
        mov     v16.s[1], v5.s[1]
        zip2    v21.4h, v18.4h, v19.4h
        mov     v17.s[1], v3.s[1]
        mov     v6.16b, v9.16b
        mov     v6.h[3], v10.h[2]
        mov     v20.s[1], v4.s[1]
        sxtl    v3.4s, v16.4h
        sxtl    v4.4s, v17.4h
        movi    v16.4s, #0x40, lsl #24
        movi    v17.4s, #0x40, lsl #24
        mov     v21.s[1], v6.s[1]
        sxtl    v5.4s, v20.4h
        movi    v20.4s, #0x40, lsl #24
        mla     v16.4s, v3.4s, v22.4s
        mla     v17.4s, v4.4s, v22.4s
        sxtl    v6.4s, v21.4h
        movi    v21.4s, #0x40, lsl #24
        mla     v20.4s, v5.4s, v22.4s
        ushr    v3.4s, v17.4s, #29
        ushr    v4.4s, v16.4s, #29
        uzp2    v5.4h, v27.4h, v28.4h
        mla     v21.4s, v6.4s, v22.4s
        uzp2    v16.4h, v23.4h, v24.4h
        uzp1    v3.8h, v4.8h, v3.8h
        uzp2    v4.4h, v29.4h, v30.4h
        ushr    v17.4s, v20.4s, #29
        uzp2    v20.4h, v18.4h, v19.4h
        ushr    v6.4s, v21.4s, #29
        zip2    v21.4h, v7.4h, v8.4h
        zip2    v31.4h, v11.4h, v12.4h
        uzp2    v5.4h, v5.4h, v27.4h
        uzp2    v4.4h, v4.4h, v29.4h
        uzp2    v16.4h, v16.4h, v23.4h
        zip2    v14.4h, v9.4h, v10.4h
        uzp2    v20.4h, v20.4h, v18.4h
        and     v2.16b, v2.16b, v1.16b
        mov     v5.s[1], v31.s[1]
        mov     v4.s[1], v21.s[1]
        mov     v16.s[1], v13.s[1]
        mov     v20.s[1], v14.s[1]
        movi    v21.4s, #0x40, lsl #24
        movi    v31.4s, #0x40, lsl #24
        movi    v13.4s, #0x40, lsl #24
        movi    v14.4s, #0x40, lsl #24
        sxtl    v4.4s, v4.4h
        sxtl    v5.4s, v5.4h
        sxtl    v16.4s, v16.4h
        sxtl    v20.4s, v20.4h
        mla     v21.4s, v4.4s, v22.4s
        mla     v31.4s, v5.4s, v22.4s
        mla     v13.4s, v16.4s, v22.4s
        mla     v14.4s, v20.4s, v22.4s
        uzp1    v4.8h, v17.8h, v6.8h
        ushr    v5.4s, v31.4s, #28
        ushr    v6.4s, v21.4s, #28
        ushr    v17.4s, v13.4s, #28
        ushr    v16.4s, v14.4s, #28
        ldr     q13, [x9, #400]
        uzp1    v5.8h, v6.8h, v5.8h
        .inst   0xf0000049  // adrp x9, 0xf000
        uzp1    v6.8h, v17.8h, v16.8h
        uzp1    v3.16b, v4.16b, v3.16b
        movi    v16.16b, #0x4
        movi    v1.16b, #0x8
        uzp1    v4.16b, v6.16b, v5.16b
        ldr     q6, [x8, #352]
        zip2    v17.8h, v23.8h, v24.8h
        .inst   0xf0000048  // adrp x8, 0xf000
        and     v3.16b, v3.16b, v16.16b
        mov     v20.16b, v6.16b
        str     q6, [sp, #176]
        orr     v2.16b, v2.16b, v3.16b
        tbl     v3.16b, {v7.16b-v8.16b}, v6.16b
        tbl     v5.16b, {v11.16b-v12.16b}, v6.16b
        zip2    v6.8h, v27.8h, v28.8h
        tbl     v16.16b, {v25.16b-v26.16b}, v20.16b
        orr     v0.16b, v2.16b, v0.16b
        and     v2.16b, v4.16b, v1.16b
        zip2    v4.8h, v29.8h, v30.8h
        mov     v6.s[1], v5.s[1]
        mov     v17.s[1], v16.s[1]
        orr     v1.16b, v0.16b, v2.16b
        ldr     q0, [x8, #368]
        mov     v4.s[1], v3.s[1]
        .inst   0xf0000048  // adrp x8, 0xf000
        tbl     v2.16b, {v9.16b-v10.16b}, v20.16b
        zip2    v3.8h, v18.8h, v19.8h
        str     q0, [sp, #128]
        sxtl    v5.4s, v6.4h
        sxtl    v6.4s, v17.4h
        movi    v17.4s, #0x40, lsl #24
        movi    v20.4s, #0x40, lsl #24
        sxtl    v4.4s, v4.4h
        mov     v3.s[1], v2.s[1]
        movi    v2.4s, #0x40, lsl #24
        mla     v17.4s, v4.4s, v22.4s
        mla     v20.4s, v5.4s, v22.4s
        movi    v4.4s, #0x40, lsl #24
        mla     v2.4s, v6.4s, v22.4s
        ushr    v6.4s, v17.4s, #27
        ushr    v5.4s, v20.4s, #27
        zip2    v17.8h, v7.8h, v8.8h
        tbl     v20.16b, {v29.16b-v30.16b}, v0.16b
        sxtl    v3.4s, v3.4h
        zip2    v21.8h, v11.8h, v12.8h
        tbl     v31.16b, {v27.16b-v28.16b}, v0.16b
        mla     v4.4s, v3.4s, v22.4s
        uzp1    v3.8h, v6.8h, v5.8h
        mov     v20.s[1], v17.s[1]
        zip2    v5.8h, v25.8h, v26.8h
        tbl     v6.16b, {v23.16b-v24.16b}, v0.16b
        movi    v14.4s, #0x40, lsl #24
        mov     v31.s[1], v21.s[1]
        zip2    v17.8h, v9.8h, v10.8h
        tbl     v21.16b, {v18.16b-v19.16b}, v0.16b
        ldr     q0, [x8, #384]
        mov     v6.s[1], v5.s[1]
        .inst   0xf0000048  // adrp x8, 0xf000
        sxtl    v5.4s, v20.4h
        sxtl    v20.4s, v31.4h
        str     q0, [sp, #160]
        mla     v14.4s, v5.4s, v22.4s
        movi    v5.4s, #0x40, lsl #24
        mov     v21.s[1], v17.s[1]
        movi    v17.4s, #0x40, lsl #24
        sxtl    v6.4s, v6.4h
        mla     v5.4s, v20.4s, v22.4s
        movi    v20.4s, #0x40, lsl #24
        sxtl    v21.4s, v21.4h
        ushr    v4.4s, v4.4s, #27
        mla     v17.4s, v21.4s, v22.4s
        ushr    v2.4s, v2.4s, #27
        mla     v20.4s, v6.4s, v22.4s
        uzp1    v2.8h, v2.8h, v4.8h
        ushr    v5.4s, v5.4s, #26
        ushr    v4.4s, v17.4s, #26
        ushr    v17.4s, v14.4s, #26
        ushr    v20.4s, v20.4s, #26
        uzp1    v5.8h, v17.8h, v5.8h
        ldr     q17, [x8, #416]
        uzp1    v4.8h, v20.8h, v4.8h
        tbl     v20.16b, {v7.16b-v8.16b}, v0.16b
        tbl     v21.16b, {v29.16b-v30.16b}, v13.16b
        str     q17, [sp, #144]
        tbl     v31.16b, {v11.16b-v12.16b}, v0.16b
        tbl     v14.16b, {v27.16b-v28.16b}, v13.16b
        uzp1    v2.16b, v2.16b, v3.16b
        uzp1    v3.16b, v4.16b, v5.16b
        mov     v21.s[1], v20.s[1]
        tbl     v4.16b, {v25.16b-v26.16b}, v0.16b
        tbl     v5.16b, {v23.16b-v24.16b}, v13.16b
        movi    v15.4s, #0x40, lsl #24
        mov     v14.s[1], v31.s[1]
        tbl     v20.16b, {v9.16b-v10.16b}, v0.16b
        tbl     v31.16b, {v18.16b-v19.16b}, v13.16b
        mov     v5.s[1], v4.s[1]
        sxtl    v4.4s, v21.4h
        movi    v0.4s, #0x40, lsl #24
        mla     v15.4s, v4.4s, v22.4s
        movi    v4.4s, #0x40, lsl #24
        mov     v31.s[1], v20.s[1]
        sxtl    v20.4s, v14.4h
        sxtl    v5.4s, v5.4h
        mla     v4.4s, v20.4s, v22.4s
        ldr     q20, [x9, #432]
        mla     v0.4s, v5.4s, v22.4s
        sxtl    v5.4s, v31.4h
        movi    v31.4s, #0x40, lsl #24
        str     q20, [sp, #112]
        tbl     v25.16b, {v25.16b-v26.16b}, v17.16b
        tbl     v23.16b, {v23.16b-v24.16b}, v20.16b
        tbl     v27.16b, {v27.16b-v28.16b}, v20.16b
        mla     v31.4s, v5.4s, v22.4s
        tbl     v5.16b, {v7.16b-v8.16b}, v17.16b
        tbl     v7.16b, {v29.16b-v30.16b}, v20.16b
        tbl     v29.16b, {v11.16b-v12.16b}, v17.16b
        tbl     v24.16b, {v9.16b-v10.16b}, v17.16b
        tbl     v18.16b, {v18.16b-v19.16b}, v20.16b
        mov     v23.s[1], v25.s[1]
        mov     v7.s[1], v5.s[1]
        mov     v27.s[1], v29.s[1]
        mov     v18.s[1], v24.s[1]
        sxtl    v19.4s, v23.4h
        movi    v23.4s, #0x40, lsl #24
        movi    v24.4s, #0x40, lsl #24
        movi    v25.4s, #0x40, lsl #24
        movi    v26.4s, #0x40, lsl #24
        sxtl    v5.4s, v7.4h
        sxtl    v7.4s, v27.4h
        sxtl    v18.4s, v18.4h
        mla     v23.4s, v5.4s, v22.4s
        mla     v24.4s, v7.4s, v22.4s
        mla     v25.4s, v19.4s, v22.4s
        mla     v26.4s, v18.4s, v22.4s
        ushr    v4.4s, v4.4s, #25
        ushr    v21.4s, v15.4s, #25
        ushr    v30.4s, v31.4s, #25
        ushr    v0.4s, v0.4s, #25
        ushr    v5.4s, v24.4s, #24
        uzp1    v4.8h, v21.8h, v4.8h
        ushr    v7.4s, v23.4s, #24
        uzp1    v0.8h, v0.8h, v30.8h
        ushr    v18.4s, v26.4s, #24
        ushr    v19.4s, v25.4s, #24
        movi    v16.16b, #0x10
        movi    v6.16b, #0x20
        uzp1    v5.8h, v7.8h, v5.8h
        uzp1    v7.8h, v19.8h, v18.8h
        uzp1    v0.16b, v0.16b, v4.16b
        movi    v4.16b, #0x40
        and     v2.16b, v2.16b, v16.16b
        and     v3.16b, v3.16b, v6.16b
        orr     v2.16b, v2.16b, v3.16b
        uzp1    v3.16b, v7.16b, v5.16b
        movi    v5.16b, #0x80
        and     v0.16b, v0.16b, v4.16b
        orr     v0.16b, v2.16b, v0.16b
        orr     v0.16b, v1.16b, v0.16b
        and     v2.16b, v3.16b, v5.16b
        orr     v1.16b, v0.16b, v2.16b
        movi    v0.2d, #0x0
        stp     q1, q0, [x0]
        ldp     q26, q27, [x1, #416]
        ldp     q28, q29, [x1, #480]
        zip1    v16.4h, v26.4h, v27.4h
        ext     v5.8b, v26.8b, v16.8b, #4
        ldp     q24, q25, [x1, #352]
        zip1    v6.4h, v28.4h, v29.4h
        ext     v18.8b, v28.8b, v6.8b, #4
        ldp     q20, q21, [x1, #288]
        zip1    v4.4h, v24.4h, v25.4h
        ext     v2.8b, v24.8b, v4.8b, #4
        ldp     q8, q9, [x1, #448]
        zip1    v3.4h, v20.4h, v21.4h
        ext     v10.8b, v20.8b, v3.8b, #4
        ldp     q14, q15, [x1, #384]
        zip1    v19.4h, v8.4h, v9.4h
        tbl     v23.16b, {v8.16b-v9.16b}, v13.16b
        mov     v19.s[1], v18.s[1]
        ldp     q30, q31, [x1, #320]
        zip1    v7.4h, v14.4h, v15.4h
        zip2    v17.8h, v14.8h, v15.8h
        sxtl    v18.4s, v19.4h
        mov     v7.s[1], v5.s[1]
        ldp     q11, q12, [x1, #256]
        zip1    v0.4h, v30.4h, v31.4h
        movi    v5.4s, #0x40, lsl #24
        sxtl    v7.4s, v7.4h
        mov     v0.s[1], v2.s[1]
        zip1    v1.4h, v11.4h, v12.4h
        movi    v2.4s, #0x40, lsl #24
        mla     v5.4s, v18.4s, v22.4s
        movi    v18.4s, #0x40, lsl #24
        mov     v1.s[1], v10.s[1]
        mla     v2.4s, v7.4s, v22.4s
        movi    v7.4s, #0x40, lsl #24
        sxtl    v0.4s, v0.4h
        sxtl    v1.4s, v1.4h
        mla     v18.4s, v0.4s, v22.4s
        mla     v7.4s, v1.4s, v22.4s
        ushr    v0.4s, v5.4s, #31
        ushr    v1.4s, v2.4s, #31
        trn2    v2.4h, v14.4h, v15.4h
        movi    v10.4s, #0x40, lsl #24
        uzp1    v5.8h, v1.8h, v0.8h
        ushr    v0.4s, v18.4s, #31
        ushr    v1.4s, v7.4s, #31
        zip2    v7.4h, v14.4h, v15.4h
        mov     v2.s[1], v16.s[1]
        zip2    v16.4h, v8.4h, v9.4h
        uzp1    v0.8h, v1.8h, v0.8h
        trn2    v1.4h, v11.4h, v12.4h
        movi    v18.4s, #0x40, lsl #24
        sxtl    v2.4s, v2.4h
        stp     q0, q5, [sp, #80]
        trn2    v0.4h, v8.4h, v9.4h
        trn2    v5.4h, v30.4h, v31.4h
        mov     v1.s[1], v3.s[1]
        movi    v3.4s, #0x40, lsl #24
        mov     v0.s[1], v6.s[1]
        movi    v6.4s, #0x40, lsl #24
        mov     v5.s[1], v4.s[1]
        sxtl    v1.4s, v1.4h
        sxtl    v0.4s, v0.4h
        mla     v6.4s, v2.4s, v22.4s
        movi    v2.4s, #0x40, lsl #24
        mla     v3.4s, v1.4s, v22.4s
        mov     v1.16b, v28.16b
        sxtl    v4.4s, v5.4h
        mla     v2.4s, v0.4s, v22.4s
        mov     v0.16b, v26.16b
        mov     v0.h[3], v27.h[2]
        movi    v5.4s, #0x40, lsl #24
        mov     v1.h[3], v29.h[2]
        ushr    v2.4s, v2.4s, #30
        mov     v7.s[1], v0.s[1]
        ushr    v6.4s, v6.4s, #30
        mov     v0.16b, v20.16b
        mla     v5.4s, v4.4s, v22.4s
        mov     v0.h[3], v21.h[2]
        zip2    v4.4h, v11.4h, v12.4h
        mov     v16.s[1], v1.s[1]
        ushr    v3.4s, v3.4s, #30
        mov     v1.16b, v24.16b
        uzp1    v2.8h, v6.8h, v2.8h
        mov     v1.h[3], v25.h[2]
        zip2    v6.4h, v30.4h, v31.4h
        mov     v4.s[1], v0.s[1]
        ushr    v5.4s, v5.4s, #30
        sxtl    v0.4s, v7.4h
        sxtl    v7.4s, v16.4h
        mov     v6.s[1], v1.s[1]
        movi    v1.4s, #0x40, lsl #24
        sxtl    v4.4s, v4.4h
        mla     v18.4s, v0.4s, v22.4s
        movi    v0.4s, #0x40, lsl #24
        mla     v1.4s, v4.4s, v22.4s
        movi    v4.4s, #0x40, lsl #24
        sxtl    v6.4s, v6.4h
        mla     v0.4s, v7.4s, v22.4s
        uzp1    v3.8h, v3.8h, v5.8h
        mla     v4.4s, v6.4s, v22.4s
        ushr    v5.4s, v18.4s, #29
        ushr    v0.4s, v0.4s, #29
        ushr    v1.4s, v1.4s, #29
        zip2    v6.4h, v20.4h, v21.4h
        zip2    v7.4h, v24.4h, v25.4h
        ushr    v4.4s, v4.4s, #29
        uzp1    v0.8h, v5.8h, v0.8h
        zip2    v5.4h, v28.4h, v29.4h
        uzp1    v1.8h, v1.8h, v4.8h
        uzp1    v4.16b, v3.16b, v2.16b
        uzp2    v2.4h, v14.4h, v15.4h
        uzp2    v3.4h, v8.4h, v9.4h
        uzp1    v0.16b, v1.16b, v0.16b
        uzp2    v1.4h, v30.4h, v31.4h
        uzp2    v2.4h, v2.4h, v14.4h
        uzp2    v3.4h, v3.4h, v8.4h
        stp     q0, q4, [sp, #48]
        uzp2    v0.4h, v11.4h, v12.4h
        zip2    v4.4h, v26.4h, v27.4h
        uzp2    v1.4h, v1.4h, v30.4h
        mov     v3.s[1], v5.s[1]
        uzp2    v0.4h, v0.4h, v11.4h
        mov     v2.s[1], v4.s[1]
        movi    v4.4s, #0x40, lsl #24
        mov     v1.s[1], v7.s[1]
        mov     v0.s[1], v6.s[1]
        sxtl    v2.4s, v2.4h
        movi    v5.4s, #0x40, lsl #24
        mla     v4.4s, v2.4s, v22.4s
        movi    v2.4s, #0x40, lsl #24
        sxtl    v0.4s, v0.4h
        sxtl    v1.4s, v1.4h
        sxtl    v3.4s, v3.4h
        mla     v2.4s, v0.4s, v22.4s
        mla     v10.4s, v1.4s, v22.4s
        ldp     q1, q0, [sp, #112]
        mla     v5.4s, v3.4s, v22.4s
        str     q2, [sp]
        tbl     v7.16b, {v14.16b-v15.16b}, v13.16b
        tbl     v19.16b, {v14.16b-v15.16b}, v1.16b
        zip2    v6.8h, v8.8h, v9.8h
        stp     q5, q4, [sp, #16]
        ldr     q2, [sp, #176]
        tbl     v18.16b, {v14.16b-v15.16b}, v0.16b
        tbl     v16.16b, {v8.16b-v9.16b}, v0.16b
        tbl     v8.16b, {v8.16b-v9.16b}, v1.16b
        zip2    v9.8h, v11.8h, v12.8h
        tbl     v14.16b, {v11.16b-v12.16b}, v0.16b
        tbl     v15.16b, {v11.16b-v12.16b}, v13.16b
        tbl     v11.16b, {v11.16b-v12.16b}, v1.16b
        tbl     v12.16b, {v30.16b-v31.16b}, v0.16b
        tbl     v13.16b, {v30.16b-v31.16b}, v13.16b
        tbl     v3.16b, {v30.16b-v31.16b}, v1.16b
        zip2    v30.8h, v30.8h, v31.8h
        tbl     v31.16b, {v26.16b-v27.16b}, v2.16b
        tbl     v0.16b, {v28.16b-v29.16b}, v2.16b
        tbl     v1.16b, {v20.16b-v21.16b}, v2.16b
        tbl     v2.16b, {v24.16b-v25.16b}, v2.16b
        mov     v17.s[1], v31.s[1]
        mov     v6.s[1], v0.s[1]
        mov     v9.s[1], v1.s[1]
        movi    v31.4s, #0x40, lsl #24
        movi    v1.4s, #0x40, lsl #24
        mov     v30.s[1], v2.s[1]
        sxtl    v2.4s, v17.4h
        sxtl    v6.4s, v6.4h
        ldp     q0, q5, [sp, #144]
        mla     v31.4s, v2.4s, v22.4s
        mla     v1.4s, v6.4s, v22.4s
        movi    v2.4s, #0x40, lsl #24
        movi    v6.4s, #0x40, lsl #24
        sxtl    v17.4s, v9.4h
        sxtl    v30.4s, v30.4h
        mla     v2.4s, v17.4s, v22.4s
        mla     v6.4s, v30.4s, v22.4s
        zip2    v17.8h, v26.8h, v27.8h
        tbl     v30.16b, {v26.16b-v27.16b}, v5.16b
        tbl     v26.16b, {v26.16b-v27.16b}, v0.16b
        zip2    v27.8h, v28.8h, v29.8h
        tbl     v4.16b, {v28.16b-v29.16b}, v5.16b
        tbl     v28.16b, {v28.16b-v29.16b}, v0.16b
        zip2    v29.8h, v20.8h, v21.8h
        tbl     v9.16b, {v20.16b-v21.16b}, v5.16b
        tbl     v20.16b, {v20.16b-v21.16b}, v0.16b
        tbl     v21.16b, {v24.16b-v25.16b}, v5.16b
        tbl     v5.16b, {v24.16b-v25.16b}, v0.16b
        zip2    v24.8h, v24.8h, v25.8h
        mov     v16.s[1], v27.s[1]
        mov     v8.s[1], v28.s[1]
        mov     v18.s[1], v17.s[1]
        mov     v12.s[1], v24.s[1]
        movi    v24.4s, #0x40, lsl #24
        mov     v14.s[1], v29.s[1]
        sxtl    v16.4s, v16.4h
        mov     v11.s[1], v20.s[1]
        movi    v20.4s, #0x40, lsl #24
        movi    v17.4s, #0x40, lsl #24
        mla     v24.4s, v16.4s, v22.4s
        movi    v16.4s, #0x40, lsl #24
        mov     v7.s[1], v30.s[1]
        mov     v19.s[1], v26.s[1]
        mov     v3.s[1], v5.s[1]
        sxtl    v26.4s, v8.4h
        sxtl    v18.4s, v18.4h
        sxtl    v25.4s, v14.4h
        mov     v23.s[1], v4.s[1]
        mov     v13.s[1], v21.s[1]
        movi    v21.4s, #0x40, lsl #24
        mla     v20.4s, v26.4s, v22.4s
        movi    v26.4s, #0x40, lsl #24
        mla     v17.4s, v18.4s, v22.4s
        movi    v18.4s, #0x40, lsl #24
        mla     v16.4s, v25.4s, v22.4s
        mov     v15.s[1], v9.s[1]
        movi    v25.4s, #0x40, lsl #24
        sxtl    v7.4s, v7.4h
        movi    v5.4s, #0x40, lsl #24
        sxtl    v3.4s, v3.4h
        sxtl    v27.4s, v12.4h
        sxtl    v23.4s, v23.4h
        mla     v21.4s, v7.4s, v22.4s
        movi    v7.4s, #0x40, lsl #24
        sxtl    v4.4s, v19.4h
        mla     v26.4s, v3.4s, v22.4s
        ldp     q3, q0, [sp, #80]
        mla     v18.4s, v27.4s, v22.4s
        ushr    v1.4s, v1.4s, #27
        mla     v25.4s, v23.4s, v22.4s
        movi    v23.4s, #0x40, lsl #24
        sxtl    v27.4s, v15.4h
        mla     v5.4s, v4.4s, v22.4s
        movi    v4.4s, #0x40, lsl #24
        sxtl    v29.4s, v13.4h
        mla     v7.4s, v27.4s, v22.4s
        sxtl    v27.4s, v11.4h
        mla     v23.4s, v29.4s, v22.4s
        mla     v4.4s, v27.4s, v22.4s
        movi    v22.16b, #0x2
        uzp1    v3.16b, v3.16b, v0.16b
        ldr     q0, [sp, #64]
        movi    v27.16b, #0x4
        ushr    v6.4s, v6.4s, #27
        and     v22.16b, v0.16b, v22.16b
        ldr     q0, [sp, #48]
        ushr    v2.4s, v2.4s, #27
        ushr    v19.4s, v10.4s, #28
        ushr    v16.4s, v16.4s, #26
        and     v27.16b, v0.16b, v27.16b
        ldr     q0, [sp, #16]
        ushr    v7.4s, v7.4s, #25
        ushr    v5.4s, v5.4s, #24
        ushr    v4.4s, v4.4s, #24
        ushr    v28.4s, v0.4s, #28
        ldr     q0, [sp, #32]
        ushr    v29.4s, v0.4s, #28
        ldr     q0, [sp]
        uzp1    v28.8h, v29.8h, v28.8h
        ushr    v30.4s, v0.4s, #28
        ushr    v0.4s, v31.4s, #27
        uzp1    v19.8h, v30.8h, v19.8h
        uzp1    v0.8h, v0.8h, v1.8h
        uzp1    v1.8h, v2.8h, v6.8h
        ushr    v6.4s, v17.4s, #26
        ushr    v17.4s, v18.4s, #26
        orr     v2.16b, v22.16b, v27.16b
        uzp1    v0.16b, v1.16b, v0.16b
        ushr    v1.4s, v24.4s, #26
        orr     v2.16b, v2.16b, v3.16b
        uzp1    v3.16b, v19.16b, v28.16b
        uzp1    v1.8h, v6.8h, v1.8h
        uzp1    v6.8h, v16.8h, v17.8h
        movi    v16.16b, #0x8
        uzp1    v1.16b, v6.16b, v1.16b
        ushr    v6.4s, v21.4s, #25
        and     v3.16b, v3.16b, v16.16b
        orr     v2.16b, v2.16b, v3.16b
        movi    v3.16b, #0x10
        ushr    v16.4s, v23.4s, #25
        and     v0.16b, v0.16b, v3.16b
        ushr    v3.4s, v25.4s, #25
        uzp1    v3.8h, v6.8h, v3.8h
        uzp1    v6.8h, v7.8h, v16.8h
        ushr    v7.4s, v20.4s, #24
        ushr    v16.4s, v26.4s, #24
        uzp1    v5.8h, v5.8h, v7.8h
        uzp1    v3.16b, v6.16b, v3.16b
        movi    v6.16b, #0x20
        uzp1    v4.8h, v4.8h, v16.8h
        and     v1.16b, v1.16b, v6.16b
        orr     v0.16b, v0.16b, v1.16b
        uzp1    v1.16b, v4.16b, v5.16b
        movi    v4.16b, #0x40
        and     v3.16b, v3.16b, v4.16b
        orr     v0.16b, v0.16b, v3.16b
        orr     v0.16b, v2.16b, v0.16b
        movi    v2.16b, #0x80
        and     v1.16b, v1.16b, v2.16b
        orr     v0.16b, v0.16b, v1.16b
        str     q0, [x0, #16]
L5120:
        ldp     d9, d8, [sp, #240]
        ldp     d11, d10, [sp, #224]
        ldp     d13, d12, [sp, #208]
        ldp     d15, d14, [sp, #192]
        ldr     x29, [sp, #256]
        add     sp, sp, #0x110
        ret

// mlkem_shake128_absorb_once (0x18 bytes)
L513c:
        mov     x8, x1
        mov     x3, x2
        mov     w1, #0xa8
        mov     x2, x8
        mov     w4, #0x1f
        b       L5154

// mlk_keccak_absorb_once (0x128 bytes)
L5154:
        sub     sp, sp, #0x50
        str     x30, [sp, #16]
        stp     x24, x23, [sp, #32]
        stp     x22, x21, [sp, #48]
        stp     x20, x19, [sp, #64]
        .inst   0xd0000148  // adrp x8, 0x2f000
        mov     w21, w4
        movi    v0.2d, #0x0
        mov     x20, x3
        mov     x23, x2
        mov     w22, w1
        ldr     x8, [x8, #4088]
        mov     x19, x0
        mov     w24, w1
        cmp     x24, x3
        ldr     x8, [x8]
        str     x8, [sp, #8]
        strb    w4, [sp, #4]
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        stp     q0, q0, [x0, #64]
        stp     q0, q0, [x0, #96]
        stp     q0, q0, [x0, #128]
        stp     q0, q0, [x0, #160]
        str     xzr, [x0, #192]
        b.hi    L51e8
L51bc:
        mov     x0, x19
        mov     x1, x23
        mov     w2, wzr
        mov     w3, w22
        bl      L5a6c
        mov     x0, x19
        bl      L627c
        sub     x20, x20, x24
        add     x23, x23, x24
        cmp     x20, x24
        b.cs    L51bc
L51e8:
        cbz     x20, L5200
        mov     x0, x19
        mov     x1, x23
        mov     w2, wzr
        mov     w3, w20
        bl      L5a6c
L5200:
        sub     w22, w22, #0x1
        cmp     x20, x22
        b.ne    L5214
        orr     w8, w21, #0x80
        b       L5230
L5214:
        add     x1, sp, #0x4
        mov     x0, x19
        mov     w2, w20
        mov     w3, #0x1
        bl      L5a6c
        mov     w8, #0x80
        mov     w20, w22
L5230:
        add     x1, sp, #0x4
        mov     x0, x19
        mov     w2, w20
        mov     w3, #0x1
        strb    w8, [sp, #4]
        bl      L5a6c
        .inst   0xd0000148  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #8]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L5278
        ldp     x20, x19, [sp, #64]
        ldp     x22, x21, [sp, #48]
        ldp     x24, x23, [sp, #32]
        ldr     x30, [sp, #16]
        add     sp, sp, #0x50
        ret
L5278:
        bl      L0830

// mlkem_shake128_squeezeblocks (0x4c bytes)
L527c:
        cbz     x1, L52c4
        stp     x30, x21, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x2
        mov     x20, x1
        mov     x21, x0
L5294:
        mov     x0, x19
        bl      L627c
        mov     x0, x19
        mov     x1, x21
        mov     w2, wzr
        mov     w3, #0xa8
        bl      L59a0
        add     x21, x21, #0xa8
        subs    x20, x20, #0x1
        b.ne    L5294
        ldp     x20, x19, [sp, #16]
        ldp     x30, x21, [sp], #32
L52c4:
        ret

// mlkem_shake128_init (0x4 bytes)
L52c8:
        ret

// mlkem_shake128_release (0x24 bytes)
L52cc:
        movi    v0.2d, #0x0
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        stp     q0, q0, [x0, #64]
        stp     q0, q0, [x0, #96]
        stp     q0, q0, [x0, #128]
        stp     q0, q0, [x0, #160]
        stp     q0, q0, [x0, #192]
        ret

// mlkem_shake256 (0xd4 bytes)
L52f0:
        stp     x29, x30, [sp, #-64]!
        str     x28, [sp, #16]
        stp     x22, x21, [sp, #32]
        stp     x20, x19, [sp, #48]
        mov     x29, sp
        sub     x9, sp, #0x100
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd0000148  // adrp x8, 0x2f000
        mov     x19, x1
        mov     x20, x0
        mov     x0, sp
        mov     w1, #0x88
        mov     w4, #0x1f
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #248]
        bl      L5154
        cbz     x19, L536c
        mov     w22, #0x88
L533c:
        mov     x0, sp
        bl      L627c
        cmp     x19, #0x88
        mov     x0, sp
        csel    x21, x19, x22, cc
        mov     x1, x20
        mov     w2, wzr
        mov     w3, w21
        bl      L59a0
        add     x20, x20, x21
        subs    x19, x19, x21
        b.ne    L533c
L536c:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        stp     q0, q0, [sp, #64]
        stp     q0, q0, [sp, #96]
        stp     q0, q0, [sp, #128]
        stp     q0, q0, [sp, #160]
        stp     q0, q0, [sp, #192]
        .inst   0xd0000148  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #248]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L53c0
        mov     sp, x29
        ldp     x20, x19, [sp, #48]
        ldp     x22, x21, [sp, #32]
        ldr     x28, [sp, #16]
        ldp     x29, x30, [sp], #64
        ret
L53c0:
        bl      L0830

// mlkem_sha3_256 (0xa4 bytes)
L53c4:
        sub     sp, sp, #0xf0
        str     x30, [sp, #208]
        stp     x20, x19, [sp, #224]
        .inst   0xd0000148  // adrp x8, 0x2f000
        mov     x3, x2
        mov     x2, x1
        mov     x19, x0
        mov     x0, sp
        mov     w1, #0x88
        ldr     x8, [x8, #4088]
        mov     w4, #0x6
        mov     x20, sp
        ldr     x8, [x8]
        str     x8, [sp, #200]
        bl      L5154
        mov     x0, sp
        bl      L627c
        mov     x0, sp
        mov     x1, x19
        mov     w2, wzr
        mov     w3, #0x20
        bl      L59a0
        movi    v0.2d, #0x0
        .inst   0xd0000148  // adrp x8, 0x2f000
        str     xzr, [sp, #192]
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        stp     q0, q0, [sp, #64]
        stp     q0, q0, [sp, #96]
        stp     q0, q0, [sp, #128]
        stp     q0, q0, [sp, #160]
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #200]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L5464
        ldp     x20, x19, [sp, #224]
        ldr     x30, [sp, #208]
        add     sp, sp, #0xf0
        ret
L5464:
        bl      L0830

// mlkem_sha3_512 (0xa4 bytes)
L5468:
        sub     sp, sp, #0xf0
        str     x30, [sp, #208]
        stp     x20, x19, [sp, #224]
        .inst   0xd0000148  // adrp x8, 0x2f000
        mov     x3, x2
        mov     x2, x1
        mov     x19, x0
        mov     x0, sp
        mov     w1, #0x48
        ldr     x8, [x8, #4088]
        mov     w4, #0x6
        mov     x20, sp
        ldr     x8, [x8]
        str     x8, [sp, #200]
        bl      L5154
        mov     x0, sp
        bl      L627c
        mov     x0, sp
        mov     x1, x19
        mov     w2, wzr
        mov     w3, #0x40
        bl      L59a0
        movi    v0.2d, #0x0
        .inst   0xd0000148  // adrp x8, 0x2f000
        str     xzr, [sp, #192]
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        stp     q0, q0, [sp, #64]
        stp     q0, q0, [sp, #96]
        stp     q0, q0, [sp, #128]
        stp     q0, q0, [sp, #160]
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #200]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L5508
        ldp     x20, x19, [sp, #224]
        ldr     x30, [sp, #208]
        add     sp, sp, #0xf0
        ret
L5508:
        bl      L0830

// mlkem_shake128x4_absorb_once (0x64 bytes)
L550c:
        str     x30, [sp, #-64]!
        stp     x24, x23, [sp, #16]
        stp     x22, x21, [sp, #32]
        stp     x20, x19, [sp, #48]
        mov     x22, x2
        mov     x23, x1
        mov     w1, wzr
        mov     w2, #0x320
        mov     x19, x5
        mov     x20, x4
        mov     x21, x3
        mov     x24, x0
        bl      L0840
        mov     x0, x24
        mov     x2, x23
        mov     x3, x22
        mov     x4, x21
        mov     x5, x20
        mov     x6, x19
        ldp     x20, x19, [sp, #48]
        mov     w1, #0xa8
        ldp     x22, x21, [sp, #32]
        ldp     x24, x23, [sp, #16]
        ldr     x30, [sp], #64
        b       L5570

// mlk_keccak_absorb_once_x4 (0x160 bytes)
L5570:
        sub     sp, sp, #0x60
        stp     x30, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        .inst   0xd0000148  // adrp x8, 0x2f000
        mov     x19, x6
        mov     x22, x5
        mov     x23, x4
        mov     w21, w1
        mov     x24, x3
        ldr     x8, [x8, #4088]
        mov     x25, x2
        mov     x20, x0
        mov     w9, #0x1f
        mov     w27, w1
        ldr     x8, [x8]
        cmp     x27, x6
        str     x8, [sp, #8]
        strb    w9, [sp, #4]
        b.hi    L5614
        mov     x26, xzr
L55cc:
        add     x4, x22, x26
        add     x3, x23, x26
        add     x2, x24, x26
        add     x1, x25, x26
        mov     x0, x20
        mov     w5, wzr
        mov     w6, w21
        bl      L5e80
        mov     x0, x20
        bl      L6254
        sub     x19, x19, x27
        add     x26, x26, x27
        cmp     x19, x27
        b.cs    L55cc
        add     x22, x22, x26
        add     x23, x23, x26
        add     x24, x24, x26
        add     x25, x25, x26
L5614:
        cbz     x19, L5638
        mov     x0, x20
        mov     x1, x25
        mov     x2, x24
        mov     x3, x23
        mov     x4, x22
        mov     w5, wzr
        mov     w6, w19
        bl      L5e80
L5638:
        sub     w21, w21, #0x1
        cmp     x19, x21
        b.ne    L564c
        mov     w8, #0x9f
        b       L5674
L564c:
        add     x1, sp, #0x4
        add     x2, sp, #0x4
        add     x3, sp, #0x4
        add     x4, sp, #0x4
        mov     x0, x20
        mov     w5, w19
        mov     w6, #0x1
        bl      L5e80
        mov     w8, #0x80
        mov     w19, w21
L5674:
        add     x1, sp, #0x4
        add     x2, sp, #0x4
        add     x3, sp, #0x4
        add     x4, sp, #0x4
        mov     x0, x20
        mov     w5, w19
        mov     w6, #0x1
        strb    w8, [sp, #4]
        bl      L5e80
        .inst   0xd0000148  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #8]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L56cc
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x30, x27, [sp, #16]
        add     sp, sp, #0x60
        ret
L56cc:
        bl      L0830

// mlkem_shake128x4_squeezeblocks (0x80 bytes)
L56d0:
        cbz     x4, L574c
        str     x30, [sp, #-64]!
        stp     x24, x23, [sp, #16]
        stp     x22, x21, [sp, #32]
        stp     x20, x19, [sp, #48]
        mov     x19, x5
        mov     x20, x4
        mov     x21, x3
        mov     x22, x2
        mov     x23, x1
        mov     x24, x0
L56fc:
        mov     x0, x19
        bl      L6254
        mov     x0, x19
        mov     x1, x24
        mov     x2, x23
        mov     x3, x22
        mov     x4, x21
        mov     w5, wzr
        mov     w6, #0xa8
        bl      L5b64
        subs    x20, x20, #0x1
        add     x21, x21, #0xa8
        add     x22, x22, #0xa8
        add     x23, x23, #0xa8
        add     x24, x24, #0xa8
        b.ne    L56fc
        ldp     x20, x19, [sp, #48]
        ldp     x22, x21, [sp, #32]
        ldp     x24, x23, [sp, #16]
        ldr     x30, [sp], #64
L574c:
        ret

// mlkem_shake128x4_init (0x4 bytes)
L5750:
        ret

// mlkem_shake128x4_release (0x1c bytes)
L5754:
        stp     x30, x19, [sp, #-16]!
        mov     w1, wzr
        mov     w2, #0x320
        mov     x19, x0
        bl      L0840
        ldp     x30, x19, [sp], #16
        ret

// mlkem_shake256x4 (0x230 bytes)
L5770:
        stp     x29, x30, [sp, #-96]!
        stp     x28, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0x5a0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd0000149  // adrp x9, 0x2f000
        str     x2, [sp, #24]
        mov     x8, #0xf0f0f0f0f0f0f0f0
        mov     x22, x1
        movk    x8, #0xf0f1
        mov     x20, x0
        ldr     x9, [x9, #4088]
        add     x0, sp, #0x260
        ldp     x27, x28, [x29, #96]
        mov     w1, wzr
        mov     w2, #0x320
        ldr     x9, [x9]
        umulh   x8, x4, x8
        mov     x24, x7
        mov     x25, x6
        mov     x23, x4
        mov     x26, x5
        mov     x21, x3
        lsr     x19, x8, #7
        str     x9, [sp, #1432]
        bl      L0840
        add     x0, sp, #0x260
        mov     w1, #0x88
        mov     x2, x26
        mov     x3, x25
        mov     x4, x24
        mov     x5, x27
        mov     x6, x28
        bl      L5570
        cmp     x23, #0x88
        b.cc    L5864
        mov     x24, x20
        mov     x25, x22
        ldr     x26, [sp, #24]
        mov     x27, x21
        mov     x28, x19
L5824:
        add     x0, sp, #0x260
        bl      L6254
        add     x0, sp, #0x260
        mov     x1, x24
        mov     x2, x25
        mov     x3, x26
        mov     x4, x27
        mov     w5, wzr
        mov     w6, #0x88
        bl      L5b64
        subs    x28, x28, #0x1
        add     x27, x27, #0x88
        add     x26, x26, #0x88
        add     x25, x25, #0x88
        add     x24, x24, #0x88
        b.ne    L5824
L5864:
        add     x8, x19, x19, lsl #4
        lsl     x24, x8, #3
        subs    x23, x23, x24
        b.eq    L58ec
        add     x0, sp, #0x260
        add     x21, x21, x24
        add     x22, x22, x24
        bl      L6254
        add     x0, sp, #0x260
        add     x1, sp, #0x1d0
        add     x2, sp, #0x140
        add     x3, sp, #0xb0
        add     x4, sp, #0x20
        mov     w5, wzr
        mov     w6, #0x88
        bl      L5b64
        ldr     x8, [sp, #24]
        add     x0, x20, x24
        add     x1, sp, #0x1d0
        mov     x2, x23
        add     x19, x8, x24
        bl      L0810
        add     x1, sp, #0x140
        mov     x0, x22
        mov     x2, x23
        bl      L0810
        add     x1, sp, #0xb0
        mov     x0, x19
        mov     x2, x23
        bl      L0810
        add     x1, sp, #0x20
        mov     x0, x21
        mov     x2, x23
        bl      L0810
L58ec:
        add     x0, sp, #0x260
        mov     w1, wzr
        mov     w2, #0x320
        add     x19, sp, #0x260
        bl      L0840
        movi    v0.2d, #0x0
        str     xzr, [sp, #592]
        add     x8, sp, #0x1d0
        stp     q0, q0, [sp, #464]
        stp     q0, q0, [sp, #496]
        stp     q0, q0, [sp, #528]
        stp     q0, q0, [sp, #560]
        str     xzr, [sp, #448]
        stp     q0, q0, [sp, #352]
        add     x8, sp, #0x140
        stp     q0, q0, [sp, #320]
        stp     q0, q0, [sp, #384]
        stp     q0, q0, [sp, #416]
        str     xzr, [sp, #304]
        stp     q0, q0, [sp, #208]
        add     x8, sp, #0xb0
        stp     q0, q0, [sp, #176]
        stp     q0, q0, [sp, #240]
        stp     q0, q0, [sp, #272]
        str     xzr, [sp, #160]
        stp     q0, q0, [sp, #64]
        add     x8, sp, #0x20
        stp     q0, q0, [sp, #32]
        stp     q0, q0, [sp, #96]
        stp     q0, q0, [sp, #128]
        .inst   0xd0000148  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #1432]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L599c
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L599c:
        bl      L0830

// mlkem_keccakf1600_extract_bytes (0xcc bytes)
L59a0:
        cbz     w3, L59e8
        mov     w9, w2
        mov     w8, w3
        cmp     w3, #0x8
        b.cc    L59c4
        sub     x10, x1, x0
        sub     x10, x10, x9
        cmp     x10, #0x20
        b.cs    L59ec
L59c4:
        mov     x10, xzr
L59c8:
        add     x11, x0, x10
        sub     x8, x8, x10
        add     x9, x11, x9
        add     x11, x1, x10
L59d8:
        ldrb    w10, [x9], #1
        subs    x8, x8, #0x1
        strb    w10, [x11], #1
        b.ne    L59d8
L59e8:
        ret
L59ec:
        cmp     w3, #0x20
        b.cs    L59fc
        mov     x10, xzr
        b       L5a38
L59fc:
        and     x10, x8, #0xffffffe0
        add     x11, x9, x0
        add     x11, x11, #0x10
        add     x12, x1, #0x10
        mov     x13, x10
L5a10:
        ldp     q0, q1, [x11, #-16]
        add     x11, x11, #0x20
        subs    x13, x13, #0x20
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L5a10
        cmp     x10, x8
        b.eq    L59e8
        tst     x8, #0x18
        b.eq    L59c8
L5a38:
        mov     x13, x10
        and     x10, x8, #0xfffffff8
        add     x11, x0, x13
        add     x12, x1, x13
        add     x11, x11, x9
        sub     x13, x13, x10
L5a50:
        ldr     d0, [x11], #8
        adds    x13, x13, #0x8
        str     d0, [x12], #8
        b.ne    L5a50
        cmp     x10, x8
        b.eq    L59e8
        b       L59c8

// mlkem_keccakf1600_xor_bytes (0xf8 bytes)
L5a6c:
        cbz     w3, L5acc
        mov     w8, w2
        mov     w9, w3
        cmp     w3, #0x8
        b.cc    L5aa0
        add     x10, x0, x8
        add     x11, x1, x9
        cmp     x10, x11
        b.cs    L5ad0
        add     x10, x9, x8
        add     x10, x0, x10
        cmp     x10, x1
        b.ls    L5ad0
L5aa0:
        mov     x10, xzr
L5aa4:
        add     x12, x0, x10
        add     x11, x1, x10
        add     x8, x12, x8
        sub     x9, x9, x10
L5ab4:
        ldrb    w10, [x11], #1
        ldrb    w12, [x8]
        subs    x9, x9, #0x1
        eor     w10, w12, w10
        strb    w10, [x8], #1
        b.ne    L5ab4
L5acc:
        ret
L5ad0:
        cmp     w3, #0x20
        b.cs    L5ae0
        mov     x10, xzr
        b       L5b28
L5ae0:
        and     x10, x9, #0xffffffe0
        add     x12, x8, x0
        add     x11, x1, #0x10
        add     x12, x12, #0x10
        mov     x13, x10
L5af4:
        ldp     q0, q1, [x11, #-16]
        add     x11, x11, #0x20
        subs    x13, x13, #0x20
        ldp     q2, q3, [x12, #-16]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v3.16b, v1.16b
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L5af4
        cmp     x10, x9
        b.eq    L5acc
        tst     x9, #0x18
        b.eq    L5aa4
L5b28:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x12, x0, x13
        add     x11, x1, x13
        add     x12, x12, x8
        sub     x13, x13, x10
L5b40:
        ldr     d0, [x11], #8
        ldr     d1, [x12]
        adds    x13, x13, #0x8
        eor     v0.8b, v1.8b, v0.8b
        str     d0, [x12], #8
        b.ne    L5b40
        cmp     x10, x9
        b.eq    L5acc
        b       L5aa4

// mlkem_keccakf1600x4_extract_bytes (0x31c bytes)
L5b64:
        cbz     w6, L5c78
        mov     w8, w5
        mov     w9, w6
        cmp     w6, #0x8
        b.cc    L5b88
        sub     x10, x1, x0
        sub     x10, x10, x8
        cmp     x10, #0x20
        b.cs    L5c7c
L5b88:
        mov     x10, xzr
L5b8c:
        add     x12, x0, x10
        sub     x11, x9, x10
        add     x10, x1, x10
        add     x12, x12, x8
L5b9c:
        ldrb    w13, [x12], #1
        subs    x11, x11, #0x1
        strb    w13, [x10], #1
        b.ne    L5b9c
L5bac:
        cmp     w6, #0x8
        b.cc    L5bc8
        add     x10, x0, x8
        sub     x10, x2, x10
        sub     x10, x10, #0xc8
        cmp     x10, #0x20
        b.cs    L5c8c
L5bc8:
        mov     x10, xzr
L5bcc:
        add     x12, x10, x8
        sub     x11, x9, x10
        add     x12, x12, x0
        add     x10, x2, x10
        add     x12, x12, #0xc8
L5be0:
        ldrb    w13, [x12], #1
        subs    x11, x11, #0x1
        strb    w13, [x10], #1
        b.ne    L5be0
L5bf0:
        cmp     w6, #0x8
        b.cc    L5c0c
        add     x10, x0, x8
        sub     x10, x3, x10
        sub     x10, x10, #0x190
        cmp     x10, #0x20
        b.cs    L5c9c
L5c0c:
        mov     x10, xzr
L5c10:
        add     x12, x10, x8
        sub     x11, x9, x10
        add     x12, x12, x0
        add     x10, x3, x10
        add     x12, x12, #0x190
L5c24:
        ldrb    w13, [x12], #1
        subs    x11, x11, #0x1
        strb    w13, [x10], #1
        b.ne    L5c24
L5c34:
        cmp     w6, #0x8
        b.cc    L5c50
        add     x11, x0, x8
        sub     x10, x4, x11
        sub     x10, x10, #0x258
        cmp     x10, #0x20
        b.cs    L5cac
L5c50:
        mov     x10, xzr
L5c54:
        add     x11, x10, x8
        sub     x8, x9, x10
        add     x11, x11, x0
        add     x9, x4, x10
        add     x10, x11, #0x258
L5c68:
        ldrb    w11, [x10], #1
        subs    x8, x8, #0x1
        strb    w11, [x9], #1
        b.ne    L5c68
L5c78:
        ret
L5c7c:
        cmp     w6, #0x20
        b.cs    L5cbc
        mov     x10, xzr
        b       L5cf8
L5c8c:
        cmp     w6, #0x20
        b.cs    L5d2c
        mov     x10, xzr
        b       L5d68
L5c9c:
        cmp     w6, #0x20
        b.cs    L5da0
        mov     x10, xzr
        b       L5ddc
L5cac:
        cmp     w6, #0x20
        b.cs    L5e14
        mov     x10, xzr
        b       L5e48
L5cbc:
        and     x10, x9, #0xffffffe0
        add     x11, x8, x0
        add     x11, x11, #0x10
        add     x12, x1, #0x10
        mov     x13, x10
L5cd0:
        ldp     q0, q1, [x11, #-16]
        add     x11, x11, #0x20
        subs    x13, x13, #0x20
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L5cd0
        cmp     x10, x9
        b.eq    L5bac
        tst     x9, #0x18
        b.eq    L5b8c
L5cf8:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x11, x0, x13
        add     x12, x1, x13
        add     x11, x11, x8
        sub     x13, x13, x10
L5d10:
        ldr     d0, [x11], #8
        adds    x13, x13, #0x8
        str     d0, [x12], #8
        b.ne    L5d10
        cmp     x10, x9
        b.eq    L5bac
        b       L5b8c
L5d2c:
        and     x10, x9, #0xffffffe0
        add     x11, x8, x0
        add     x11, x11, #0xd8
        add     x12, x2, #0x10
        mov     x13, x10
L5d40:
        ldp     q0, q1, [x11, #-16]
        add     x11, x11, #0x20
        subs    x13, x13, #0x20
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L5d40
        cmp     x10, x9
        b.eq    L5bf0
        tst     x9, #0x18
        b.eq    L5bcc
L5d68:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x11, x13, x8
        add     x12, x2, x13
        add     x11, x11, x0
        sub     x13, x13, x10
        add     x11, x11, #0xc8
L5d84:
        ldr     d0, [x11], #8
        adds    x13, x13, #0x8
        str     d0, [x12], #8
        b.ne    L5d84
        cmp     x10, x9
        b.eq    L5bf0
        b       L5bcc
L5da0:
        and     x10, x9, #0xffffffe0
        add     x11, x8, x0
        add     x11, x11, #0x1a0
        add     x12, x3, #0x10
        mov     x13, x10
L5db4:
        ldp     q0, q1, [x11, #-16]
        add     x11, x11, #0x20
        subs    x13, x13, #0x20
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L5db4
        cmp     x10, x9
        b.eq    L5c34
        tst     x9, #0x18
        b.eq    L5c10
L5ddc:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x11, x13, x8
        add     x12, x3, x13
        add     x11, x11, x0
        sub     x13, x13, x10
        add     x11, x11, #0x190
L5df8:
        ldr     d0, [x11], #8
        adds    x13, x13, #0x8
        str     d0, [x12], #8
        b.ne    L5df8
        cmp     x10, x9
        b.eq    L5c34
        b       L5c10
L5e14:
        and     x10, x9, #0xffffffe0
        add     x11, x11, #0x258
        add     x12, x4, #0x10
        mov     x13, x10
L5e24:
        ldp     q0, q1, [x11], #32
        subs    x13, x13, #0x20
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L5e24
        cmp     x10, x9
        b.eq    L5c78
        tst     x9, #0x18
        b.eq    L5c54
L5e48:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x11, x13, x8
        add     x12, x4, x13
        add     x11, x11, x0
        sub     x13, x13, x10
        add     x11, x11, #0x258
L5e64:
        ldr     d0, [x11], #8
        adds    x13, x13, #0x8
        str     d0, [x12], #8
        b.ne    L5e64
        cmp     x10, x9
        b.eq    L5c78
        b       L5c54

// mlkem_keccakf1600x4_xor_bytes (0x3d4 bytes)
L5e80:
        cbz     w6, L6000
        mov     w8, w5
        mov     w9, w6
        cmp     w6, #0x8
        b.cc    L5eb4
        add     x10, x0, x8
        add     x11, x1, x9
        cmp     x10, x11
        b.cs    L6004
        add     x10, x9, x8
        add     x10, x0, x10
        cmp     x10, x1
        b.ls    L6004
L5eb4:
        mov     x10, xzr
L5eb8:
        add     x12, x0, x10
        sub     x11, x9, x10
        add     x12, x12, x8
        add     x10, x1, x10
L5ec8:
        ldrb    w13, [x10], #1
        ldrb    w14, [x12]
        subs    x11, x11, #0x1
        eor     w13, w14, w13
        strb    w13, [x12], #1
        b.ne    L5ec8
L5ee0:
        cmp     w6, #0x8
        b.cc    L5f10
        add     x10, x0, x8
        add     x11, x2, x9
        add     x10, x10, #0xc8
        cmp     x10, x11
        b.cs    L6014
        add     x10, x9, x8
        add     x10, x10, x0
        add     x10, x10, #0xc8
        cmp     x10, x2
        b.ls    L6014
L5f10:
        mov     x10, xzr
L5f14:
        add     x12, x10, x8
        sub     x11, x9, x10
        add     x12, x12, x0
        add     x10, x2, x10
        add     x12, x12, #0xc8
L5f28:
        ldrb    w13, [x10], #1
        ldrb    w14, [x12]
        subs    x11, x11, #0x1
        eor     w13, w14, w13
        strb    w13, [x12], #1
        b.ne    L5f28
L5f40:
        cmp     w6, #0x8
        b.cc    L5f70
        add     x10, x0, x8
        add     x11, x3, x9
        add     x10, x10, #0x190
        cmp     x10, x11
        b.cs    L6024
        add     x10, x9, x8
        add     x10, x10, x0
        add     x10, x10, #0x190
        cmp     x10, x3
        b.ls    L6024
L5f70:
        mov     x10, xzr
L5f74:
        add     x12, x10, x8
        sub     x11, x9, x10
        add     x12, x12, x0
        add     x10, x3, x10
        add     x12, x12, #0x190
L5f88:
        ldrb    w13, [x10], #1
        ldrb    w14, [x12]
        subs    x11, x11, #0x1
        eor     w13, w14, w13
        strb    w13, [x12], #1
        b.ne    L5f88
L5fa0:
        cmp     w6, #0x8
        b.cc    L5fd0
        add     x10, x0, x8
        add     x11, x10, #0x258
        add     x10, x4, x9
        cmp     x11, x10
        b.cs    L6034
        add     x10, x9, x8
        add     x10, x10, x0
        add     x10, x10, #0x258
        cmp     x10, x4
        b.ls    L6034
L5fd0:
        mov     x10, xzr
L5fd4:
        add     x11, x10, x8
        sub     x8, x9, x10
        add     x9, x11, x0
        add     x10, x4, x10
        add     x9, x9, #0x258
L5fe8:
        ldrb    w11, [x10], #1
        ldrb    w12, [x9]
        subs    x8, x8, #0x1
        eor     w11, w12, w11
        strb    w11, [x9], #1
        b.ne    L5fe8
L6000:
        ret
L6004:
        cmp     w6, #0x20
        b.cs    L6044
        mov     x10, xzr
        b       L608c
L6014:
        cmp     w6, #0x20
        b.cs    L60c8
        mov     x10, xzr
        b       L6110
L6024:
        cmp     w6, #0x20
        b.cs    L6150
        mov     x10, xzr
        b       L6198
L6034:
        cmp     w6, #0x20
        b.cs    L61d8
        mov     x10, xzr
        b       L6214
L6044:
        and     x10, x9, #0xffffffe0
        add     x12, x8, x0
        add     x11, x1, #0x10
        add     x12, x12, #0x10
        mov     x13, x10
L6058:
        ldp     q0, q1, [x11, #-16]
        add     x11, x11, #0x20
        subs    x13, x13, #0x20
        ldp     q2, q3, [x12, #-16]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v3.16b, v1.16b
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L6058
        cmp     x10, x9
        b.eq    L5ee0
        tst     x9, #0x18
        b.eq    L5eb8
L608c:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x12, x0, x13
        add     x11, x1, x13
        add     x12, x12, x8
        sub     x13, x13, x10
L60a4:
        ldr     d0, [x11], #8
        ldr     d1, [x12]
        adds    x13, x13, #0x8
        eor     v0.8b, v1.8b, v0.8b
        str     d0, [x12], #8
        b.ne    L60a4
        cmp     x10, x9
        b.eq    L5ee0
        b       L5eb8
L60c8:
        and     x10, x9, #0xffffffe0
        add     x12, x8, x0
        add     x11, x2, #0x10
        add     x12, x12, #0xd8
        mov     x13, x10
L60dc:
        ldp     q0, q1, [x11, #-16]
        add     x11, x11, #0x20
        subs    x13, x13, #0x20
        ldp     q2, q3, [x12, #-16]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v3.16b, v1.16b
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L60dc
        cmp     x10, x9
        b.eq    L5f40
        tst     x9, #0x18
        b.eq    L5f14
L6110:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x12, x13, x8
        add     x11, x2, x13
        add     x12, x12, x0
        sub     x13, x13, x10
        add     x12, x12, #0xc8
L612c:
        ldr     d0, [x11], #8
        ldr     d1, [x12]
        adds    x13, x13, #0x8
        eor     v0.8b, v1.8b, v0.8b
        str     d0, [x12], #8
        b.ne    L612c
        cmp     x10, x9
        b.eq    L5f40
        b       L5f14
L6150:
        and     x10, x9, #0xffffffe0
        add     x12, x8, x0
        add     x11, x3, #0x10
        add     x12, x12, #0x1a0
        mov     x13, x10
L6164:
        ldp     q0, q1, [x11, #-16]
        add     x11, x11, #0x20
        subs    x13, x13, #0x20
        ldp     q2, q3, [x12, #-16]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v3.16b, v1.16b
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L6164
        cmp     x10, x9
        b.eq    L5fa0
        tst     x9, #0x18
        b.eq    L5f74
L6198:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x12, x13, x8
        add     x11, x3, x13
        add     x12, x12, x0
        sub     x13, x13, x10
        add     x12, x12, #0x190
L61b4:
        ldr     d0, [x11], #8
        ldr     d1, [x12]
        adds    x13, x13, #0x8
        eor     v0.8b, v1.8b, v0.8b
        str     d0, [x12], #8
        b.ne    L61b4
        cmp     x10, x9
        b.eq    L5fa0
        b       L5f74
L61d8:
        and     x10, x9, #0xffffffe0
        add     x12, x4, #0x10
        mov     x13, x10
L61e4:
        ldp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        subs    x13, x13, #0x20
        ldp     q2, q3, [x11]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v3.16b, v1.16b
        stp     q0, q1, [x11], #32
        b.ne    L61e4
        cmp     x10, x9
        b.eq    L6000
        tst     x9, #0x18
        b.eq    L5fd4
L6214:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x12, x13, x8
        add     x11, x4, x13
        add     x12, x12, x0
        sub     x13, x13, x10
        add     x12, x12, #0x258
L6230:
        ldr     d0, [x11], #8
        ldr     d1, [x12]
        adds    x13, x13, #0x8
        eor     v0.8b, v1.8b, v0.8b
        str     d0, [x12], #8
        b.ne    L6230
        cmp     x10, x9
        b.eq    L6000
        b       L5fd4

// mlkem_keccakf1600x4_permute (0x28 bytes)
L6254:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L627c
        add     x0, x19, #0xc8
        bl      L627c
        add     x0, x19, #0x190
        bl      L627c
        add     x0, x19, #0x258
        ldp     x30, x19, [sp], #16
        b       L627c

// mlkem_keccakf1600_permute (0x534 bytes)
L627c:
        sub     sp, sp, #0xd0
        stp     x29, x30, [sp, #112]
        stp     x28, x27, [sp, #128]
        stp     x26, x25, [sp, #144]
        stp     x24, x23, [sp, #160]
        stp     x22, x21, [sp, #176]
        stp     x20, x19, [sp, #192]
        ldp     x10, x27, [x0, #24]
        mov     x14, xzr
        str     x0, [sp, #8]
        ldr     x8, [x0, #56]
        ldr     x9, [x0, #16]
        ldp     x23, x4, [x0]
        stp     x8, x10, [sp, #80]
        ldp     x8, x1, [x0, #64]
        ldp     x22, x24, [x0, #40]
        ldp     x3, x26, [x0, #80]
        stp     x8, x9, [sp, #96]
        ldp     x29, x2, [x0, #96]
        ldp     x28, x17, [x0, #112]
        ldp     x19, x5, [x0, #128]
        ldp     x30, x7, [x0, #144]
        ldp     x21, x6, [x0, #160]
        ldp     x15, x20, [x0, #176]
        ldr     x9, [x0, #192]
L62e0:
        stp     x28, x17, [sp, #56]
        mov     x18, x22
        eor     x10, x22, x23
        eor     x11, x3, x17
        ldp     x17, x22, [sp, #80]
        eor     x10, x10, x11
        eor     x12, x24, x4
        ldr     x8, [sp, #104]
        eor     x0, x29, x5
        eor     x25, x26, x19
        stp     x26, x27, [sp, #40]
        eor     x12, x12, x25
        eor     x25, x2, x30
        eor     x11, x17, x8
        ldr     x8, [sp, #96]
        eor     x11, x11, x0
        eor     x26, x1, x27
        eor     x27, x28, x7
        eor     x10, x10, x21
        eor     x0, x8, x22
        eor     x11, x11, x15
        eor     x0, x0, x25
        eor     x25, x26, x27
        eor     x0, x0, x20
        eor     x13, x25, x9
        eor     x12, x12, x6
        .inst   0xb0000050  // adrp x16, 0xf000
        add     x16, x16, #0x780
        eor     x26, x12, x0, ror #63
        eor     x25, x10, x11, ror #63
        eor     x28, x11, x13, ror #63
        eor     x27, x0, x10, ror #63
        eor     x11, x26, x29
        add     x0, x16, x14, lsl #3
        str     x14, [sp, #72]
        eor     x10, x25, x24
        eor     x30, x28, x30
        eor     x14, x27, x9
        eor     x24, x13, x12, ror #63
        ror     x9, x11, #21
        eor     x23, x24, x23
        ldp     x11, x12, [x0]
        ror     x29, x10, #20
        ror     x10, x30, #43
        ror     x30, x14, #50
        eor     x15, x26, x15
        eor     x7, x27, x7
        eor     x2, x28, x2
        eor     x11, x11, x23
        bic     x13, x9, x29
        bic     x14, x30, x10
        bic     x0, x23, x30
        eor     x13, x11, x13
        eor     x11, x14, x9
        bic     x9, x10, x9
        eor     x14, x28, x22
        eor     x22, x10, x0
        eor     x10, x25, x19
        eor     x19, x9, x29
        eor     x9, x24, x3
        eor     x0, x27, x1
        ror     x14, x14, #36
        ror     x15, x15, #3
        ror     x1, x10, #19
        bic     x10, x29, x23
        ror     x3, x9, #61
        ror     x23, x0, #44
        str     x12, [sp, #16]
        bic     x9, x14, x15
        bic     x0, x15, x1
        eor     x12, x10, x30
        eor     x10, x9, x1
        bic     x29, x1, x3
        eor     x1, x0, x3
        eor     x30, x25, x4
        bic     x0, x3, x23
        eor     x3, x24, x21
        eor     x16, x26, x17
        eor     x0, x0, x14
        eor     x29, x29, x23
        ror     x21, x30, #63
        ror     x7, x7, #56
        ror     x3, x3, #46
        bic     x14, x23, x14
        ror     x23, x2, #39
        ror     x16, x16, #58
        eor     x14, x14, x15
        eor     x5, x26, x5
        bic     x2, x21, x3
        eor     x6, x25, x6
        eor     x2, x2, x7
        bic     x15, x7, x23
        bic     x7, x3, x7
        ror     x4, x5, #49
        eor     x30, x7, x23
        bic     x7, x23, x16
        eor     x23, x24, x18
        ror     x6, x6, #62
        ldp     x9, x18, [sp, #40]
        stp     x10, x11, [sp, #24]
        ror     x23, x23, #28
        eor     x17, x25, x9
        eor     x9, x7, x21
        eor     x7, x27, x18
        eor     x18, x28, x20
        eor     x20, x15, x16
        bic     x16, x16, x21
        ror     x17, x17, #54
        ror     x18, x18, #8
        ror     x15, x7, #37
        eor     x7, x16, x3
        eor     x16, x28, x8
        ldr     x8, [sp, #56]
        bic     x5, x17, x23
        bic     x3, x18, x4
        eor     x5, x5, x15
        eor     x21, x3, x17
        ror     x16, x16, #9
        eor     x3, x27, x8
        ldr     x8, [sp, #104]
        bic     x27, x15, x18
        bic     x15, x23, x15
        bic     x17, x4, x17
        eor     x27, x27, x4
        eor     x26, x26, x8
        ldr     x8, [sp, #64]
        ror     x3, x3, #25
        eor     x18, x15, x18
        eor     x17, x17, x23
        eor     x24, x24, x8
        ror     x25, x26, #2
        bic     x4, x3, x16
        eor     x8, x22, x10
        mov     x10, x12
        ror     x24, x24, #23
        eor     x26, x4, x25
        bic     x15, x24, x3
        bic     x23, x6, x24
        eor     x4, x15, x16
        bic     x15, x25, x6
        bic     x16, x16, x25
        eor     x3, x23, x3
        eor     x28, x15, x24
        eor     x15, x16, x6
        eor     x16, x0, x5
        eor     x6, x9, x26
        eor     x23, x17, x29
        eor     x24, x4, x19
        eor     x16, x16, x6
        eor     x6, x23, x24
        eor     x23, x6, x20
        eor     x6, x3, x1
        eor     x24, x30, x21
        eor     x25, x28, x2
        eor     x6, x6, x24
        eor     x8, x25, x8
        eor     x24, x7, x12
        eor     x25, x18, x15
        eor     x16, x16, x13
        eor     x6, x6, x11
        eor     x24, x24, x25
        eor     x8, x8, x27
        eor     x24, x24, x14
        eor     x25, x16, x6, ror #63
        eor     x16, x8, x16, ror #63
        eor     x8, x23, x8, ror #63
        eor     x6, x6, x24, ror #63
        eor     x29, x25, x29
        eor     x30, x8, x30
        eor     x27, x6, x27
        eor     x15, x16, x15
        eor     x23, x24, x23, ror #63
        ror     x24, x29, #20
        ldr     x11, [sp, #16]
        ror     x29, x30, #21
        ror     x27, x27, #43
        ror     x30, x15, #50
        eor     x13, x23, x13
        eor     x12, x11, x13
        eor     x9, x23, x9
        bic     x15, x29, x24
        eor     x14, x16, x14
        eor     x11, x12, x15
        bic     x12, x30, x27
        eor     x12, x12, x29
        ror     x9, x9, #61
        bic     x29, x27, x29
        ror     x14, x14, #44
        eor     x15, x29, x24
        eor     x10, x16, x10
        str     x12, [sp, #104]
        bic     x12, x13, x30
        eor     x12, x12, x27
        bic     x13, x24, x13
        eor     x27, x13, x30
        ror     x10, x10, #37
        str     x11, [sp, #64]
        ldr     x11, [sp, #24]
        str     x12, [sp, #88]
        eor     x12, x25, x17
        eor     x17, x8, x3
        eor     x3, x6, x22
        bic     x22, x9, x14
        eor     x11, x6, x11
        ror     x12, x12, #19
        ror     x17, x17, #3
        ror     x3, x3, #36
        ror     x11, x11, #9
        bic     x13, x17, x12
        eor     x22, x22, x3
        eor     x13, x13, x9
        bic     x9, x12, x9
        eor     x24, x9, x14
        eor     x9, x25, x19
        bic     x14, x14, x3
        str     x13, [sp, #80]
        bic     x13, x3, x17
        eor     x12, x13, x12
        eor     x13, x23, x26
        ror     x9, x9, #63
        str     x12, [sp, #96]
        eor     x12, x16, x18
        eor     x18, x8, x1
        eor     x1, x6, x2
        ror     x13, x13, #46
        eor     x16, x16, x7
        ror     x12, x12, #56
        ror     x18, x18, #58
        ror     x2, x1, #39
        eor     x1, x14, x17
        bic     x14, x13, x12
        bic     x17, x2, x18
        eor     x29, x14, x2
        bic     x14, x12, x2
        bic     x2, x9, x13
        eor     x3, x17, x9
        eor     x26, x14, x18
        bic     x9, x18, x9
        eor     x14, x8, x21
        eor     x18, x6, x28
        eor     x2, x2, x12
        eor     x12, x25, x20
        eor     x28, x9, x13
        eor     x9, x23, x0
        ror     x13, x14, #49
        ror     x14, x18, #8
        eor     x0, x23, x5
        ror     x12, x12, #54
        ldr     x23, [sp, #64]
        ror     x9, x9, #28
        bic     x5, x10, x14
        bic     x18, x13, x12
        eor     x30, x5, x13
        bic     x13, x14, x13
        eor     x19, x18, x9
        eor     x5, x13, x12
        bic     x12, x12, x9
        eor     x13, x25, x4
        eor     x17, x12, x10
        ldr     x12, [sp, #32]
        bic     x9, x9, x10
        eor     x7, x9, x14
        mov     x4, x15
        ror     x13, x13, #62
        eor     x8, x8, x12
        ror     x12, x16, #25
        ror     x16, x0, #23
        ror     x8, x8, #2
        bic     x9, x12, x11
        bic     x14, x13, x16
        bic     x10, x16, x12
        eor     x15, x14, x12
        ldr     x14, [sp, #72]
        bic     x12, x8, x13
        eor     x21, x9, x8
        bic     x8, x11, x8
        eor     x20, x12, x16
        cmp     x14, #0x16
        add     x14, x14, #0x2
        eor     x6, x10, x11
        eor     x9, x8, x13
        b.cc    L62e0
        ldr     x8, [sp, #8]
        ldr     x11, [sp, #104]
        ldr     x10, [sp, #88]
        stp     x23, x4, [x8]
        stp     x27, x22, [x8, #32]
        stp     x11, x10, [x8, #16]
        ldr     x10, [sp, #80]
        stp     x3, x26, [x8, #80]
        stp     x29, x2, [x8, #96]
        stp     x24, x10, [x8, #48]
        ldr     x10, [sp, #96]
        stp     x28, x17, [x8, #112]
        stp     x19, x5, [x8, #128]
        stp     x30, x7, [x8, #144]
        stp     x21, x6, [x8, #160]
        stp     x15, x20, [x8, #176]
        ldp     x20, x19, [sp, #192]
        stp     x10, x1, [x8, #64]
        ldp     x22, x21, [sp, #176]
        str     x9, [x8, #192]
        ldp     x24, x23, [sp, #160]
        ldp     x26, x25, [sp, #144]
        ldp     x28, x27, [sp, #128]
        ldp     x29, x30, [sp, #112]
        add     sp, sp, #0xd0
        ret

// mlkem512_gen_matrix (0xc8 bytes)
L67b0:
        stp     x29, x30, [sp, #-32]!
        stp     x28, x19, [sp, #16]
        mov     x29, sp
        sub     x9, sp, #0x120
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb0000148  // adrp x8, 0x2f000
        cmp     w2, #0x0
        cset    w9, eq
        add     x2, x0, #0x400
        add     x3, x0, #0x600
        mov     x4, sp
        ldr     x8, [x8, #4088]
        mov     x19, sp
        ldr     x8, [x8]
        str     x8, [sp, #280]
        cset    w8, ne
        ldp     q0, q1, [x1]
        add     x1, x0, #0x200
        strh    wzr, [sp, #32]
        strb    w8, [sp, #97]
        strb    w8, [sp, #160]
        mov     w8, #0x101
        strb    w9, [sp, #96]
        strb    w9, [sp, #161]
        stp     q0, q1, [sp]
        stp     q0, q1, [sp, #64]
        stp     q0, q1, [sp, #128]
        stp     q0, q1, [sp, #192]
        strh    w8, [sp, #224]
        bl      Lc4fc
        movi    v0.2d, #0x0
        .inst   0xb0000148  // adrp x8, 0x2f000
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        stp     q0, q0, [sp, #64]
        stp     q0, q0, [sp, #96]
        stp     q0, q0, [sp, #128]
        stp     q0, q0, [sp, #160]
        stp     q0, q0, [sp, #192]
        stp     q0, q0, [sp, #224]
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #280]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L6874
        mov     sp, x29
        ldp     x28, x19, [sp, #16]
        ldp     x29, x30, [sp], #32
        ret
L6874:
        bl      L0830

// mlkem512_indcpa_keypair_derand (0x2dc bytes)
L6878:
        stp     x29, x30, [sp, #-96]!
        stp     x28, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0x1, lsl #12
        sub     x9, x9, #0x6c0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb0000148  // adrp x8, 0x2f000
        mov     x20, x1
        mov     x19, x0
        add     x24, sp, #0x1, lsl #12
        add     x0, sp, #0x1, lsl #12
        add     x1, sp, #0x1, lsl #12
        ldr     x8, [x8, #4088]
        add     x24, x24, #0x620
        add     x0, x0, #0x660
        add     x1, x1, #0x620
        add     x23, sp, #0x1, lsl #12
        ldr     x8, [x8]
        add     x23, x23, #0x660
        add     x22, x23, #0x20
        str     x8, [sp, #5816]
        mov     w8, #0x2
        ldp     q0, q1, [x2]
        mov     w2, #0x21
        strb    w8, [x24, #32]
        str     q0, [sp, #5664]
        str     q1, [sp, #5680]
        bl      L5468
        mov     w8, #0x1
        add     x26, sp, #0xe20
        add     x21, x26, #0x400
        ldr     q0, [sp, #5728]
        ldr     q1, [sp, #5744]
        mov     w9, #0x100
        add     x1, x26, #0x200
        strh    w8, [sp, #2688]
        mov     w8, #0x101
        add     x3, x26, #0x600
        add     x0, sp, #0xe20
        add     x4, sp, #0xa20
        mov     x2, x21
        str     q0, [sp, #2592]
        str     q1, [sp, #2608]
        add     x27, sp, #0xa20
        str     q0, [sp, #2656]
        str     q1, [sp, #2672]
        str     q0, [sp, #2720]
        str     q1, [sp, #2736]
        str     q1, [sp, #2800]
        str     q0, [sp, #2784]
        strh    w9, [sp, #2752]
        strh    wzr, [sp, #2624]
        strh    w8, [sp, #2816]
        bl      Lc4fc
        movi    v0.2d, #0x0
        add     x28, sp, #0x220
        add     x1, x28, #0x200
        add     x3, x27, #0x200
        mov     w8, #0x3
        add     x0, sp, #0x220
        add     x2, sp, #0xa20
        mov     x4, x22
        str     q0, [sp, #2832]
        mov     w5, wzr
        str     q0, [sp, #2816]
        mov     w6, #0x1
        str     q0, [sp, #2800]
        mov     w7, #0x2
        str     q0, [sp, #2784]
        str     q0, [sp, #2768]
        str     q0, [sp, #2752]
        str     q0, [sp, #2736]
        str     q0, [sp, #2720]
        str     q0, [sp, #2704]
        str     q0, [sp, #2688]
        str     q0, [sp, #2672]
        str     q0, [sp, #2656]
        str     q0, [sp, #2640]
        str     q0, [sp, #2624]
        str     q0, [sp, #2608]
        str     q0, [sp, #2592]
        strb    w8, [sp]
        bl      Lc19c
        add     x0, sp, #0x220
        bl      Lbf3c
        add     x0, sp, #0xa20
        bl      Lbf3c
        add     x0, sp, #0x20
        add     x1, sp, #0x220
        add     x25, sp, #0x20
        bl      Lc11c
        add     x0, sp, #0x620
        add     x1, sp, #0xe20
        add     x2, sp, #0x220
        add     x3, sp, #0x20
        add     x22, sp, #0x620
        bl      Lbf6c
        add     x0, x22, #0x200
        add     x2, sp, #0x220
        add     x3, sp, #0x20
        mov     x1, x21
        bl      Lbf6c
        add     x0, sp, #0x620
        bl      Lc184
        add     x0, sp, #0x620
        add     x1, sp, #0xa20
        bl      Lc15c
        add     x0, sp, #0x620
        bl      Lc144
        add     x0, sp, #0x220
        bl      Lc144
        add     x1, sp, #0x220
        mov     x0, x20
        bl      Lbeec
        add     x1, sp, #0x620
        mov     x0, x19
        bl      Lbeec
        movi    v2.2d, #0x0
        ldr     q0, [sp, #5728]
        ldr     q1, [sp, #5744]
        add     x0, sp, #0x220
        mov     w1, wzr
        mov     w2, #0x400
        stp     q2, q2, [sp, #32]
        stp     q0, q1, [x19, #768]
        stp     q2, q2, [sp, #64]
        stp     q2, q2, [sp, #96]
        stp     q2, q2, [sp, #128]
        stp     q2, q2, [sp, #160]
        stp     q2, q2, [sp, #192]
        stp     q2, q2, [sp, #224]
        stp     q2, q2, [sp, #256]
        stp     q2, q2, [sp, #288]
        stp     q2, q2, [sp, #320]
        stp     q2, q2, [sp, #352]
        stp     q2, q2, [sp, #384]
        stp     q2, q2, [sp, #416]
        stp     q2, q2, [sp, #448]
        stp     q2, q2, [sp, #480]
        stp     q2, q2, [sp, #512]
        bl      L0840
        add     x0, sp, #0x620
        mov     w1, wzr
        mov     w2, #0x400
        bl      L0840
        add     x0, sp, #0xa20
        mov     w1, wzr
        mov     w2, #0x400
        bl      L0840
        add     x0, sp, #0xe20
        mov     w1, wzr
        mov     w2, #0x800
        bl      L0840
        movi    v0.2d, #0x0
        add     x8, sp, #0x1, lsl #12
        strb    wzr, [x24, #32]
        add     x8, x8, #0x620
        str     q0, [sp, #5680]
        str     q0, [sp, #5664]
        .inst   0xb0000148  // adrp x8, 0x2f000
        str     q0, [sp, #5776]
        str     q0, [sp, #5760]
        str     q0, [sp, #5744]
        str     q0, [sp, #5728]
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #5816]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L6b50
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L6b50:
        bl      L0830

// mlkem512_indcpa_enc (0x48c bytes)
L6b54:
        stp     x29, x30, [sp, #-96]!
        stp     x28, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0x2, lsl #12
        sub     x9, x9, #0x60
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb0000148  // adrp x8, 0x2f000
        mov     x19, x0
        add     x0, sp, #0x1, lsl #12
        mov     x22, x1
        add     x0, x0, #0x20
        mov     x1, x2
        ldr     x8, [x8, #4088]
        add     x23, sp, #0x1, lsl #12
        mov     x20, x3
        mov     x21, x2
        add     x23, x23, #0x20
        ldr     x8, [x8]
        str     x8, [sp, #8280]
        bl      Lbf14
        ldp     q0, q1, [x21, #768]
        add     x0, sp, #0x420
        mov     x1, x22
        add     x25, sp, #0x420
        str     q0, [sp, #8224]
        str     q1, [sp, #8240]
        bl      L45c0
        mov     w8, #0x100
        add     x22, sp, #0x1, lsl #12
        add     x22, x22, #0x820
        add     x0, sp, #0x1, lsl #12
        add     x21, x22, #0x400
        add     x4, sp, #0x1, lsl #12
        ldr     q0, [sp, #8224]
        mov     w9, #0x1
        ldr     q1, [sp, #8240]
        add     x1, x22, #0x200
        strh    w8, [sp, #5248]
        mov     w8, #0x101
        add     x3, x22, #0x600
        add     x0, x0, #0x820
        add     x4, x4, #0x420
        mov     x2, x21
        add     x24, sp, #0x1, lsl #12
        str     q0, [sp, #5152]
        str     q1, [sp, #5168]
        add     x24, x24, #0x420
        str     q0, [sp, #5216]
        str     q1, [sp, #5232]
        str     q0, [sp, #5280]
        str     q1, [sp, #5296]
        str     q1, [sp, #5360]
        str     q0, [sp, #5344]
        strh    w9, [sp, #5312]
        strh    wzr, [sp, #5184]
        strh    w8, [sp, #5376]
        bl      Lc4fc
        movi    v0.2d, #0x0
        add     x26, sp, #0xc20
        add     x0, sp, #0x1, lsl #12
        add     x1, x24, #0x200
        add     x3, x26, #0x200
        mov     w8, #0x3
        add     x0, x0, #0x420
        add     x2, sp, #0xc20
        str     q0, [sp, #5392]
        mov     x4, x20
        str     q0, [sp, #5376]
        mov     w5, wzr
        str     q0, [sp, #5360]
        mov     w6, #0x1
        str     q0, [sp, #5344]
        mov     w7, #0x2
        str     q0, [sp, #5328]
        str     q0, [sp, #5312]
        str     q0, [sp, #5296]
        str     q0, [sp, #5280]
        str     q0, [sp, #5264]
        str     q0, [sp, #5248]
        str     q0, [sp, #5232]
        str     q0, [sp, #5216]
        str     q0, [sp, #5200]
        str     q0, [sp, #5184]
        str     q0, [sp, #5168]
        str     q0, [sp, #5152]
        strb    w8, [sp]
        bl      Lc3a4
        add     x0, sp, #0x220
        mov     x1, x20
        mov     w2, #0x4
        add     x27, sp, #0x220
        bl      Lc2f8
        add     x0, sp, #0x1, lsl #12
        add     x0, x0, #0x420
        bl      Lbf3c
        add     x1, sp, #0x1, lsl #12
        add     x0, sp, #0x20
        add     x1, x1, #0x420
        add     x28, sp, #0x20
        bl      Lc11c
        add     x1, sp, #0x1, lsl #12
        add     x2, sp, #0x1, lsl #12
        add     x0, sp, #0x820
        add     x1, x1, #0x820
        add     x2, x2, #0x420
        add     x3, sp, #0x20
        add     x20, sp, #0x820
        bl      Lbf6c
        add     x2, sp, #0x1, lsl #12
        add     x0, x20, #0x200
        add     x2, x2, #0x420
        add     x3, sp, #0x20
        mov     x1, x21
        bl      Lbf6c
        add     x1, sp, #0x1, lsl #12
        add     x2, sp, #0x1, lsl #12
        add     x0, sp, #0x620
        add     x1, x1, #0x20
        add     x2, x2, #0x420
        add     x3, sp, #0x20
        add     x21, sp, #0x620
        bl      Lbf6c
        add     x0, sp, #0x820
        bl      Lbf54
        add     x0, sp, #0x620
        bl      La46c
        add     x0, sp, #0x820
        add     x1, sp, #0xc20
        bl      Lc15c
        add     x0, sp, #0x620
        add     x1, sp, #0x220
        bl      L837c
        add     x0, sp, #0x620
        add     x1, sp, #0x420
        bl      L837c
        add     x0, sp, #0x820
        bl      Lc144
        add     x0, sp, #0x620
        bl      L832c
        add     x1, sp, #0x820
        mov     x0, x19
        bl      Lbe9c
        add     x0, x19, #0x280
        add     x1, sp, #0x620
        bl      L22b0
        movi    v0.2d, #0x0
        add     x0, sp, #0x820
        mov     w1, wzr
        mov     w2, #0x400
        stp     q0, q0, [sp, #32]
        stp     q0, q0, [sp, #64]
        stp     q0, q0, [sp, #96]
        stp     q0, q0, [sp, #128]
        stp     q0, q0, [sp, #160]
        stp     q0, q0, [sp, #192]
        stp     q0, q0, [sp, #224]
        stp     q0, q0, [sp, #256]
        stp     q0, q0, [sp, #288]
        stp     q0, q0, [sp, #320]
        stp     q0, q0, [sp, #352]
        stp     q0, q0, [sp, #384]
        stp     q0, q0, [sp, #416]
        stp     q0, q0, [sp, #448]
        stp     q0, q0, [sp, #480]
        stp     q0, q0, [sp, #512]
        str     q0, [sp, #1040]
        stp     q0, q0, [sp, #560]
        stp     q0, q0, [sp, #592]
        stp     q0, q0, [sp, #624]
        stp     q0, q0, [sp, #656]
        stp     q0, q0, [sp, #688]
        stp     q0, q0, [sp, #720]
        stp     q0, q0, [sp, #752]
        stp     q0, q0, [sp, #784]
        stp     q0, q0, [sp, #816]
        stp     q0, q0, [sp, #848]
        stp     q0, q0, [sp, #880]
        stp     q0, q0, [sp, #912]
        stp     q0, q0, [sp, #944]
        stp     q0, q0, [sp, #976]
        stp     q0, q0, [sp, #1008]
        str     q0, [sp, #544]
        str     q0, [sp, #1552]
        str     q0, [sp, #1536]
        str     q0, [sp, #1520]
        str     q0, [sp, #1504]
        str     q0, [sp, #1488]
        str     q0, [sp, #1472]
        str     q0, [sp, #1456]
        str     q0, [sp, #1440]
        str     q0, [sp, #1424]
        str     q0, [sp, #1408]
        str     q0, [sp, #1392]
        str     q0, [sp, #1376]
        str     q0, [sp, #1360]
        str     q0, [sp, #1344]
        str     q0, [sp, #1328]
        str     q0, [sp, #1312]
        str     q0, [sp, #1296]
        str     q0, [sp, #1280]
        str     q0, [sp, #1264]
        str     q0, [sp, #1248]
        str     q0, [sp, #1232]
        str     q0, [sp, #1216]
        str     q0, [sp, #1200]
        str     q0, [sp, #1184]
        str     q0, [sp, #1168]
        str     q0, [sp, #1152]
        str     q0, [sp, #1136]
        str     q0, [sp, #1120]
        str     q0, [sp, #1104]
        str     q0, [sp, #1088]
        str     q0, [sp, #1072]
        str     q0, [sp, #1056]
        str     q0, [sp, #2064]
        str     q0, [sp, #2048]
        str     q0, [sp, #2032]
        str     q0, [sp, #2016]
        str     q0, [sp, #2000]
        str     q0, [sp, #1984]
        str     q0, [sp, #1968]
        str     q0, [sp, #1952]
        str     q0, [sp, #1936]
        str     q0, [sp, #1920]
        str     q0, [sp, #1904]
        str     q0, [sp, #1888]
        str     q0, [sp, #1872]
        str     q0, [sp, #1856]
        str     q0, [sp, #1840]
        str     q0, [sp, #1824]
        str     q0, [sp, #1808]
        str     q0, [sp, #1792]
        str     q0, [sp, #1776]
        str     q0, [sp, #1760]
        str     q0, [sp, #1744]
        str     q0, [sp, #1728]
        str     q0, [sp, #1712]
        str     q0, [sp, #1696]
        str     q0, [sp, #1680]
        str     q0, [sp, #1664]
        str     q0, [sp, #1648]
        str     q0, [sp, #1632]
        str     q0, [sp, #1616]
        str     q0, [sp, #1600]
        str     q0, [sp, #1584]
        str     q0, [sp, #1568]
        bl      L0840
        add     x0, sp, #0xc20
        mov     w1, wzr
        mov     w2, #0x400
        bl      L0840
        add     x0, sp, #0x1, lsl #12
        add     x0, x0, #0x20
        mov     w1, wzr
        mov     w2, #0x400
        bl      L0840
        add     x0, sp, #0x1, lsl #12
        add     x0, x0, #0x420
        mov     w1, wzr
        mov     w2, #0x400
        bl      L0840
        add     x0, sp, #0x1, lsl #12
        add     x0, x0, #0x820
        mov     w1, wzr
        mov     w2, #0x800
        bl      L0840
        movi    v0.2d, #0x0
        add     x8, sp, #0x2, lsl #12
        add     x8, x8, #0x20
        str     q0, [sp, #8240]
        str     q0, [sp, #8224]
        .inst   0xb0000148  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #8280]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L6fdc
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L6fdc:
        bl      L0830

// mlkem512_indcpa_dec (0x220 bytes)
L6fe0:
        stp     x29, x30, [sp, #-80]!
        str     x28, [sp, #16]
        stp     x24, x23, [sp, #32]
        stp     x22, x21, [sp, #48]
        stp     x20, x19, [sp, #64]
        mov     x29, sp
        sub     x9, sp, #0xe10
        and     sp, x9, #0xffffffffffffffe0
        .inst   0x90000148  // adrp x8, 0x2f000
        mov     x21, x0
        add     x0, sp, #0xa00
        mov     x19, x2
        mov     x20, x1
        add     x22, sp, #0xa00
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #3592]
        bl      Lbec4
        add     x1, x20, #0x280
        add     x0, sp, #0x400
        add     x20, sp, #0x400
        bl      L2db0
        add     x0, sp, #0x600
        mov     x1, x19
        add     x19, sp, #0x600
        bl      Lbf14
        add     x0, sp, #0xa00
        bl      Lbf3c
        mov     x0, sp
        add     x1, sp, #0xa00
        mov     x24, sp
        bl      Lc11c
        add     x0, sp, #0x200
        add     x1, sp, #0x600
        add     x2, sp, #0xa00
        mov     x3, sp
        add     x23, sp, #0x200
        bl      Lbf6c
        add     x0, sp, #0x200
        bl      La46c
        add     x0, sp, #0x400
        add     x1, sp, #0x200
        bl      L84fc
        add     x0, sp, #0x400
        bl      L832c
        add     x1, sp, #0x400
        mov     x0, x21
        bl      L46a0
        movi    v0.2d, #0x0
        add     x0, sp, #0x600
        mov     w1, wzr
        mov     w2, #0x400
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        stp     q0, q0, [sp, #64]
        stp     q0, q0, [sp, #96]
        stp     q0, q0, [sp, #128]
        stp     q0, q0, [sp, #160]
        stp     q0, q0, [sp, #192]
        stp     q0, q0, [sp, #224]
        stp     q0, q0, [sp, #256]
        stp     q0, q0, [sp, #288]
        stp     q0, q0, [sp, #320]
        stp     q0, q0, [sp, #352]
        stp     q0, q0, [sp, #384]
        stp     q0, q0, [sp, #416]
        stp     q0, q0, [sp, #448]
        stp     q0, q0, [sp, #480]
        stp     q0, q0, [sp, #512]
        stp     q0, q0, [sp, #544]
        stp     q0, q0, [sp, #576]
        stp     q0, q0, [sp, #608]
        stp     q0, q0, [sp, #640]
        stp     q0, q0, [sp, #672]
        stp     q0, q0, [sp, #704]
        stp     q0, q0, [sp, #736]
        stp     q0, q0, [sp, #768]
        stp     q0, q0, [sp, #800]
        stp     q0, q0, [sp, #832]
        stp     q0, q0, [sp, #864]
        stp     q0, q0, [sp, #896]
        stp     q0, q0, [sp, #928]
        stp     q0, q0, [sp, #960]
        stp     q0, q0, [sp, #992]
        str     q0, [sp, #1520]
        str     q0, [sp, #1504]
        str     q0, [sp, #1488]
        str     q0, [sp, #1472]
        str     q0, [sp, #1456]
        str     q0, [sp, #1440]
        str     q0, [sp, #1424]
        str     q0, [sp, #1408]
        str     q0, [sp, #1392]
        str     q0, [sp, #1376]
        str     q0, [sp, #1360]
        str     q0, [sp, #1344]
        str     q0, [sp, #1328]
        str     q0, [sp, #1312]
        str     q0, [sp, #1296]
        str     q0, [sp, #1280]
        str     q0, [sp, #1264]
        str     q0, [sp, #1248]
        str     q0, [sp, #1232]
        str     q0, [sp, #1216]
        str     q0, [sp, #1200]
        str     q0, [sp, #1184]
        str     q0, [sp, #1168]
        str     q0, [sp, #1152]
        str     q0, [sp, #1136]
        str     q0, [sp, #1120]
        str     q0, [sp, #1104]
        str     q0, [sp, #1088]
        str     q0, [sp, #1072]
        str     q0, [sp, #1056]
        str     q0, [sp, #1040]
        str     q0, [sp, #1024]
        bl      L0840
        add     x0, sp, #0xa00
        mov     w1, wzr
        mov     w2, #0x400
        bl      L0840
        .inst   0x90000148  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #3592]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L71fc
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #64]
        ldp     x22, x21, [sp, #48]
        ldp     x24, x23, [sp, #32]
        ldr     x28, [sp, #16]
        ldp     x29, x30, [sp], #80
        ret
L71fc:
        bl      L0830

// mlkem512_check_pk (0x41c bytes)
L7200:
        stp     d15, d14, [sp, #-128]!
        stp     d13, d12, [sp, #16]
        stp     d11, d10, [sp, #32]
        stp     d9, d8, [sp, #48]
        stp     x29, x30, [sp, #64]
        str     x28, [sp, #80]
        stp     x22, x21, [sp, #96]
        stp     x20, x19, [sp, #112]
        add     x29, sp, #0x40
        sub     x9, sp, #0x720
        and     sp, x9, #0xffffffffffffffe0
        .inst   0x90000148  // adrp x8, 0x2f000
        mov     x20, x0
        add     x0, sp, #0x300
        mov     x1, x20
        add     x21, sp, #0x300
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #1816]
        bl      Lbf14
        add     x0, sp, #0x300
        bl      Lc144
        mov     x0, sp
        add     x1, sp, #0x300
        mov     x22, sp
        bl      Lbeec
        ldp     q0, q1, [x20]
        mov     w19, wzr
        mov     x0, sp
        mov     w1, w19
        mov     w2, #0x300
        ldp     q2, q3, [sp]
        eor     v2.16b, v2.16b, v0.16b
        ldp     q4, q5, [x20, #32]
        eor     v0.16b, v3.16b, v1.16b
        ldp     q6, q7, [sp, #32]
        eor     v4.16b, v6.16b, v4.16b
        ldp     q16, q17, [x20, #64]
        eor     v1.16b, v7.16b, v5.16b
        orr     v7.16b, v4.16b, v2.16b
        eor     v4.16b, v4.16b, v2.16b
        ldp     q18, q3, [sp, #64]
        eor     v16.16b, v18.16b, v16.16b
        eor     v4.16b, v16.16b, v4.16b
        ldp     q6, q5, [x20, #96]
        eor     v2.16b, v3.16b, v17.16b
        ldp     q19, q20, [sp, #96]
        eor     v6.16b, v19.16b, v6.16b
        orr     v16.16b, v6.16b, v16.16b
        ldp     q18, q17, [x20, #128]
        eor     v3.16b, v20.16b, v5.16b
        orr     v7.16b, v16.16b, v7.16b
        eor     v6.16b, v6.16b, v4.16b
        ldp     q21, q19, [sp, #128]
        eor     v18.16b, v21.16b, v18.16b
        eor     v6.16b, v18.16b, v6.16b
        ldp     q5, q20, [x20, #160]
        eor     v4.16b, v19.16b, v17.16b
        ldp     q16, q22, [sp, #160]
        eor     v16.16b, v16.16b, v5.16b
        orr     v18.16b, v16.16b, v18.16b
        ldp     q21, q17, [x20, #192]
        eor     v5.16b, v22.16b, v20.16b
        eor     v16.16b, v16.16b, v6.16b
        ldp     q19, q23, [sp, #192]
        eor     v19.16b, v19.16b, v21.16b
        orr     v18.16b, v19.16b, v18.16b
        ldp     q20, q22, [x20, #224]
        eor     v6.16b, v23.16b, v17.16b
        orr     v25.16b, v18.16b, v7.16b
        eor     v16.16b, v19.16b, v16.16b
        ldp     q24, q21, [sp, #224]
        eor     v20.16b, v24.16b, v20.16b
        ldp     q17, q23, [x20, #256]
        eor     v7.16b, v21.16b, v22.16b
        eor     v22.16b, v20.16b, v16.16b
        ldp     q18, q19, [sp, #256]
        eor     v17.16b, v18.16b, v17.16b
        orr     v20.16b, v17.16b, v20.16b
        ldp     q24, q21, [x20, #288]
        eor     v16.16b, v19.16b, v23.16b
        eor     v22.16b, v17.16b, v22.16b
        ldp     q26, q18, [sp, #288]
        eor     v24.16b, v26.16b, v24.16b
        orr     v20.16b, v24.16b, v20.16b
        ldp     q19, q23, [x20, #320]
        eor     v17.16b, v18.16b, v21.16b
        eor     v22.16b, v24.16b, v22.16b
        ldp     q27, q26, [sp, #320]
        eor     v19.16b, v27.16b, v19.16b
        orr     v20.16b, v19.16b, v20.16b
        ldp     q21, q28, [x20, #352]
        eor     v18.16b, v26.16b, v23.16b
        orr     v25.16b, v20.16b, v25.16b
        eor     v22.16b, v19.16b, v22.16b
        ldp     q24, q27, [sp, #352]
        eor     v21.16b, v24.16b, v21.16b
        eor     v22.16b, v21.16b, v22.16b
        ldp     q23, q26, [x20, #384]
        eor     v19.16b, v27.16b, v28.16b
        ldp     q20, q29, [sp, #384]
        eor     v23.16b, v20.16b, v23.16b
        eor     v22.16b, v23.16b, v22.16b
        ldp     q24, q27, [x20, #416]
        eor     v20.16b, v29.16b, v26.16b
        orr     v29.16b, v23.16b, v21.16b
        ldp     q28, q30, [sp, #416]
        eor     v24.16b, v28.16b, v24.16b
        orr     v29.16b, v24.16b, v29.16b
        ldp     q26, q31, [x20, #448]
        eor     v21.16b, v30.16b, v27.16b
        eor     v24.16b, v24.16b, v22.16b
        ldp     q23, q28, [sp, #448]
        eor     v23.16b, v23.16b, v26.16b
        orr     v29.16b, v23.16b, v29.16b
        ldp     q27, q30, [x20, #480]
        eor     v22.16b, v28.16b, v31.16b
        eor     v24.16b, v23.16b, v24.16b
        ldp     q8, q26, [sp, #480]
        eor     v27.16b, v8.16b, v27.16b
        orr     v29.16b, v27.16b, v29.16b
        ldp     q28, q31, [x20, #512]
        eor     v23.16b, v26.16b, v30.16b
        orr     v10.16b, v29.16b, v25.16b
        eor     v27.16b, v27.16b, v24.16b
        ldp     q9, q8, [sp, #512]
        eor     v28.16b, v9.16b, v28.16b
        eor     v27.16b, v28.16b, v27.16b
        ldp     q26, q30, [x20, #544]
        eor     v24.16b, v8.16b, v31.16b
        ldp     q25, q29, [sp, #544]
        eor     v26.16b, v25.16b, v26.16b
        orr     v28.16b, v26.16b, v28.16b
        ldp     q9, q31, [x20, #576]
        eor     v25.16b, v29.16b, v30.16b
        eor     v27.16b, v26.16b, v27.16b
        ldp     q8, q11, [sp, #576]
        eor     v8.16b, v8.16b, v9.16b
        orr     v28.16b, v8.16b, v28.16b
        ldp     q29, q30, [x20, #608]
        eor     v26.16b, v11.16b, v31.16b
        eor     v8.16b, v8.16b, v27.16b
        ldp     q12, q9, [sp, #608]
        eor     v29.16b, v12.16b, v29.16b
        ldp     q31, q11, [x20, #640]
        eor     v27.16b, v9.16b, v30.16b
        orr     v9.16b, v29.16b, v28.16b
        eor     v29.16b, v29.16b, v8.16b
        ldp     q13, q12, [sp, #640]
        eor     v31.16b, v13.16b, v31.16b
        orr     v9.16b, v31.16b, v9.16b
        ldp     q30, q14, [x20, #672]
        eor     v28.16b, v12.16b, v11.16b
        eor     v31.16b, v31.16b, v29.16b
        ldp     q8, q13, [sp, #672]
        eor     v30.16b, v8.16b, v30.16b
        orr     v9.16b, v30.16b, v9.16b
        ldp     q11, q12, [x20, #704]
        eor     v29.16b, v13.16b, v14.16b
        orr     v9.16b, v9.16b, v10.16b
        eor     v30.16b, v30.16b, v31.16b
        ldp     q15, q8, [sp, #704]
        eor     v11.16b, v15.16b, v11.16b
        eor     v30.16b, v11.16b, v30.16b
        ldp     q13, q14, [x20, #736]
        eor     v8.16b, v8.16b, v12.16b
        ldp     q10, q15, [sp, #736]
        eor     v10.16b, v10.16b, v13.16b
        orr     v13.16b, v10.16b, v11.16b
        orr     v13.16b, v0.16b, v13.16b
        orr     v13.16b, v13.16b, v1.16b
        orr     v13.16b, v13.16b, v2.16b
        orr     v13.16b, v13.16b, v3.16b
        eor     v0.16b, v0.16b, v1.16b
        orr     v13.16b, v13.16b, v4.16b
        eor     v0.16b, v0.16b, v2.16b
        orr     v9.16b, v13.16b, v9.16b
        orr     v13.16b, v5.16b, v6.16b
        eor     v0.16b, v0.16b, v3.16b
        orr     v13.16b, v13.16b, v7.16b
        eor     v0.16b, v0.16b, v4.16b
        orr     v13.16b, v13.16b, v16.16b
        eor     v0.16b, v0.16b, v5.16b
        orr     v13.16b, v13.16b, v17.16b
        eor     v0.16b, v0.16b, v6.16b
        orr     v13.16b, v13.16b, v18.16b
        eor     v0.16b, v0.16b, v7.16b
        orr     v13.16b, v13.16b, v19.16b
        eor     v0.16b, v0.16b, v16.16b
        orr     v13.16b, v13.16b, v20.16b
        eor     v0.16b, v0.16b, v17.16b
        orr     v9.16b, v9.16b, v13.16b
        orr     v13.16b, v21.16b, v22.16b
        eor     v0.16b, v0.16b, v18.16b
        orr     v13.16b, v13.16b, v23.16b
        eor     v0.16b, v0.16b, v19.16b
        orr     v13.16b, v13.16b, v24.16b
        eor     v0.16b, v0.16b, v20.16b
        orr     v13.16b, v13.16b, v25.16b
        eor     v0.16b, v0.16b, v21.16b
        orr     v13.16b, v13.16b, v26.16b
        eor     v0.16b, v0.16b, v22.16b
        orr     v13.16b, v13.16b, v27.16b
        eor     v0.16b, v0.16b, v23.16b
        orr     v13.16b, v13.16b, v28.16b
        eor     v0.16b, v0.16b, v24.16b
        eor     v12.16b, v15.16b, v14.16b
        orr     v13.16b, v13.16b, v29.16b
        eor     v0.16b, v0.16b, v25.16b
        orr     v9.16b, v9.16b, v13.16b
        orr     v13.16b, v8.16b, v12.16b
        eor     v0.16b, v0.16b, v26.16b
        orr     v9.16b, v9.16b, v13.16b
        eor     v0.16b, v0.16b, v27.16b
        ext     v13.16b, v9.16b, v9.16b, #8
        eor     v0.16b, v0.16b, v28.16b
        eor     v0.16b, v0.16b, v29.16b
        eor     v0.16b, v0.16b, v8.16b
        eor     v30.16b, v10.16b, v30.16b
        eor     v0.16b, v0.16b, v12.16b
        orr     v31.8b, v9.8b, v13.8b
        eor     v0.16b, v0.16b, v30.16b
        fmov    x8, d31
        ext     v1.16b, v0.16b, v0.16b, #8
        orr     x8, x8, x8, lsr #32
        lsr     x9, x8, #16
        eor     v0.8b, v0.8b, v1.8b
        orr     w8, w8, w9
        fmov    x9, d0
        orr     w8, w8, w8, lsr #8
        sub     w8, w19, w8, uxtb
        eor     x9, x9, x9, lsr #32
        eor     x9, x9, x9, lsr #16
        lsr     x10, x9, #8
        eor     w9, w9, w10
        eor     w8, w9, w8, lsr #16
        and     w8, w8, #0xff
        cmp     w8, w9, uxtb
        mov     w8, #0xfffffffc
        csel    w20, w19, w8, eq
        bl      L0840
        add     x0, sp, #0x300
        mov     w1, w19
        mov     w2, #0x400
        bl      L0840
        .inst   0x90000148  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #1816]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L7618
        mov     w0, w20
        sub     sp, x29, #0x40
        ldp     x20, x19, [sp, #112]
        ldp     x22, x21, [sp, #96]
        ldp     x29, x30, [sp, #64]
        ldp     d9, d8, [sp, #48]
        ldp     d11, d10, [sp, #32]
        ldp     d13, d12, [sp, #16]
        ldr     x28, [sp, #80]
        ldp     d15, d14, [sp], #128
        ret
L7618:
        bl      L0830

// mlkem512_check_sk (0xe0 bytes)
L761c:
        stp     x29, x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x29, sp
        sub     x9, sp, #0x40
        and     sp, x9, #0xffffffffffffffe0
        .inst   0x90000148  // adrp x8, 0x2f000
        mov     x19, x0
        add     x1, x0, #0x300
        mov     x0, sp
        mov     w2, #0x320
        mov     x20, sp
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #56]
        bl      L53c4
        ldp     q1, q2, [sp]
        mov     w8, wzr
        ldr     q0, [x19, #1584]
        ldr     q3, [x19, #1568]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v1.16b, v3.16b
        orr     v2.16b, v1.16b, v0.16b
        ext     v3.16b, v2.16b, v2.16b, #8
        eor     v0.16b, v1.16b, v0.16b
        ext     v1.16b, v0.16b, v0.16b, #8
        orr     v2.8b, v2.8b, v3.8b
        fmov    x9, d2
        eor     v0.8b, v0.8b, v1.8b
        fmov    x11, d0
        orr     x9, x9, x9, lsr #32
        lsr     x10, x9, #16
        orr     w9, w9, w10
        eor     x10, x11, x11, lsr #32
        movi    v0.2d, #0x0
        orr     w9, w9, w9, lsr #8
        eor     x10, x10, x10, lsr #16
        sub     w9, w8, w9, uxtb
        lsr     x11, x10, #8
        eor     w10, w10, w11
        eor     w9, w10, w9, lsr #16
        .inst   0x9000014b  // adrp x11, 0x2f000
        stp     q0, q0, [sp]
        and     w9, w9, #0xff
        ldr     x11, [x11, #4088]
        cmp     w9, w10, uxtb
        ldr     x12, [sp, #56]
        mov     w9, #0xfffffffb
        csel    w0, w8, w9, eq
        ldr     x11, [x11]
        cmp     x11, x12
        b.ne    L76f8
        mov     sp, x29
        ldp     x20, x19, [sp, #16]
        ldp     x29, x30, [sp], #32
        ret
L76f8:
        bl      L0830

// mlkem512_keypair_derand (0x98 bytes)
L76fc:
        str     x30, [sp, #-48]!
        stp     x22, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x22, x2
        mov     x19, x1
        mov     x21, x0
        bl      L6878
        mov     w20, w0
        cbz     w0, L7754
        mov     x0, x21
        mov     w1, wzr
        mov     w2, #0x320
        bl      L0840
        mov     x0, x19
        mov     w1, wzr
        mov     w2, #0x660
        bl      L0840
        mov     w0, w20
        ldp     x20, x19, [sp, #32]
        ldp     x22, x21, [sp, #16]
        ldr     x30, [sp], #48
        ret
L7754:
        add     x0, x19, #0x300
        mov     x1, x21
        mov     w2, #0x320
        bl      L0810
        add     x0, x19, #0x620
        mov     x1, x21
        mov     w2, #0x320
        bl      L53c4
        ldp     q1, q0, [x22, #32]
        str     q1, [x19, #1600]
        str     q0, [x19, #1616]
        mov     w0, w20
        ldp     x20, x19, [sp, #32]
        ldp     x22, x21, [sp, #16]
        ldr     x30, [sp], #48
        ret

// mlkem512_keypair (0xf4 bytes)
L7794:
        stp     x29, x30, [sp, #-48]!
        str     x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0x50
        and     sp, x9, #0xffffffffffffffe0
        .inst   0x90000148  // adrp x8, 0x2f000
        mov     x19, x1
        mov     x21, x0
        mov     x0, sp
        mov     w1, #0x40
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #72]
        bl      L0820
        cbz     w0, L77dc
        mov     w20, #0xfffffffd
        b       L7844
L77dc:
        mov     x2, sp
        mov     x0, x21
        mov     x1, x19
        bl      L6878
        mov     w20, w0
        cbz     w0, L7818
        mov     x0, x21
        mov     w1, wzr
        mov     w2, #0x320
        bl      L0840
        mov     x0, x19
        mov     w1, wzr
        mov     w2, #0x660
        bl      L0840
        b       L7844
L7818:
        add     x0, x19, #0x300
        mov     x1, x21
        mov     w2, #0x320
        bl      L0810
        add     x0, x19, #0x620
        mov     x1, x21
        mov     w2, #0x320
        bl      L53c4
        ldp     q0, q1, [sp, #32]
        str     q0, [x19, #1600]
        str     q1, [x19, #1616]
L7844:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        .inst   0x90000148  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #72]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L7884
        mov     w0, w20
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldr     x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L7884:
        bl      L0830

// mlkem512_enc_derand (0x49c bytes)
L7888:
        stp     d15, d14, [sp, #-160]!
        stp     d13, d12, [sp, #16]
        stp     d11, d10, [sp, #32]
        stp     d9, d8, [sp, #48]
        stp     x29, x30, [sp, #64]
        stp     x28, x27, [sp, #80]
        stp     x26, x25, [sp, #96]
        stp     x24, x23, [sp, #112]
        stp     x22, x21, [sp, #128]
        stp     x20, x19, [sp, #144]
        add     x29, sp, #0x40
        sub     x9, sp, #0x720
        and     sp, x9, #0xffffffffffffffe0
        .inst   0x90000148  // adrp x8, 0x2f000
        mov     x19, x1
        mov     x21, x0
        add     x0, sp, #0x300
        mov     x1, x2
        mov     x22, x3
        ldr     x8, [x8, #4088]
        mov     x20, x2
        add     x25, sp, #0x300
        ldr     x8, [x8]
        str     x8, [sp, #1816]
        bl      Lbf14
        add     x0, sp, #0x300
        bl      Lc144
        mov     x0, sp
        add     x1, sp, #0x300
        mov     x24, sp
        bl      Lbeec
        ldp     q0, q1, [x20]
        mov     w23, wzr
        mov     x0, sp
        mov     w1, wzr
        mov     w2, #0x300
        ldp     q2, q3, [sp]
        eor     v2.16b, v2.16b, v0.16b
        ldp     q4, q5, [x20, #32]
        eor     v0.16b, v3.16b, v1.16b
        ldp     q6, q7, [sp, #32]
        eor     v4.16b, v6.16b, v4.16b
        ldp     q16, q17, [x20, #64]
        eor     v1.16b, v7.16b, v5.16b
        orr     v7.16b, v4.16b, v2.16b
        eor     v4.16b, v4.16b, v2.16b
        ldp     q18, q3, [sp, #64]
        eor     v16.16b, v18.16b, v16.16b
        eor     v4.16b, v16.16b, v4.16b
        ldp     q6, q5, [x20, #96]
        eor     v2.16b, v3.16b, v17.16b
        ldp     q19, q20, [sp, #96]
        eor     v6.16b, v19.16b, v6.16b
        orr     v16.16b, v6.16b, v16.16b
        ldp     q18, q17, [x20, #128]
        eor     v3.16b, v20.16b, v5.16b
        orr     v7.16b, v16.16b, v7.16b
        eor     v6.16b, v6.16b, v4.16b
        ldp     q21, q19, [sp, #128]
        eor     v18.16b, v21.16b, v18.16b
        eor     v6.16b, v18.16b, v6.16b
        ldp     q5, q20, [x20, #160]
        eor     v4.16b, v19.16b, v17.16b
        ldp     q16, q22, [sp, #160]
        eor     v16.16b, v16.16b, v5.16b
        orr     v18.16b, v16.16b, v18.16b
        ldp     q21, q17, [x20, #192]
        eor     v5.16b, v22.16b, v20.16b
        eor     v16.16b, v16.16b, v6.16b
        ldp     q19, q23, [sp, #192]
        eor     v19.16b, v19.16b, v21.16b
        orr     v18.16b, v19.16b, v18.16b
        ldp     q20, q22, [x20, #224]
        eor     v6.16b, v23.16b, v17.16b
        orr     v25.16b, v18.16b, v7.16b
        eor     v16.16b, v19.16b, v16.16b
        ldp     q24, q21, [sp, #224]
        eor     v20.16b, v24.16b, v20.16b
        ldp     q17, q23, [x20, #256]
        eor     v7.16b, v21.16b, v22.16b
        eor     v22.16b, v20.16b, v16.16b
        ldp     q18, q19, [sp, #256]
        eor     v17.16b, v18.16b, v17.16b
        orr     v20.16b, v17.16b, v20.16b
        ldp     q24, q21, [x20, #288]
        eor     v16.16b, v19.16b, v23.16b
        eor     v22.16b, v17.16b, v22.16b
        ldp     q26, q18, [sp, #288]
        eor     v24.16b, v26.16b, v24.16b
        orr     v20.16b, v24.16b, v20.16b
        ldp     q19, q23, [x20, #320]
        eor     v17.16b, v18.16b, v21.16b
        eor     v22.16b, v24.16b, v22.16b
        ldp     q27, q26, [sp, #320]
        eor     v19.16b, v27.16b, v19.16b
        orr     v20.16b, v19.16b, v20.16b
        ldp     q21, q28, [x20, #352]
        eor     v18.16b, v26.16b, v23.16b
        orr     v25.16b, v20.16b, v25.16b
        eor     v22.16b, v19.16b, v22.16b
        ldp     q24, q27, [sp, #352]
        eor     v21.16b, v24.16b, v21.16b
        eor     v22.16b, v21.16b, v22.16b
        ldp     q23, q26, [x20, #384]
        eor     v19.16b, v27.16b, v28.16b
        ldp     q20, q29, [sp, #384]
        eor     v23.16b, v20.16b, v23.16b
        eor     v22.16b, v23.16b, v22.16b
        ldp     q24, q27, [x20, #416]
        eor     v20.16b, v29.16b, v26.16b
        orr     v29.16b, v23.16b, v21.16b
        ldp     q28, q30, [sp, #416]
        eor     v24.16b, v28.16b, v24.16b
        orr     v29.16b, v24.16b, v29.16b
        ldp     q26, q31, [x20, #448]
        eor     v21.16b, v30.16b, v27.16b
        eor     v24.16b, v24.16b, v22.16b
        ldp     q23, q28, [sp, #448]
        eor     v23.16b, v23.16b, v26.16b
        orr     v29.16b, v23.16b, v29.16b
        ldp     q27, q30, [x20, #480]
        eor     v22.16b, v28.16b, v31.16b
        eor     v24.16b, v23.16b, v24.16b
        ldp     q8, q26, [sp, #480]
        eor     v27.16b, v8.16b, v27.16b
        orr     v29.16b, v27.16b, v29.16b
        ldp     q28, q31, [x20, #512]
        eor     v23.16b, v26.16b, v30.16b
        orr     v10.16b, v29.16b, v25.16b
        eor     v27.16b, v27.16b, v24.16b
        ldp     q9, q8, [sp, #512]
        eor     v28.16b, v9.16b, v28.16b
        eor     v27.16b, v28.16b, v27.16b
        ldp     q26, q30, [x20, #544]
        eor     v24.16b, v8.16b, v31.16b
        ldp     q25, q29, [sp, #544]
        eor     v26.16b, v25.16b, v26.16b
        orr     v28.16b, v26.16b, v28.16b
        ldp     q9, q31, [x20, #576]
        eor     v25.16b, v29.16b, v30.16b
        eor     v27.16b, v26.16b, v27.16b
        ldp     q8, q11, [sp, #576]
        eor     v8.16b, v8.16b, v9.16b
        orr     v28.16b, v8.16b, v28.16b
        ldp     q29, q30, [x20, #608]
        eor     v26.16b, v11.16b, v31.16b
        eor     v8.16b, v8.16b, v27.16b
        ldp     q12, q9, [sp, #608]
        eor     v29.16b, v12.16b, v29.16b
        ldp     q31, q11, [x20, #640]
        eor     v27.16b, v9.16b, v30.16b
        orr     v9.16b, v29.16b, v28.16b
        eor     v29.16b, v29.16b, v8.16b
        ldp     q13, q12, [sp, #640]
        eor     v31.16b, v13.16b, v31.16b
        orr     v9.16b, v31.16b, v9.16b
        ldp     q30, q14, [x20, #672]
        eor     v28.16b, v12.16b, v11.16b
        eor     v31.16b, v31.16b, v29.16b
        ldp     q8, q13, [sp, #672]
        eor     v30.16b, v8.16b, v30.16b
        orr     v9.16b, v30.16b, v9.16b
        ldp     q11, q12, [x20, #704]
        eor     v29.16b, v13.16b, v14.16b
        orr     v9.16b, v9.16b, v10.16b
        eor     v30.16b, v30.16b, v31.16b
        ldp     q15, q8, [sp, #704]
        eor     v11.16b, v15.16b, v11.16b
        eor     v30.16b, v11.16b, v30.16b
        ldp     q13, q14, [x20, #736]
        eor     v8.16b, v8.16b, v12.16b
        ldp     q10, q15, [sp, #736]
        eor     v10.16b, v10.16b, v13.16b
        orr     v13.16b, v10.16b, v11.16b
        orr     v13.16b, v0.16b, v13.16b
        orr     v13.16b, v13.16b, v1.16b
        orr     v13.16b, v13.16b, v2.16b
        orr     v13.16b, v13.16b, v3.16b
        eor     v0.16b, v0.16b, v1.16b
        orr     v13.16b, v13.16b, v4.16b
        eor     v0.16b, v0.16b, v2.16b
        orr     v9.16b, v13.16b, v9.16b
        orr     v13.16b, v5.16b, v6.16b
        eor     v0.16b, v0.16b, v3.16b
        orr     v13.16b, v13.16b, v7.16b
        eor     v0.16b, v0.16b, v4.16b
        orr     v13.16b, v13.16b, v16.16b
        eor     v0.16b, v0.16b, v5.16b
        orr     v13.16b, v13.16b, v17.16b
        eor     v0.16b, v0.16b, v6.16b
        orr     v13.16b, v13.16b, v18.16b
        eor     v0.16b, v0.16b, v7.16b
        orr     v13.16b, v13.16b, v19.16b
        eor     v0.16b, v0.16b, v16.16b
        orr     v13.16b, v13.16b, v20.16b
        eor     v0.16b, v0.16b, v17.16b
        orr     v9.16b, v9.16b, v13.16b
        orr     v13.16b, v21.16b, v22.16b
        eor     v0.16b, v0.16b, v18.16b
        orr     v13.16b, v13.16b, v23.16b
        eor     v0.16b, v0.16b, v19.16b
        orr     v13.16b, v13.16b, v24.16b
        eor     v0.16b, v0.16b, v20.16b
        orr     v13.16b, v13.16b, v25.16b
        eor     v0.16b, v0.16b, v21.16b
        orr     v13.16b, v13.16b, v26.16b
        eor     v0.16b, v0.16b, v22.16b
        orr     v13.16b, v13.16b, v27.16b
        eor     v0.16b, v0.16b, v23.16b
        orr     v13.16b, v13.16b, v28.16b
        eor     v0.16b, v0.16b, v24.16b
        eor     v12.16b, v15.16b, v14.16b
        orr     v13.16b, v13.16b, v29.16b
        eor     v0.16b, v0.16b, v25.16b
        orr     v9.16b, v9.16b, v13.16b
        orr     v13.16b, v8.16b, v12.16b
        eor     v0.16b, v0.16b, v26.16b
        orr     v9.16b, v9.16b, v13.16b
        eor     v0.16b, v0.16b, v27.16b
        ext     v13.16b, v9.16b, v9.16b, #8
        eor     v0.16b, v0.16b, v28.16b
        eor     v0.16b, v0.16b, v29.16b
        eor     v0.16b, v0.16b, v8.16b
        eor     v30.16b, v10.16b, v30.16b
        eor     v0.16b, v0.16b, v12.16b
        orr     v31.8b, v9.8b, v13.8b
        eor     v0.16b, v0.16b, v30.16b
        fmov    x8, d31
        ext     v1.16b, v0.16b, v0.16b, #8
        orr     x8, x8, x8, lsr #32
        lsr     x9, x8, #16
        eor     v0.8b, v0.8b, v1.8b
        orr     w8, w8, w9
        fmov    x9, d0
        orr     w8, w8, w8, lsr #8
        sub     w8, w23, w8, uxtb
        eor     x9, x9, x9, lsr #32
        eor     x9, x9, x9, lsr #16
        lsr     x10, x9, #8
        eor     w26, w9, w10
        eor     w8, w26, w8, lsr #16
        and     w27, w8, #0xff
        bl      L0840
        add     x0, sp, #0x300
        mov     w1, wzr
        mov     w2, #0x400
        bl      L0840
        cmp     w27, w26, uxtb
        b.ne    L7cb8
        ldp     q0, q1, [x22]
        add     x0, x25, #0x20
        mov     x1, x20
        mov     w2, #0x320
        stp     q0, q1, [sp, #768]
        bl      L53c4
        mov     x0, sp
        add     x1, sp, #0x300
        mov     w2, #0x40
        bl      L5468
        add     x3, x24, #0x20
        add     x1, sp, #0x300
        mov     x0, x21
        mov     x2, x20
        bl      L6b54
        cbnz    w0, L7cbc
        ldp     q0, q1, [sp]
        stp     q0, q1, [x19]
        b       L7cbc
L7cb8:
        mov     w0, #0xfffffffc
L7cbc:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        stp     q0, q0, [sp, #800]
        add     x8, sp, #0x300
        stp     q0, q0, [sp, #768]
        .inst   0x90000148  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #1816]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L7d20
        sub     sp, x29, #0x40
        ldp     x20, x19, [sp, #144]
        ldp     x22, x21, [sp, #128]
        ldp     x24, x23, [sp, #112]
        ldp     x26, x25, [sp, #96]
        ldp     x28, x27, [sp, #80]
        ldp     x29, x30, [sp, #64]
        ldp     d9, d8, [sp, #48]
        ldp     d11, d10, [sp, #32]
        ldp     d13, d12, [sp, #16]
        ldp     d15, d14, [sp], #160
        ret
L7d20:
        bl      L0830

// mlkem512_enc (0x9c bytes)
L7d24:
        stp     x29, x30, [sp, #-48]!
        str     x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0x30
        and     sp, x9, #0xffffffffffffffe0
        .inst   0x90000148  // adrp x8, 0x2f000
        mov     x20, x1
        mov     x21, x0
        mov     x0, sp
        mov     w1, #0x20
        mov     x19, x2
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #40]
        bl      L0820
        cbz     w0, L7d70
        mov     w0, #0xfffffffd
        b       L7d84
L7d70:
        mov     x3, sp
        mov     x0, x21
        mov     x1, x20
        mov     x2, x19
        bl      L7888
L7d84:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        .inst   0x90000148  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #40]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L7dbc
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldr     x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L7dbc:
        bl      L0830

// mlkem512_dec (0x4d8 bytes)
L7dc0:
        stp     d15, d14, [sp, #-144]!
        stp     d13, d12, [sp, #16]
        stp     d11, d10, [sp, #32]
        stp     d9, d8, [sp, #48]
        stp     x29, x30, [sp, #64]
        str     x28, [sp, #80]
        stp     x24, x23, [sp, #96]
        stp     x22, x21, [sp, #112]
        stp     x20, x19, [sp, #128]
        add     x29, sp, #0x40
        sub     x9, sp, #0x3b0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0x90000148  // adrp x8, 0x2f000
        mov     x19, x0
        mov     x0, x2
        mov     x21, x2
        mov     x20, x1
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #936]
        bl      L761c
        mov     w22, w0
        cbnz    w0, L821c
        add     x0, sp, #0x360
        mov     x1, x20
        mov     x2, x21
        bl      L6fe0
        mov     w22, w0
        cbnz    w0, L821c
        ldr     q0, [x21, #1568]
        add     x0, sp, #0x320
        ldr     q1, [x21, #1584]
        add     x1, sp, #0x360
        mov     w2, #0x40
        add     x22, x21, #0x300
        add     x23, sp, #0x320
        stp     q0, q1, [sp, #896]
        bl      L5468
        add     x3, x23, #0x20
        mov     x0, sp
        add     x1, sp, #0x360
        mov     x2, x22
        mov     x24, sp
        bl      L6b54
        mov     w22, w0
        cbnz    w0, L821c
        ldp     q0, q1, [x20]
        add     x0, x24, #0x20
        mov     x1, x20
        mov     w2, #0x300
        ldp     q2, q3, [sp]
        eor     v2.16b, v2.16b, v0.16b
        ldp     q4, q5, [x20, #32]
        eor     v0.16b, v3.16b, v1.16b
        ldp     q6, q7, [sp, #32]
        eor     v4.16b, v6.16b, v4.16b
        ldp     q16, q17, [x20, #64]
        eor     v1.16b, v7.16b, v5.16b
        orr     v7.16b, v4.16b, v2.16b
        eor     v4.16b, v4.16b, v2.16b
        ldp     q18, q3, [sp, #64]
        eor     v16.16b, v18.16b, v16.16b
        eor     v4.16b, v16.16b, v4.16b
        ldp     q6, q5, [x20, #96]
        eor     v2.16b, v3.16b, v17.16b
        ldp     q19, q20, [sp, #96]
        eor     v6.16b, v19.16b, v6.16b
        orr     v16.16b, v6.16b, v16.16b
        ldp     q18, q17, [x20, #128]
        eor     v3.16b, v20.16b, v5.16b
        orr     v7.16b, v16.16b, v7.16b
        eor     v6.16b, v6.16b, v4.16b
        ldp     q21, q19, [sp, #128]
        eor     v18.16b, v21.16b, v18.16b
        eor     v6.16b, v18.16b, v6.16b
        ldp     q5, q20, [x20, #160]
        eor     v4.16b, v19.16b, v17.16b
        ldp     q16, q22, [sp, #160]
        eor     v16.16b, v16.16b, v5.16b
        orr     v18.16b, v16.16b, v18.16b
        ldp     q21, q17, [x20, #192]
        eor     v5.16b, v22.16b, v20.16b
        eor     v16.16b, v16.16b, v6.16b
        ldp     q19, q23, [sp, #192]
        eor     v19.16b, v19.16b, v21.16b
        orr     v18.16b, v19.16b, v18.16b
        ldp     q20, q22, [x20, #224]
        eor     v6.16b, v23.16b, v17.16b
        orr     v25.16b, v18.16b, v7.16b
        eor     v16.16b, v19.16b, v16.16b
        ldp     q24, q21, [sp, #224]
        eor     v20.16b, v24.16b, v20.16b
        ldp     q17, q23, [x20, #256]
        eor     v7.16b, v21.16b, v22.16b
        eor     v22.16b, v20.16b, v16.16b
        ldp     q18, q19, [sp, #256]
        eor     v17.16b, v18.16b, v17.16b
        orr     v20.16b, v17.16b, v20.16b
        ldp     q24, q21, [x20, #288]
        eor     v16.16b, v19.16b, v23.16b
        eor     v22.16b, v17.16b, v22.16b
        ldp     q26, q18, [sp, #288]
        eor     v24.16b, v26.16b, v24.16b
        orr     v20.16b, v24.16b, v20.16b
        ldp     q19, q23, [x20, #320]
        eor     v17.16b, v18.16b, v21.16b
        eor     v22.16b, v24.16b, v22.16b
        ldp     q27, q26, [sp, #320]
        eor     v19.16b, v27.16b, v19.16b
        orr     v20.16b, v19.16b, v20.16b
        ldp     q21, q28, [x20, #352]
        eor     v18.16b, v26.16b, v23.16b
        orr     v25.16b, v20.16b, v25.16b
        eor     v22.16b, v19.16b, v22.16b
        ldp     q24, q27, [sp, #352]
        eor     v21.16b, v24.16b, v21.16b
        eor     v22.16b, v21.16b, v22.16b
        ldp     q23, q26, [x20, #384]
        eor     v19.16b, v27.16b, v28.16b
        ldp     q20, q29, [sp, #384]
        eor     v23.16b, v20.16b, v23.16b
        eor     v22.16b, v23.16b, v22.16b
        ldp     q24, q27, [x20, #416]
        eor     v20.16b, v29.16b, v26.16b
        orr     v29.16b, v23.16b, v21.16b
        ldp     q28, q30, [sp, #416]
        eor     v24.16b, v28.16b, v24.16b
        orr     v29.16b, v24.16b, v29.16b
        ldp     q26, q31, [x20, #448]
        eor     v21.16b, v30.16b, v27.16b
        eor     v24.16b, v24.16b, v22.16b
        ldp     q23, q28, [sp, #448]
        eor     v23.16b, v23.16b, v26.16b
        orr     v29.16b, v23.16b, v29.16b
        ldp     q27, q30, [x20, #480]
        eor     v22.16b, v28.16b, v31.16b
        eor     v24.16b, v23.16b, v24.16b
        ldp     q8, q26, [sp, #480]
        eor     v27.16b, v8.16b, v27.16b
        orr     v29.16b, v27.16b, v29.16b
        ldp     q28, q31, [x20, #512]
        eor     v23.16b, v26.16b, v30.16b
        orr     v10.16b, v29.16b, v25.16b
        eor     v27.16b, v27.16b, v24.16b
        ldp     q9, q8, [sp, #512]
        eor     v28.16b, v9.16b, v28.16b
        eor     v27.16b, v28.16b, v27.16b
        ldp     q26, q30, [x20, #544]
        eor     v24.16b, v8.16b, v31.16b
        ldp     q25, q29, [sp, #544]
        eor     v26.16b, v25.16b, v26.16b
        orr     v28.16b, v26.16b, v28.16b
        ldp     q9, q31, [x20, #576]
        eor     v25.16b, v29.16b, v30.16b
        eor     v27.16b, v26.16b, v27.16b
        ldp     q8, q11, [sp, #576]
        eor     v8.16b, v8.16b, v9.16b
        orr     v28.16b, v8.16b, v28.16b
        ldp     q29, q30, [x20, #608]
        eor     v26.16b, v11.16b, v31.16b
        eor     v8.16b, v8.16b, v27.16b
        ldp     q12, q9, [sp, #608]
        eor     v29.16b, v12.16b, v29.16b
        ldp     q31, q11, [x20, #640]
        eor     v27.16b, v9.16b, v30.16b
        orr     v9.16b, v29.16b, v28.16b
        eor     v29.16b, v29.16b, v8.16b
        ldp     q13, q12, [sp, #640]
        eor     v31.16b, v13.16b, v31.16b
        orr     v9.16b, v31.16b, v9.16b
        ldp     q30, q14, [x20, #672]
        eor     v28.16b, v12.16b, v11.16b
        eor     v31.16b, v31.16b, v29.16b
        ldp     q8, q13, [sp, #672]
        eor     v30.16b, v8.16b, v30.16b
        orr     v9.16b, v30.16b, v9.16b
        ldp     q11, q12, [x20, #704]
        eor     v29.16b, v13.16b, v14.16b
        orr     v9.16b, v9.16b, v10.16b
        eor     v30.16b, v30.16b, v31.16b
        ldp     q15, q8, [sp, #704]
        eor     v11.16b, v15.16b, v11.16b
        eor     v30.16b, v11.16b, v30.16b
        ldp     q13, q14, [x20, #736]
        eor     v8.16b, v8.16b, v12.16b
        ldp     q10, q15, [sp, #736]
        eor     v10.16b, v10.16b, v13.16b
        orr     v13.16b, v10.16b, v11.16b
        orr     v13.16b, v0.16b, v13.16b
        orr     v13.16b, v13.16b, v1.16b
        orr     v13.16b, v13.16b, v2.16b
        orr     v13.16b, v13.16b, v3.16b
        eor     v0.16b, v0.16b, v1.16b
        orr     v13.16b, v13.16b, v4.16b
        eor     v0.16b, v0.16b, v2.16b
        orr     v9.16b, v13.16b, v9.16b
        orr     v13.16b, v5.16b, v6.16b
        eor     v0.16b, v0.16b, v3.16b
        orr     v13.16b, v13.16b, v7.16b
        eor     v0.16b, v0.16b, v4.16b
        orr     v13.16b, v13.16b, v16.16b
        eor     v0.16b, v0.16b, v5.16b
        orr     v13.16b, v13.16b, v17.16b
        eor     v0.16b, v0.16b, v6.16b
        orr     v13.16b, v13.16b, v18.16b
        eor     v0.16b, v0.16b, v7.16b
        orr     v13.16b, v13.16b, v19.16b
        eor     v0.16b, v0.16b, v16.16b
        orr     v13.16b, v13.16b, v20.16b
        eor     v0.16b, v0.16b, v17.16b
        orr     v9.16b, v9.16b, v13.16b
        orr     v13.16b, v21.16b, v22.16b
        eor     v0.16b, v0.16b, v18.16b
        orr     v13.16b, v13.16b, v23.16b
        eor     v0.16b, v0.16b, v19.16b
        orr     v13.16b, v13.16b, v24.16b
        eor     v0.16b, v0.16b, v20.16b
        orr     v13.16b, v13.16b, v25.16b
        eor     v0.16b, v0.16b, v21.16b
        orr     v13.16b, v13.16b, v26.16b
        eor     v0.16b, v0.16b, v22.16b
        orr     v13.16b, v13.16b, v27.16b
        eor     v0.16b, v0.16b, v23.16b
        orr     v13.16b, v13.16b, v28.16b
        eor     v0.16b, v0.16b, v24.16b
        eor     v12.16b, v15.16b, v14.16b
        orr     v13.16b, v13.16b, v29.16b
        eor     v0.16b, v0.16b, v25.16b
        orr     v9.16b, v9.16b, v13.16b
        orr     v13.16b, v8.16b, v12.16b
        eor     v0.16b, v0.16b, v26.16b
        orr     v9.16b, v9.16b, v13.16b
        eor     v0.16b, v0.16b, v27.16b
        ext     v13.16b, v9.16b, v9.16b, #8
        eor     v0.16b, v0.16b, v28.16b
        eor     v0.16b, v0.16b, v29.16b
        eor     v0.16b, v0.16b, v8.16b
        eor     v30.16b, v10.16b, v30.16b
        eor     v0.16b, v0.16b, v12.16b
        orr     v31.8b, v9.8b, v13.8b
        eor     v0.16b, v0.16b, v30.16b
        fmov    x8, d31
        ext     v1.16b, v0.16b, v0.16b, #8
        orr     x8, x8, x8, lsr #32
        lsr     x9, x8, #16
        eor     v0.8b, v0.8b, v1.8b
        orr     w8, w8, w9
        fmov    x9, d0
        orr     w8, w8, w8, lsr #8
        sub     w8, w22, w8, uxtb
        eor     x9, x9, x9, lsr #32
        eor     x9, x9, x9, lsr #16
        lsr     x10, x9, #8
        eor     w9, w9, w10
        eor     w8, w9, w8, lsr #16
        ldr     q0, [x21, #1600]
        ldr     q1, [x21, #1616]
        eor     w21, w8, w9
        stp     q0, q1, [sp]
        bl      L0810
        mov     x2, sp
        mov     x0, x19
        mov     w1, #0x20
        mov     w3, #0x320
        bl      L52f0
        mov     x8, xzr
        sub     w9, w22, w21, uxtb
L81ec:
        ldrb    w10, [x19, x8]
        mov     w11, w9
        ldrb    w12, [x23, x8]
        lsr     w11, w11, #16
        and     w10, w10, w11
        bic     w12, w12, w11
        orr     w10, w10, w12
        strb    w10, [x19, x8]
        add     x8, x8, #0x1
        cmp     x8, #0x20
        b.ne    L81ec
        mov     w22, wzr
L821c:
        mov     x0, sp
        mov     w1, wzr
        mov     w2, #0x320
        mov     x19, sp
        bl      L0840
        movi    v0.2d, #0x0
        add     x8, sp, #0x320
        stp     q0, q0, [sp, #800]
        stp     q0, q0, [sp, #832]
        stp     q0, q0, [sp, #896]
        add     x8, sp, #0x360
        stp     q0, q0, [sp, #864]
        .inst   0xf0000128  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #936]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L8294
        mov     w0, w22
        sub     sp, x29, #0x40
        ldp     x20, x19, [sp, #128]
        ldp     x22, x21, [sp, #112]
        ldp     x24, x23, [sp, #96]
        ldp     x29, x30, [sp, #64]
        ldp     d9, d8, [sp, #48]
        ldp     d11, d10, [sp, #32]
        ldp     d13, d12, [sp, #16]
        ldr     x28, [sp, #80]
        ldp     d15, d14, [sp], #144
        ret
L8294:
        bl      L0830

// mlkem_poly_tomont (0x94 bytes)
L8298:
        mov     w9, #0x549
        mov     w10, #0x50490000
        mov     x8, xzr
        mvni    v2.4s, #0xd, lsl #8
        dup     v0.8h, w9
        dup     v1.4s, w10
L82b0:
        add     x9, x0, x8
        add     x8, x8, #0x20
        cmp     x8, #0x200
        ldp     q3, q4, [x9]
        sxtl    v5.4s, v3.4h
        sxtl2   v6.4s, v3.8h
        sxtl    v7.4s, v4.4h
        mul     v5.4s, v5.4s, v1.4s
        mul     v7.4s, v7.4s, v1.4s
        sxtl2   v16.4s, v4.8h
        mul     v6.4s, v6.4s, v1.4s
        mul     v16.4s, v16.4s, v1.4s
        sshr    v5.4s, v5.4s, #16
        sshr    v7.4s, v7.4s, #16
        smull2  v17.4s, v3.8h, v0.8h
        sshr    v6.4s, v6.4s, #16
        smull   v3.4s, v3.4h, v0.4h
        smull2  v18.4s, v4.8h, v0.8h
        smull   v4.4s, v4.4h, v0.4h
        mul     v5.4s, v5.4s, v2.4s
        mul     v7.4s, v7.4s, v2.4s
        sshr    v16.4s, v16.4s, #16
        mul     v6.4s, v6.4s, v2.4s
        mul     v16.4s, v16.4s, v2.4s
        addhn   v3.4h, v5.4s, v3.4s
        addhn   v4.4h, v7.4s, v4.4s
        addhn2  v3.8h, v6.4s, v17.4s
        addhn2  v4.8h, v16.4s, v18.4s
        stp     q3, q4, [x9]
        b.ne    L82b0
        ret

// mlkem_poly_reduce (0x50 bytes)
L832c:
        mov     x8, xzr
        mov     w9, #0x4ebf
        mov     w10, #0x2000000
        mov     w11, #0xfffff2ff
L833c:
        ldrsh   w12, [x0, x8]
        madd    w13, w12, w9, w10
        asr     w13, w13, #26
        madd    w12, w13, w11, w12
        sxth    w13, w12
        add     w14, w12, #0xd01
        neg     w13, w13, lsr #16
        lsr     w13, w13, #16
        bic     w12, w12, w13
        and     w13, w14, w13
        orr     w12, w13, w12
        strh    w12, [x0, x8]
        add     x8, x8, #0x2
        cmp     x8, #0x200
        b.ne    L833c
        ret

// mlkem_poly_add (0x180 bytes)
L837c:
        add     x8, x1, #0x200
        cmp     x8, x0
        b.ls    L83b8
        add     x8, x0, #0x200
        cmp     x8, x1
        b.ls    L83b8
        mov     x8, xzr
L8398:
        ldrh    w9, [x0, x8]
        ldrh    w10, [x1, x8]
        add     w9, w10, w9
        strh    w9, [x0, x8]
        add     x8, x8, #0x2
        cmp     x8, #0x200
        b.ne    L8398
        ret
L83b8:
        ldp     q0, q1, [x0]
        ldp     q2, q3, [x1]
        add     v0.8h, v2.8h, v0.8h
        ldp     q4, q2, [x0, #32]
        add     v1.8h, v3.8h, v1.8h
        stp     q0, q1, [x0]
        ldp     q3, q5, [x1, #32]
        add     v1.8h, v3.8h, v4.8h
        ldp     q0, q3, [x0, #64]
        add     v2.8h, v5.8h, v2.8h
        stp     q1, q2, [x0, #32]
        ldp     q4, q5, [x1, #64]
        add     v0.8h, v4.8h, v0.8h
        ldp     q1, q2, [x0, #96]
        add     v3.8h, v5.8h, v3.8h
        stp     q0, q3, [x0, #64]
        ldp     q4, q5, [x1, #96]
        add     v1.8h, v4.8h, v1.8h
        ldp     q0, q3, [x0, #128]
        add     v2.8h, v5.8h, v2.8h
        stp     q1, q2, [x0, #96]
        ldp     q4, q5, [x1, #128]
        add     v0.8h, v4.8h, v0.8h
        ldp     q1, q2, [x0, #160]
        add     v3.8h, v5.8h, v3.8h
        stp     q0, q3, [x0, #128]
        ldp     q4, q5, [x1, #160]
        add     v1.8h, v4.8h, v1.8h
        ldp     q0, q3, [x0, #192]
        add     v2.8h, v5.8h, v2.8h
        stp     q1, q2, [x0, #160]
        ldp     q4, q5, [x1, #192]
        add     v0.8h, v4.8h, v0.8h
        ldp     q1, q2, [x0, #224]
        add     v3.8h, v5.8h, v3.8h
        stp     q0, q3, [x0, #192]
        ldp     q4, q5, [x1, #224]
        add     v1.8h, v4.8h, v1.8h
        ldp     q0, q3, [x0, #256]
        add     v2.8h, v5.8h, v2.8h
        stp     q1, q2, [x0, #224]
        ldp     q4, q5, [x1, #256]
        add     v0.8h, v4.8h, v0.8h
        ldp     q1, q2, [x0, #288]
        add     v3.8h, v5.8h, v3.8h
        stp     q0, q3, [x0, #256]
        ldp     q4, q5, [x1, #288]
        add     v1.8h, v4.8h, v1.8h
        ldp     q0, q3, [x0, #320]
        add     v2.8h, v5.8h, v2.8h
        stp     q1, q2, [x0, #288]
        ldp     q4, q5, [x1, #320]
        add     v0.8h, v4.8h, v0.8h
        ldp     q1, q2, [x0, #352]
        add     v3.8h, v5.8h, v3.8h
        stp     q0, q3, [x0, #320]
        ldp     q4, q5, [x1, #352]
        add     v1.8h, v4.8h, v1.8h
        ldp     q0, q3, [x0, #384]
        add     v2.8h, v5.8h, v2.8h
        stp     q1, q2, [x0, #352]
        ldp     q4, q5, [x1, #384]
        add     v0.8h, v4.8h, v0.8h
        ldp     q1, q2, [x0, #416]
        add     v3.8h, v5.8h, v3.8h
        stp     q0, q3, [x0, #384]
        ldp     q4, q5, [x1, #416]
        add     v1.8h, v4.8h, v1.8h
        ldp     q0, q3, [x0, #448]
        add     v2.8h, v5.8h, v2.8h
        stp     q1, q2, [x0, #416]
        ldp     q4, q5, [x1, #448]
        add     v0.8h, v4.8h, v0.8h
        ldp     q1, q2, [x0, #480]
        add     v3.8h, v5.8h, v3.8h
        stp     q0, q3, [x0, #448]
        ldp     q4, q5, [x1, #480]
        add     v0.8h, v4.8h, v1.8h
        add     v1.8h, v5.8h, v2.8h
        stp     q0, q1, [x0, #480]
        ret

// mlkem_poly_sub (0x180 bytes)
L84fc:
        add     x8, x1, #0x200
        cmp     x8, x0
        b.ls    L8538
        add     x8, x0, #0x200
        cmp     x8, x1
        b.ls    L8538
        mov     x8, xzr
L8518:
        ldrh    w9, [x0, x8]
        ldrh    w10, [x1, x8]
        sub     w9, w9, w10
        strh    w9, [x0, x8]
        add     x8, x8, #0x2
        cmp     x8, #0x200
        b.ne    L8518
        ret
L8538:
        ldp     q0, q1, [x0]
        ldp     q2, q3, [x1]
        sub     v0.8h, v0.8h, v2.8h
        ldp     q4, q2, [x0, #32]
        sub     v1.8h, v1.8h, v3.8h
        stp     q0, q1, [x0]
        ldp     q3, q5, [x1, #32]
        sub     v1.8h, v4.8h, v3.8h
        ldp     q0, q3, [x0, #64]
        sub     v2.8h, v2.8h, v5.8h
        stp     q1, q2, [x0, #32]
        ldp     q4, q5, [x1, #64]
        sub     v0.8h, v0.8h, v4.8h
        ldp     q1, q2, [x0, #96]
        sub     v3.8h, v3.8h, v5.8h
        stp     q0, q3, [x0, #64]
        ldp     q4, q5, [x1, #96]
        sub     v1.8h, v1.8h, v4.8h
        ldp     q0, q3, [x0, #128]
        sub     v2.8h, v2.8h, v5.8h
        stp     q1, q2, [x0, #96]
        ldp     q4, q5, [x1, #128]
        sub     v0.8h, v0.8h, v4.8h
        ldp     q1, q2, [x0, #160]
        sub     v3.8h, v3.8h, v5.8h
        stp     q0, q3, [x0, #128]
        ldp     q4, q5, [x1, #160]
        sub     v1.8h, v1.8h, v4.8h
        ldp     q0, q3, [x0, #192]
        sub     v2.8h, v2.8h, v5.8h
        stp     q1, q2, [x0, #160]
        ldp     q4, q5, [x1, #192]
        sub     v0.8h, v0.8h, v4.8h
        ldp     q1, q2, [x0, #224]
        sub     v3.8h, v3.8h, v5.8h
        stp     q0, q3, [x0, #192]
        ldp     q4, q5, [x1, #224]
        sub     v1.8h, v1.8h, v4.8h
        ldp     q0, q3, [x0, #256]
        sub     v2.8h, v2.8h, v5.8h
        stp     q1, q2, [x0, #224]
        ldp     q4, q5, [x1, #256]
        sub     v0.8h, v0.8h, v4.8h
        ldp     q1, q2, [x0, #288]
        sub     v3.8h, v3.8h, v5.8h
        stp     q0, q3, [x0, #256]
        ldp     q4, q5, [x1, #288]
        sub     v1.8h, v1.8h, v4.8h
        ldp     q0, q3, [x0, #320]
        sub     v2.8h, v2.8h, v5.8h
        stp     q1, q2, [x0, #288]
        ldp     q4, q5, [x1, #320]
        sub     v0.8h, v0.8h, v4.8h
        ldp     q1, q2, [x0, #352]
        sub     v3.8h, v3.8h, v5.8h
        stp     q0, q3, [x0, #320]
        ldp     q4, q5, [x1, #352]
        sub     v1.8h, v1.8h, v4.8h
        ldp     q0, q3, [x0, #384]
        sub     v2.8h, v2.8h, v5.8h
        stp     q1, q2, [x0, #352]
        ldp     q4, q5, [x1, #384]
        sub     v0.8h, v0.8h, v4.8h
        ldp     q1, q2, [x0, #416]
        sub     v3.8h, v3.8h, v5.8h
        stp     q0, q3, [x0, #384]
        ldp     q4, q5, [x1, #416]
        sub     v1.8h, v1.8h, v4.8h
        ldp     q0, q3, [x0, #448]
        sub     v2.8h, v2.8h, v5.8h
        stp     q1, q2, [x0, #416]
        ldp     q4, q5, [x1, #448]
        sub     v0.8h, v0.8h, v4.8h
        ldp     q1, q2, [x0, #480]
        sub     v3.8h, v3.8h, v5.8h
        stp     q0, q3, [x0, #448]
        ldp     q4, q5, [x1, #480]
        sub     v0.8h, v1.8h, v4.8h
        sub     v1.8h, v2.8h, v5.8h
        stp     q0, q1, [x0, #480]
        ret

// mlkem_poly_mulcache_compute (0x5ac bytes)
L867c:
        add     x8, x1, #0x2
        add     x9, x1, #0x200
        cmp     x9, x0
        b.ls    L86a0
        add     x9, x0, #0x100
        cmp     x8, x9
        b.cs    L86a0
        mov     x11, xzr
        b       L8ba8
L86a0:
        ld4     {v1.8h-v4.8h}, [x8]
        .inst   0xf0000028  // adrp x8, 0xf000
        .inst   0xf0000029  // adrp x9, 0xf000
        .inst   0xf000002b  // adrp x11, 0xf000
        .inst   0xf000002a  // adrp x10, 0xf000
        mvni    v0.4s, #0xd, lsl #8
        ldr     d5, [x8, #1648]
        .inst   0xf0000028  // adrp x8, 0xf000
        ldr     d6, [x9, #1656]
        .inst   0xf0000029  // adrp x9, 0xf000
        ldr     q7, [x11, #1072]
        .inst   0xf000002b  // adrp x11, 0xf000
        ldr     d16, [x8, #1672]
        .inst   0xf0000028  // adrp x8, 0xf000
        sxtl    v17.4s, v1.4h
        ldr     q23, [x10, #1056]
        sxtl2   v18.4s, v1.8h
        .inst   0xf000002a  // adrp x10, 0xf000
        ext     v19.16b, v1.16b, v1.16b, #8
        smull   v6.4s, v1.4h, v6.4h
        sxtl    v20.4s, v3.4h
        sxtl2   v21.4s, v3.8h
        ext     v22.16b, v3.16b, v3.16b, #8
        smull   v1.4s, v3.4h, v16.4h
        ldr     q4, [x11, #1104]
        mul     v3.4s, v17.4s, v7.4s
        ldr     q2, [x9, #1088]
        mul     v7.4s, v18.4s, v23.4s
        ldr     d16, [x8, #1664]
        mul     v4.4s, v20.4s, v4.4s
        mov     x8, x0
        mul     v2.4s, v21.4s, v2.4s
        add     x9, x1, #0x42
        sshr    v3.4s, v3.4s, #16
        .inst   0xf000002b  // adrp x11, 0xf000
        sshr    v7.4s, v7.4s, #16
        mul     v3.4s, v3.4s, v0.4s
        sshr    v4.4s, v4.4s, #16
        smull   v5.4s, v19.4h, v5.4h
        mul     v7.4s, v7.4s, v0.4s
        mul     v4.4s, v4.4s, v0.4s
        addhn   v17.4h, v3.4s, v6.4s
        ldr     d6, [x10, #1688]
        sshr    v2.4s, v2.4s, #16
        .inst   0xf000002a  // adrp x10, 0xf000
        smull   v3.4s, v22.4h, v16.4h
        mul     v2.4s, v2.4s, v0.4s
        addhn2  v17.8h, v7.4s, v5.4s
        ldr     q7, [x11, #1120]
        addhn   v18.4h, v4.4s, v1.4s
        .inst   0xf000002b  // adrp x11, 0xf000
        addhn2  v18.8h, v2.4s, v3.4s
        st2     {v17.8h-v18.8h}, [x8], #32
        ld4     {v1.8h-v4.8h}, [x9]
        .inst   0xf0000029  // adrp x9, 0xf000
        ldr     d5, [x9, #1680]
        .inst   0xf0000029  // adrp x9, 0xf000
        ldr     d17, [x10, #1704]
        .inst   0xf000002a  // adrp x10, 0xf000
        ldr     q18, [x11, #1152]
        mov     w11, #0x38
        ldr     q16, [x9, #1136]
        .inst   0xf0000029  // adrp x9, 0xf000
        sxtl    v19.4s, v1.4h
        sxtl2   v20.4s, v1.8h
        ext     v21.16b, v1.16b, v1.16b, #8
        smull   v6.4s, v1.4h, v6.4h
        sxtl    v22.4s, v3.4h
        sxtl2   v23.4s, v3.8h
        smull   v17.4s, v3.4h, v17.4h
        ext     v1.16b, v3.16b, v3.16b, #8
        ldr     q2, [x9, #1168]
        mul     v3.4s, v19.4s, v16.4s
        .inst   0xf0000029  // adrp x9, 0xf000
        mul     v4.4s, v20.4s, v7.4s
        mul     v2.4s, v22.4s, v2.4s
        mul     v7.4s, v23.4s, v18.4s
        ldr     d16, [x9, #1696]
        sshr    v3.4s, v3.4s, #16
        add     x9, x1, #0x82
        sshr    v4.4s, v4.4s, #16
        mul     v3.4s, v3.4s, v0.4s
        sshr    v2.4s, v2.4s, #16
        smull   v5.4s, v21.4h, v5.4h
        mul     v4.4s, v4.4s, v0.4s
        mul     v2.4s, v2.4s, v0.4s
        addhn   v18.4h, v3.4s, v6.4s
        sshr    v7.4s, v7.4s, #16
        smull   v1.4s, v1.4h, v16.4h
        mul     v3.4s, v7.4s, v0.4s
        ldr     q7, [x10, #1184]
        addhn2  v18.8h, v4.4s, v5.4s
        .inst   0xf000002a  // adrp x10, 0xf000
        addhn   v19.4h, v2.4s, v17.4s
        addhn2  v19.8h, v3.4s, v1.4s
        st2     {v18.8h-v19.8h}, [x8]
        .inst   0xf0000028  // adrp x8, 0xf000
        ld4     {v1.8h-v4.8h}, [x9]
        .inst   0xf0000029  // adrp x9, 0xf000
        ldr     d5, [x8, #1712]
        .inst   0xf0000028  // adrp x8, 0xf000
        ldr     d6, [x9, #1720]
        .inst   0xf0000029  // adrp x9, 0xf000
        ldr     q18, [x10, #1216]
        .inst   0xf000002a  // adrp x10, 0xf000
        ldr     q16, [x8, #1200]
        .inst   0xf0000028  // adrp x8, 0xf000
        ldr     d17, [x9, #1736]
        add     x9, x1, #0xc2
        sxtl    v19.4s, v1.4h
        sxtl2   v20.4s, v1.8h
        ext     v21.16b, v1.16b, v1.16b, #8
        smull   v6.4s, v1.4h, v6.4h
        sxtl    v22.4s, v3.4h
        sxtl2   v23.4s, v3.8h
        smull   v17.4s, v3.4h, v17.4h
        ext     v1.16b, v3.16b, v3.16b, #8
        ldr     q2, [x8, #1232]
        mul     v3.4s, v19.4s, v16.4s
        .inst   0xf0000028  // adrp x8, 0xf000
        mul     v4.4s, v20.4s, v7.4s
        mul     v2.4s, v22.4s, v2.4s
        mul     v7.4s, v23.4s, v18.4s
        ldr     d16, [x8, #1728]
        sshr    v3.4s, v3.4s, #16
        add     x8, x0, #0x40
        sshr    v4.4s, v4.4s, #16
        mul     v3.4s, v3.4s, v0.4s
        sshr    v2.4s, v2.4s, #16
        smull   v5.4s, v21.4h, v5.4h
        mul     v4.4s, v4.4s, v0.4s
        mul     v2.4s, v2.4s, v0.4s
        addhn   v18.4h, v3.4s, v6.4s
        sshr    v7.4s, v7.4s, #16
        smull   v1.4s, v1.4h, v16.4h
        mul     v3.4s, v7.4s, v0.4s
        ldr     q7, [x10, #1248]
        addhn2  v18.8h, v4.4s, v5.4s
        .inst   0xf000002a  // adrp x10, 0xf000
        addhn   v19.4h, v2.4s, v17.4s
        addhn2  v19.8h, v3.4s, v1.4s
        st2     {v18.8h-v19.8h}, [x8]
        .inst   0xf0000028  // adrp x8, 0xf000
        ld4     {v1.8h-v4.8h}, [x9]
        .inst   0xf0000029  // adrp x9, 0xf000
        ldr     d5, [x8, #1744]
        .inst   0xf0000028  // adrp x8, 0xf000
        ldr     d6, [x9, #1752]
        .inst   0xf0000029  // adrp x9, 0xf000
        ldr     q18, [x10, #1280]
        .inst   0xf000002a  // adrp x10, 0xf000
        ldr     q16, [x8, #1264]
        .inst   0xf0000028  // adrp x8, 0xf000
        ldr     d17, [x9, #1768]
        add     x9, x1, #0x102
        sxtl    v19.4s, v1.4h
        sxtl2   v20.4s, v1.8h
        ext     v21.16b, v1.16b, v1.16b, #8
        smull   v6.4s, v1.4h, v6.4h
        sxtl    v22.4s, v3.4h
        sxtl2   v23.4s, v3.8h
        smull   v17.4s, v3.4h, v17.4h
        ext     v1.16b, v3.16b, v3.16b, #8
        ldr     q2, [x8, #1296]
        mul     v3.4s, v19.4s, v16.4s
        .inst   0xf0000028  // adrp x8, 0xf000
        mul     v4.4s, v20.4s, v7.4s
        mul     v2.4s, v22.4s, v2.4s
        mul     v7.4s, v23.4s, v18.4s
        ldr     d16, [x8, #1760]
        sshr    v3.4s, v3.4s, #16
        add     x8, x0, #0x60
        sshr    v4.4s, v4.4s, #16
        mul     v3.4s, v3.4s, v0.4s
        sshr    v2.4s, v2.4s, #16
        smull   v5.4s, v21.4h, v5.4h
        mul     v4.4s, v4.4s, v0.4s
        mul     v2.4s, v2.4s, v0.4s
        addhn   v18.4h, v3.4s, v6.4s
        sshr    v7.4s, v7.4s, #16
        smull   v1.4s, v1.4h, v16.4h
        mul     v3.4s, v7.4s, v0.4s
        ldr     q7, [x10, #1312]
        addhn2  v18.8h, v4.4s, v5.4s
        .inst   0xf000002a  // adrp x10, 0xf000
        addhn   v19.4h, v2.4s, v17.4s
        addhn2  v19.8h, v3.4s, v1.4s
        st2     {v18.8h-v19.8h}, [x8]
        .inst   0xf0000028  // adrp x8, 0xf000
        ld4     {v1.8h-v4.8h}, [x9]
        .inst   0xf0000029  // adrp x9, 0xf000
        ldr     d5, [x8, #1776]
        .inst   0xf0000028  // adrp x8, 0xf000
        ldr     d6, [x9, #1784]
        .inst   0xf0000029  // adrp x9, 0xf000
        ldr     q18, [x10, #1344]
        .inst   0xf000002a  // adrp x10, 0xf000
        ldr     q16, [x8, #1328]
        .inst   0xf0000028  // adrp x8, 0xf000
        ldr     d17, [x9, #1800]
        add     x9, x1, #0x142
        sxtl    v19.4s, v1.4h
        sxtl2   v20.4s, v1.8h
        ext     v21.16b, v1.16b, v1.16b, #8
        smull   v6.4s, v1.4h, v6.4h
        sxtl    v22.4s, v3.4h
        sxtl2   v23.4s, v3.8h
        smull   v17.4s, v3.4h, v17.4h
        ext     v1.16b, v3.16b, v3.16b, #8
        ldr     q2, [x8, #1360]
        mul     v3.4s, v19.4s, v16.4s
        .inst   0xf0000028  // adrp x8, 0xf000
        mul     v4.4s, v20.4s, v7.4s
        mul     v2.4s, v22.4s, v2.4s
        mul     v7.4s, v23.4s, v18.4s
        ldr     d16, [x8, #1792]
        sshr    v3.4s, v3.4s, #16
        add     x8, x0, #0x80
        sshr    v4.4s, v4.4s, #16
        mul     v3.4s, v3.4s, v0.4s
        sshr    v2.4s, v2.4s, #16
        smull   v5.4s, v21.4h, v5.4h
        mul     v4.4s, v4.4s, v0.4s
        mul     v2.4s, v2.4s, v0.4s
        addhn   v18.4h, v3.4s, v6.4s
        sshr    v7.4s, v7.4s, #16
        smull   v1.4s, v1.4h, v16.4h
        mul     v3.4s, v7.4s, v0.4s
        ldr     q7, [x10, #1376]
        addhn2  v18.8h, v4.4s, v5.4s
        .inst   0xf000002a  // adrp x10, 0xf000
        addhn   v19.4h, v2.4s, v17.4s
        addhn2  v19.8h, v3.4s, v1.4s
        st2     {v18.8h-v19.8h}, [x8]
        .inst   0xf0000028  // adrp x8, 0xf000
        ld4     {v1.8h-v4.8h}, [x9]
        .inst   0xf0000029  // adrp x9, 0xf000
        ldr     d5, [x8, #1808]
        .inst   0xf0000028  // adrp x8, 0xf000
        ldr     d6, [x9, #1816]
        .inst   0xf0000029  // adrp x9, 0xf000
        ldr     q16, [x8, #1392]
        .inst   0xf0000028  // adrp x8, 0xf000
        ldr     d17, [x9, #1832]
        add     x9, x1, #0x182
        sxtl    v18.4s, v1.4h
        sxtl2   v19.4s, v1.8h
        ext     v20.16b, v1.16b, v1.16b, #8
        smull   v6.4s, v1.4h, v6.4h
        sxtl    v21.4s, v3.4h
        sxtl2   v22.4s, v3.8h
        smull   v17.4s, v3.4h, v17.4h
        ext     v1.16b, v3.16b, v3.16b, #8
        ldr     q4, [x8, #1424]
        mul     v3.4s, v18.4s, v16.4s
        ldr     q2, [x10, #1408]
        mul     v7.4s, v19.4s, v7.4s
        .inst   0xf0000028  // adrp x8, 0xf000
        mul     v4.4s, v21.4s, v4.4s
        .inst   0xf000002a  // adrp x10, 0xf000
        mul     v2.4s, v22.4s, v2.4s
        sshr    v3.4s, v3.4s, #16
        ldr     d16, [x8, #1824]
        sshr    v7.4s, v7.4s, #16
        add     x8, x0, #0xa0
        mul     v3.4s, v3.4s, v0.4s
        sshr    v4.4s, v4.4s, #16
        smull   v5.4s, v20.4h, v5.4h
        mul     v7.4s, v7.4s, v0.4s
        mul     v4.4s, v4.4s, v0.4s
        addhn   v18.4h, v3.4s, v6.4s
        sshr    v2.4s, v2.4s, #16
        smull   v1.4s, v1.4h, v16.4h
        mul     v2.4s, v2.4s, v0.4s
        addhn2  v18.8h, v7.4s, v5.4s
        ldr     d7, [x10, #1864]
        addhn   v19.4h, v4.4s, v17.4s
        addhn2  v19.8h, v2.4s, v1.4s
        st2     {v18.8h-v19.8h}, [x8]
        .inst   0xf0000028  // adrp x8, 0xf000
        ld4     {v1.8h-v4.8h}, [x9]
        .inst   0xf0000029  // adrp x9, 0xf000
        ldr     d5, [x8, #1848]
        .inst   0xf0000028  // adrp x8, 0xf000
        ldr     q6, [x9, #1456]
        .inst   0xf0000029  // adrp x9, 0xf000
        sxtl    v16.4s, v1.4h
        sxtl2   v17.4s, v1.8h
        ext     v18.16b, v1.16b, v1.16b, #8
        smull   v5.4s, v1.4h, v5.4h
        sxtl    v19.4s, v3.4h
        sxtl2   v20.4s, v3.8h
        smull   v7.4s, v3.4h, v7.4h
        ext     v1.16b, v3.16b, v3.16b, #8
        ldr     q2, [x8, #1440]
        mul     v3.4s, v16.4s, v6.4s
        .inst   0xf0000028  // adrp x8, 0xf000
        ldr     q4, [x9, #1488]
        .inst   0xf0000029  // adrp x9, 0xf000
        mul     v2.4s, v17.4s, v2.4s
        ldr     q6, [x8, #1472]
        .inst   0xf0000028  // adrp x8, 0xf000
        mul     v4.4s, v19.4s, v4.4s
        sshr    v3.4s, v3.4s, #16
        ldr     d16, [x9, #1840]
        mul     v3.4s, v3.4s, v0.4s
        sshr    v2.4s, v2.4s, #16
        mul     v6.4s, v20.4s, v6.4s
        ldr     d17, [x8, #1856]
        sshr    v4.4s, v4.4s, #16
        add     x8, x0, #0xc0
        smull   v16.4s, v18.4h, v16.4h
        mul     v2.4s, v2.4s, v0.4s
        mul     v4.4s, v4.4s, v0.4s
        addhn   v18.4h, v3.4s, v5.4s
        sshr    v3.4s, v6.4s, #16
        smull   v1.4s, v1.4h, v17.4h
        addhn2  v18.8h, v2.4s, v16.4s
        mul     v0.4s, v3.4s, v0.4s
        addhn   v19.4h, v4.4s, v7.4s
        addhn2  v19.8h, v0.4s, v1.4s
        st2     {v18.8h-v19.8h}, [x8]
L8ba8:
        lsl     x9, x11, #1
        add     x10, x1, x11, lsl #3
        add     x11, x0, x11, lsl #2
        mov     w8, #0xf3010000
        add     x10, x10, #0x6
        add     x11, x11, #0x2
        mov     w12, #0xfffff2ff
        .inst   0xf000002d  // adrp x13, 0xf000
        add     x13, x13, #0x840
L8bcc:
        add     x14, x13, x9
        ldursh  w15, [x10, #-4]
        add     x9, x9, #0x2
        cmp     x9, #0x80
        ldrsh   w14, [x14, #128]
        mul     w15, w14, w15
        neg     w14, w14
        sxth    w14, w14
        mul     w16, w15, w8
        asr     w16, w16, #16
        madd    w15, w16, w12, w15
        lsr     w15, w15, #16
        sturh   w15, [x11, #-2]
        ldrsh   w15, [x10]
        add     x10, x10, #0x8
        mul     w14, w15, w14
        mul     w15, w14, w8
        asr     w15, w15, #16
        madd    w14, w15, w12, w14
        lsr     w14, w14, #16
        strh    w14, [x11], #4
        b.ne    L8bcc
        ret

// mlkem_poly_ntt (0x1844 bytes)
L8c28:
        sub     sp, sp, #0x1b0
        stp     d15, d14, [sp, #352]
        stp     d13, d12, [sp, #368]
        stp     d11, d10, [sp, #384]
        stp     d9, d8, [sp, #400]
        str     x29, [sp, #416]
        ldp     q1, q2, [x0, #256]
        mov     w10, #0x7b0a0000
        mov     w9, #0xfd0a
        mvni    v0.4s, #0xd, lsl #8
        mov     x8, xzr
        dup     v18.4s, w10
        dup     v17.8h, w9
        sxtl    v3.4s, v1.4h
        mov     w9, #0x39990000
        sxtl2   v4.4s, v1.8h
        mov     w10, #0xfe99
        mul     v3.4s, v3.4s, v18.4s
        mul     v4.4s, v4.4s, v18.4s
        sxtl    v6.4s, v2.4h
        smull2  v5.4s, v1.8h, v17.8h
        sshr    v3.4s, v3.4s, #16
        smull   v1.4s, v1.4h, v17.4h
        sshr    v4.4s, v4.4s, #16
        mul     v6.4s, v6.4s, v18.4s
        mul     v3.4s, v3.4s, v0.4s
        sxtl2   v7.4s, v2.8h
        ldp     q19, q20, [x0, #288]
        mul     v7.4s, v7.4s, v18.4s
        sshr    v6.4s, v6.4s, #16
        mul     v4.4s, v4.4s, v0.4s
        addhn   v3.4h, v3.4s, v1.4s
        smull2  v16.4s, v2.8h, v17.8h
        smull   v2.4s, v2.4h, v17.4h
        mul     v6.4s, v6.4s, v0.4s
        sshr    v7.4s, v7.4s, #16
        addhn2  v3.8h, v4.4s, v5.4s
        sxtl    v4.4s, v19.4h
        mul     v1.4s, v7.4s, v0.4s
        mul     v4.4s, v4.4s, v18.4s
        str     q3, [sp, #288]
        addhn   v3.4h, v6.4s, v2.4s
        sxtl2   v5.4s, v19.8h
        smull2  v6.4s, v19.8h, v17.8h
        mul     v2.4s, v5.4s, v18.4s
        addhn2  v3.8h, v1.4s, v16.4s
        sshr    v1.4s, v4.4s, #16
        smull   v4.4s, v19.4h, v17.4h
        mul     v1.4s, v1.4s, v0.4s
        str     q3, [sp, #32]
        sshr    v2.4s, v2.4s, #16
        smull2  v16.4s, v20.8h, v17.8h
        mul     v7.4s, v2.4s, v0.4s
        addhn   v2.4h, v1.4s, v4.4s
        sxtl2   v4.4s, v20.8h
        sxtl    v1.4s, v20.4h
        mul     v4.4s, v4.4s, v18.4s
        smull   v5.4s, v20.4h, v17.4h
        ldp     q19, q20, [x0, #320]
        mul     v1.4s, v1.4s, v18.4s
        sshr    v4.4s, v4.4s, #16
        addhn2  v2.8h, v7.4s, v6.4s
        sxtl    v21.4s, v19.4h
        mul     v22.4s, v4.4s, v0.4s
        mul     v4.4s, v21.4s, v18.4s
        sshr    v1.4s, v1.4s, #16
        sxtl2   v21.4s, v19.8h
        mul     v1.4s, v1.4s, v0.4s
        mul     v21.4s, v21.4s, v18.4s
        sshr    v4.4s, v4.4s, #16
        smull   v23.4s, v19.4h, v17.4h
        mul     v4.4s, v4.4s, v0.4s
        addhn   v5.4h, v1.4s, v5.4s
        sshr    v1.4s, v21.4s, #16
        smull2  v19.4s, v19.8h, v17.8h
        mul     v1.4s, v1.4s, v0.4s
        addhn   v3.4h, v4.4s, v23.4s
        sxtl    v6.4s, v20.4h
        addhn2  v5.8h, v22.4s, v16.4s
        mul     v6.4s, v6.4s, v18.4s
        addhn2  v3.8h, v1.4s, v19.4s
        sxtl2   v1.4s, v20.8h
        stp     q2, q5, [sp, #144]
        smull2  v16.4s, v20.8h, v17.8h
        mul     v1.4s, v1.4s, v18.4s
        str     q3, [sp, #224]
        smull   v7.4s, v20.4h, v17.4h
        ldp     q19, q20, [x0, #352]
        sshr    v6.4s, v6.4s, #16
        sshr    v1.4s, v1.4s, #16
        mul     v6.4s, v6.4s, v0.4s
        sxtl    v21.4s, v19.4h
        mul     v1.4s, v1.4s, v0.4s
        mul     v21.4s, v21.4s, v18.4s
        addhn   v2.4h, v6.4s, v7.4s
        sxtl2   v22.4s, v19.8h
        smull2  v23.4s, v20.8h, v17.8h
        addhn2  v2.8h, v1.4s, v16.4s
        sshr    v1.4s, v21.4s, #16
        smull   v16.4s, v19.4h, v17.4h
        mul     v1.4s, v1.4s, v0.4s
        str     q2, [sp, #128]
        mul     v6.4s, v22.4s, v18.4s
        ldp     q22, q24, [x0, #384]
        smull2  v19.4s, v19.8h, v17.8h
        addhn   v2.4h, v1.4s, v16.4s
        sxtl2   v16.4s, v20.8h
        sxtl    v1.4s, v20.4h
        mul     v16.4s, v16.4s, v18.4s
        mul     v1.4s, v1.4s, v18.4s
        sxtl    v25.4s, v22.4h
        smull   v20.4s, v20.4h, v17.4h
        sshr    v16.4s, v16.4s, #16
        sshr    v1.4s, v1.4s, #16
        sshr    v6.4s, v6.4s, #16
        mul     v26.4s, v16.4s, v0.4s
        mul     v16.4s, v25.4s, v18.4s
        sxtl2   v25.4s, v22.8h
        mul     v1.4s, v1.4s, v0.4s
        mul     v25.4s, v25.4s, v18.4s
        sshr    v16.4s, v16.4s, #16
        mul     v21.4s, v6.4s, v0.4s
        smull   v27.4s, v22.4h, v17.4h
        mul     v28.4s, v16.4s, v0.4s
        addhn   v3.4h, v1.4s, v20.4s
        sshr    v1.4s, v25.4s, #16
        smull2  v20.4s, v22.8h, v17.8h
        mul     v1.4s, v1.4s, v0.4s
        addhn   v22.4h, v28.4s, v27.4s
        addhn2  v2.8h, v21.4s, v19.4s
        sxtl    v19.4s, v24.4h
        addhn2  v22.8h, v1.4s, v20.4s
        mul     v19.4s, v19.4s, v18.4s
        sxtl2   v1.4s, v24.8h
        addhn2  v3.8h, v26.4s, v23.4s
        mul     v1.4s, v1.4s, v18.4s
        smull2  v20.4s, v24.8h, v17.8h
        smull   v21.4s, v24.4h, v17.4h
        stp     q2, q3, [sp, #96]
        ldp     q23, q24, [x0, #416]
        sshr    v19.4s, v19.4s, #16
        sshr    v1.4s, v1.4s, #16
        mul     v19.4s, v19.4s, v0.4s
        sxtl    v25.4s, v23.4h
        mul     v1.4s, v1.4s, v0.4s
        mul     v25.4s, v25.4s, v18.4s
        addhn   v28.4h, v19.4s, v21.4s
        sxtl2   v26.4s, v23.8h
        smull2  v21.4s, v23.8h, v17.8h
        addhn2  v28.8h, v1.4s, v20.4s
        sshr    v1.4s, v25.4s, #16
        mul     v19.4s, v26.4s, v18.4s
        smull   v20.4s, v23.4h, v17.4h
        mul     v1.4s, v1.4s, v0.4s
        ldp     q25, q26, [x0, #448]
        sshr    v19.4s, v19.4s, #16
        addhn   v10.4h, v1.4s, v20.4s
        sxtl    v20.4s, v24.4h
        mul     v23.4s, v19.4s, v0.4s
        mul     v20.4s, v20.4s, v18.4s
        sxtl    v27.4s, v25.4h
        sxtl2   v8.4s, v25.8h
        addhn2  v10.8h, v23.4s, v21.4s
        sxtl2   v21.4s, v24.8h
        sshr    v20.4s, v20.4s, #16
        mul     v21.4s, v21.4s, v18.4s
        smull2  v23.4s, v24.8h, v17.8h
        smull   v24.4s, v24.4h, v17.4h
        mul     v20.4s, v20.4s, v0.4s
        mul     v27.4s, v27.4s, v18.4s
        sshr    v21.4s, v21.4s, #16
        mul     v11.4s, v8.4s, v18.4s
        addhn   v8.4h, v20.4s, v24.4s
        sshr    v20.4s, v27.4s, #16
        mul     v21.4s, v21.4s, v0.4s
        smull   v24.4s, v25.4h, v17.4h
        mul     v20.4s, v20.4s, v0.4s
        sshr    v27.4s, v11.4s, #16
        smull2  v25.4s, v25.8h, v17.8h
        mul     v27.4s, v27.4s, v0.4s
        addhn2  v8.8h, v21.4s, v23.4s
        sxtl    v21.4s, v26.4h
        ldp     q11, q12, [x0, #480]
        addhn   v24.4h, v20.4s, v24.4s
        mul     v21.4s, v21.4s, v18.4s
        sxtl2   v23.4s, v26.8h
        addhn2  v24.8h, v27.4s, v25.4s
        sxtl    v27.4s, v11.4h
        mul     v23.4s, v23.4s, v18.4s
        sshr    v21.4s, v21.4s, #16
        mul     v27.4s, v27.4s, v18.4s
        smull2  v25.4s, v26.8h, v17.8h
        smull   v26.4s, v26.4h, v17.4h
        mul     v21.4s, v21.4s, v0.4s
        sshr    v23.4s, v23.4s, #16
        ldp     q31, q16, [x0, #128]
        sshr    v27.4s, v27.4s, #16
        mul     v23.4s, v23.4s, v0.4s
        sxtl2   v13.4s, v11.8h
        mul     v15.4s, v27.4s, v0.4s
        addhn   v27.4h, v21.4s, v26.4s
        mul     v13.4s, v13.4s, v18.4s
        add     v1.8h, v31.8h, v22.8h
        addhn2  v27.8h, v23.4s, v25.4s
        sxtl2   v23.4s, v12.8h
        add     v19.8h, v16.8h, v28.8h
        smull   v14.4s, v11.4h, v17.4h
        sshr    v21.4s, v13.4s, #16
        stp     q1, q19, [x0, #128]
        sxtl    v25.4s, v12.4h
        mul     v23.4s, v23.4s, v18.4s
        smull2  v26.4s, v11.8h, v17.8h
        mul     v11.4s, v21.4s, v0.4s
        mul     v18.4s, v25.4s, v18.4s
        smull2  v25.4s, v12.8h, v17.8h
        smull   v17.4s, v12.4h, v17.4h
        ldp     q19, q12, [x0, #128]
        addhn   v29.4h, v15.4s, v14.4s
        sshr    v23.4s, v23.4s, #16
        sshr    v1.4s, v18.4s, #16
        mul     v18.4s, v23.4s, v0.4s
        dup     v15.8h, w10
        addhn2  v29.8h, v11.4s, v26.4s
        mov     w10, #0x58e
        sxtl    v23.4s, v19.4h
        dup     v11.4s, w9
        mov     w9, #0x3130000
        ldp     q9, q7, [x0, #160]
        mul     v1.4s, v1.4s, v0.4s
        mul     v23.4s, v23.4s, v11.4s
        sxtl2   v26.4s, v19.8h
        add     v20.8h, v9.8h, v10.8h
        mul     v14.4s, v26.4s, v11.4s
        addhn   v26.4h, v1.4s, v17.4s
        sshr    v17.4s, v23.4s, #16
        add     v13.8h, v7.8h, v8.8h
        smull   v1.4s, v19.4h, v15.4h
        mul     v17.4s, v17.4s, v0.4s
        stp     q20, q13, [x0, #160]
        sshr    v20.4s, v14.4s, #16
        sxtl    v23.4s, v12.4h
        mul     v20.4s, v20.4s, v0.4s
        addhn   v0.4h, v17.4s, v1.4s
        mul     v1.4s, v23.4s, v11.4s
        addhn2  v26.8h, v18.4s, v25.4s
        ldp     q23, q25, [x0, #160]
        smull2  v19.4s, v19.8h, v15.8h
        sshr    v1.4s, v1.4s, #16
        smull   v18.4s, v12.4h, v15.4h
        smull   v13.4s, v23.4h, v15.4h
        addhn2  v0.8h, v20.4s, v19.4s
        sxtl    v19.4s, v23.4h
        sxtl    v20.4s, v25.4h
        mul     v19.4s, v19.4s, v11.4s
        str     q0, [sp, #80]
        mul     v20.4s, v20.4s, v11.4s
        mvni    v0.4s, #0xd, lsl #8
        mul     v1.4s, v1.4s, v0.4s
        sshr    v19.4s, v19.4s, #16
        sshr    v20.4s, v20.4s, #16
        mul     v19.4s, v19.4s, v0.4s
        mul     v14.4s, v20.4s, v0.4s
        smull   v0.4s, v25.4h, v15.4h
        addhn   v20.4h, v1.4s, v18.4s
        addhn   v18.4h, v19.4s, v13.4s
        sxtl2   v13.4s, v12.8h
        addhn   v5.4h, v14.4s, v0.4s
        ldp     q6, q14, [x0, #192]
        sxtl2   v0.4s, v23.8h
        mul     v13.4s, v13.4s, v11.4s
        mul     v2.4s, v0.4s, v11.4s
        add     v0.8h, v6.8h, v24.8h
        smull2  v4.4s, v12.8h, v15.8h
        add     v1.8h, v14.8h, v27.8h
        sshr    v12.4s, v13.4s, #16
        stp     q0, q1, [x0, #192]
        sshr    v3.4s, v2.4s, #16
        ldp     q1, q0, [x0, #192]
        sxtl2   v13.4s, v25.8h
        mvni    v17.4s, #0xd, lsl #8
        mul     v13.4s, v13.4s, v11.4s
        sxtl    v2.4s, v1.4h
        smull2  v23.4s, v23.8h, v15.8h
        mul     v2.4s, v2.4s, v11.4s
        sshr    v13.4s, v13.4s, #16
        mul     v3.4s, v3.4s, v17.4s
        smull2  v25.4s, v25.8h, v15.8h
        mul     v13.4s, v13.4s, v17.4s
        sshr    v2.4s, v2.4s, #16
        smull   v30.4s, v1.4h, v15.4h
        mul     v2.4s, v2.4s, v17.4s
        addhn2  v18.8h, v3.4s, v23.4s
        addhn2  v5.8h, v13.4s, v25.4s
        mul     v12.4s, v12.4s, v17.4s
        sxtl    v3.4s, v0.4h
        stp     q18, q5, [sp, #48]
        addhn   v18.4h, v2.4s, v30.4s
        sxtl2   v2.4s, v1.8h
        addhn2  v20.8h, v12.4s, v4.4s
        mul     v2.4s, v2.4s, v11.4s
        ldp     q12, q13, [x0, #224]
        smull2  v1.4s, v1.8h, v15.8h
        mul     v3.4s, v3.4s, v11.4s
        sshr    v2.4s, v2.4s, #16
        add     v4.8h, v12.8h, v29.8h
        mul     v2.4s, v2.4s, v17.4s
        add     v25.8h, v13.8h, v26.8h
        sxtl2   v30.4s, v0.8h
        stp     q4, q25, [x0, #224]
        sshr    v3.4s, v3.4s, #16
        mul     v4.4s, v30.4s, v11.4s
        smull   v30.4s, v0.4h, v15.4h
        smull2  v5.4s, v0.8h, v15.8h
        addhn2  v18.8h, v2.4s, v1.4s
        ldp     q0, q1, [x0, #224]
        mul     v3.4s, v3.4s, v17.4s
        sshr    v4.4s, v4.4s, #16
        str     q18, [sp, #16]
        mul     v4.4s, v4.4s, v17.4s
        sxtl    v2.4s, v0.4h
        addhn   v25.4h, v3.4s, v30.4s
        mul     v2.4s, v2.4s, v11.4s
        sxtl2   v3.4s, v0.8h
        addhn2  v25.8h, v4.4s, v5.4s
        mul     v3.4s, v3.4s, v11.4s
        sub     v4.8h, v31.8h, v22.8h
        sshr    v2.4s, v2.4s, #16
        sub     v5.8h, v16.8h, v28.8h
        mul     v2.4s, v2.4s, v17.4s
        stp     q4, q5, [x0, #384]
        sshr    v3.4s, v3.4s, #16
        smull   v4.4s, v0.4h, v15.4h
        smull2  v0.4s, v0.8h, v15.8h
        mul     v3.4s, v3.4s, v17.4s
        ldp     q5, q16, [x0, #384]
        addhn   v23.4h, v2.4s, v4.4s
        sub     v4.8h, v7.8h, v8.8h
        smull   v7.4s, v1.4h, v15.4h
        addhn2  v23.8h, v3.4s, v0.4s
        sxtl    v0.4s, v1.4h
        smull2  v3.4s, v1.8h, v15.8h
        mul     v0.4s, v0.4s, v11.4s
        sxtl2   v1.4s, v1.8h
        sxtl    v28.4s, v5.4h
        dup     v8.4s, w9
        mov     w9, #0xfa13
        sshr    v0.4s, v0.4s, #16
        mul     v1.4s, v1.4s, v11.4s
        mul     v0.4s, v0.4s, v17.4s
        mul     v28.4s, v28.4s, v8.4s
        sxtl2   v30.4s, v5.8h
        dup     v31.8h, w9
        mov     w9, #0x34d50000
        addhn   v22.4h, v0.4s, v7.4s
        sshr    v0.4s, v1.4s, #16
        mul     v1.4s, v30.4s, v8.4s
        sshr    v28.4s, v28.4s, #16
        sub     v2.8h, v9.8h, v10.8h
        dup     v10.4s, w9
        mul     v28.4s, v28.4s, v17.4s
        mov     w9, #0x5d5
        smull   v9.4s, v5.4h, v31.4h
        stp     q2, q4, [x0, #416]
        sshr    v1.4s, v1.4s, #16
        smull2  v2.4s, v5.8h, v31.8h
        mul     v1.4s, v1.4s, v17.4s
        addhn   v28.4h, v28.4s, v9.4s
        sxtl    v5.4s, v16.4h
        mul     v0.4s, v0.4s, v17.4s
        addhn2  v28.8h, v1.4s, v2.4s
        ldp     q4, q1, [x0, #416]
        mul     v5.4s, v5.4s, v8.4s
        addhn2  v22.8h, v0.4s, v3.4s
        sub     v3.8h, v6.8h, v24.8h
        sxtl    v2.4s, v4.4h
        sshr    v0.4s, v5.4s, #16
        mul     v2.4s, v2.4s, v8.4s
        sxtl    v6.4s, v1.4h
        mvni    v18.4s, #0xd, lsl #8
        mul     v0.4s, v0.4s, v18.4s
        smull   v5.4s, v16.4h, v31.4h
        mul     v6.4s, v6.4s, v8.4s
        sshr    v2.4s, v2.4s, #16
        smull   v30.4s, v1.4h, v31.4h
        addhn   v21.4h, v0.4s, v5.4s
        ldr     q0, [sp, #288]
        mul     v2.4s, v2.4s, v18.4s
        sshr    v5.4s, v6.4s, #16
        smull   v6.4s, v4.4h, v31.4h
        mul     v5.4s, v5.4s, v18.4s
        sub     v7.8h, v14.8h, v27.8h
        sxtl2   v24.4s, v16.8h
        addhn   v27.4h, v2.4s, v6.4s
        stp     q3, q7, [x0, #448]
        sxtl2   v6.4s, v4.8h
        mul     v2.4s, v24.4s, v8.4s
        addhn   v24.4h, v5.4s, v30.4s
        mul     v5.4s, v6.4s, v8.4s
        smull2  v3.4s, v16.8h, v31.8h
        sxtl2   v6.4s, v1.8h
        ldp     q7, q16, [x0, #448]
        mul     v6.4s, v6.4s, v8.4s
        sshr    v2.4s, v2.4s, #16
        sshr    v5.4s, v5.4s, #16
        mul     v2.4s, v2.4s, v18.4s
        sxtl    v30.4s, v7.4h
        sshr    v6.4s, v6.4s, #16
        mul     v30.4s, v30.4s, v8.4s
        smull2  v4.4s, v4.8h, v31.8h
        mul     v5.4s, v5.4s, v18.4s
        smull2  v1.4s, v1.8h, v31.8h
        mul     v6.4s, v6.4s, v18.4s
        addhn2  v21.8h, v2.4s, v3.4s
        sshr    v3.4s, v30.4s, #16
        addhn2  v27.8h, v5.4s, v4.4s
        addhn2  v24.8h, v6.4s, v1.4s
        ldp     q2, q1, [x0]
        mul     v3.4s, v3.4s, v18.4s
        smull   v5.4s, v7.4h, v31.4h
        sub     v30.8h, v13.8h, v26.8h
        sxtl2   v26.4s, v7.8h
        sub     v4.8h, v2.8h, v0.8h
        add     v2.8h, v2.8h, v0.8h
        addhn   v0.4h, v3.4s, v5.4s
        mul     v5.4s, v26.4s, v8.4s
        str     q2, [x0]
        sxtl    v3.4s, v16.4h
        sxtl2   v26.4s, v16.8h
        mul     v3.4s, v3.4s, v8.4s
        sshr    v5.4s, v5.4s, #16
        smull2  v7.4s, v7.8h, v31.8h
        mul     v26.4s, v26.4s, v8.4s
        mul     v5.4s, v5.4s, v18.4s
        sub     v6.8h, v12.8h, v29.8h
        sshr    v3.4s, v3.4s, #16
        smull   v9.4s, v16.4h, v31.4h
        stp     q6, q30, [x0, #480]
        mul     v3.4s, v3.4s, v18.4s
        sshr    v26.4s, v26.4s, #16
        addhn2  v0.8h, v5.4s, v7.4s
        dup     v29.8h, w9
        ldp     q5, q7, [x0, #480]
        smull2  v16.4s, v16.8h, v31.8h
        mov     w9, #0xcf8e0000
        mul     v11.4s, v26.4s, v18.4s
        str     q0, [sp]
        addhn   v26.4h, v3.4s, v9.4s
        sxtl    v3.4s, v5.4h
        smull   v14.4s, v5.4h, v31.4h
        ldr     q0, [sp, #32]
        addhn2  v26.8h, v11.4s, v16.4s
        ldp     q16, q30, [x0, #32]
        mul     v3.4s, v3.4s, v8.4s
        sub     v6.8h, v1.8h, v0.8h
        add     v17.8h, v1.8h, v0.8h
        stp     q4, q6, [x0, #256]
        sshr    v2.4s, v3.4s, #16
        ldp     q3, q0, [sp, #128]
        ldp     q11, q13, [x0, #64]
        mul     v2.4s, v2.4s, v18.4s
        sub     v9.8h, v16.8h, v0.8h
        add     v16.8h, v16.8h, v0.8h
        smull2  v4.4s, v5.8h, v31.8h
        smull   v6.4s, v7.4h, v31.4h
        stp     q17, q16, [x0, #16]
        ldr     q0, [sp, #160]
        sub     v12.8h, v30.8h, v0.8h
        add     v30.8h, v30.8h, v0.8h
        ldr     q0, [sp, #224]
        stp     q9, q12, [x0, #288]
        str     q30, [x0, #48]
        sub     v1.8h, v11.8h, v0.8h
        add     v15.8h, v11.8h, v0.8h
        addhn   v11.4h, v2.4s, v14.4s
        str     q1, [sp, #288]
        sxtl2   v2.4s, v5.8h
        sxtl    v0.4s, v7.4h
        mul     v2.4s, v2.4s, v8.4s
        mul     v0.4s, v0.4s, v8.4s
        sxtl2   v14.4s, v7.8h
        add     v5.8h, v13.8h, v3.8h
        sshr    v2.4s, v2.4s, #16
        sshr    v0.4s, v0.4s, #16
        stp     q15, q5, [x0, #64]
        mvni    v1.4s, #0xd, lsl #8
        mul     v8.4s, v14.4s, v8.4s
        mul     v2.4s, v2.4s, v1.4s
        mul     v0.4s, v0.4s, v1.4s
        ldp     q19, q18, [x0, #64]
        sshr    v5.4s, v8.4s, #16
        addhn2  v11.8h, v2.4s, v4.4s
        smull2  v7.4s, v7.8h, v31.8h
        addhn   v8.4h, v0.4s, v6.4s
        mul     v5.4s, v5.4s, v1.4s
        ldr     q4, [sp, #16]
        ldp     q6, q31, [x0, #96]
        add     v2.8h, v18.8h, v25.8h
        add     v0.8h, v19.8h, v4.8h
        addhn2  v8.8h, v5.4s, v7.4s
        stp     q0, q2, [x0, #64]
        sub     v5.8h, v13.8h, v3.8h
        ldr     q1, [sp, #96]
        mvni    v15.4s, #0xd, lsl #8
        sub     v0.8h, v6.8h, v1.8h
        add     v14.8h, v6.8h, v1.8h
        ldr     q1, [sp, #112]
        str     q0, [sp, #224]
        ldp     q7, q0, [x0, #64]
        sub     v2.8h, v31.8h, v1.8h
        add     v30.8h, v31.8h, v1.8h
        str     q2, [sp, #128]
        sxtl    v13.4s, v7.4h
        stp     q14, q30, [x0, #96]
        sxtl2   v17.4s, v7.8h
        mul     v6.4s, v13.4s, v10.4s
        ldr     q2, [sp, #48]
        mul     v17.4s, v17.4s, v10.4s
        smull   v16.4s, v7.4h, v29.4h
        smull2  v7.4s, v7.8h, v29.8h
        sshr    v6.4s, v6.4s, #16
        sshr    v17.4s, v17.4s, #16
        mul     v6.4s, v6.4s, v15.4s
        mul     v17.4s, v17.4s, v15.4s
        sxtl    v31.4s, v0.4h
        addhn   v13.4h, v6.4s, v16.4s
        ldp     q6, q1, [sp, #64]
        addhn2  v13.8h, v17.4s, v7.4s
        ldp     q16, q17, [x0]
        sub     v12.8h, v16.8h, v1.8h
        add     v16.8h, v16.8h, v1.8h
        ldp     q9, q1, [x0, #32]
        sub     v7.8h, v17.8h, v20.8h
        add     v17.8h, v17.8h, v20.8h
        mul     v20.4s, v31.4s, v10.4s
        stp     q12, q7, [x0, #128]
        sub     v31.8h, v9.8h, v2.8h
        stp     q16, q17, [x0]
        add     v2.8h, v9.8h, v2.8h
        sxtl2   v9.4s, v0.8h
        sshr    v20.4s, v20.4s, #16
        str     q2, [sp, #48]
        mul     v3.4s, v9.4s, v10.4s
        mul     v20.4s, v20.4s, v15.4s
        smull   v2.4s, v0.4h, v29.4h
        sub     v14.8h, v1.8h, v6.8h
        add     v9.8h, v1.8h, v6.8h
        sshr    v1.4s, v3.4s, #16
        stp     q31, q14, [x0, #160]
        smull2  v0.4s, v0.8h, v29.8h
        mul     v1.4s, v1.4s, v15.4s
        addhn   v30.4h, v20.4s, v2.4s
        sub     v2.8h, v19.8h, v4.8h
        sub     v4.8h, v18.8h, v25.8h
        addhn2  v30.8h, v1.4s, v0.4s
        ldp     q3, q0, [x0, #96]
        stp     q2, q4, [x0, #192]
        sub     v6.8h, v3.8h, v23.8h
        add     v3.8h, v3.8h, v23.8h
        add     v18.8h, v0.8h, v22.8h
        sub     v22.8h, v0.8h, v22.8h
        stp     q3, q18, [x0, #96]
        ldp     q3, q0, [x0, #256]
        stp     q6, q22, [x0, #224]
        sub     v20.8h, v3.8h, v28.8h
        add     v1.8h, v3.8h, v28.8h
        ldp     q18, q3, [x0, #96]
        str     q1, [sp, #144]
        sxtl    v25.4s, v18.4h
        sxtl2   v23.4s, v18.8h
        mul     v28.4s, v25.4s, v10.4s
        sub     v25.8h, v0.8h, v21.8h
        add     v0.8h, v0.8h, v21.8h
        mul     v23.4s, v23.4s, v10.4s
        stp     q20, q25, [x0, #384]
        str     q0, [sp, #112]
        ldr     q0, [sp, #288]
        smull2  v19.4s, v18.8h, v29.8h
        smull   v18.4s, v18.4h, v29.4h
        stp     q0, q5, [x0, #320]
        sshr    v5.4s, v28.4s, #16
        sxtl    v28.4s, v3.4h
        sshr    v23.4s, v23.4s, #16
        mul     v5.4s, v5.4s, v15.4s
        mul     v1.4s, v28.4s, v10.4s
        mul     v23.4s, v23.4s, v15.4s
        sxtl2   v0.4s, v3.8h
        addhn   v28.4h, v5.4s, v18.4s
        sshr    v1.4s, v1.4s, #16
        mul     v0.4s, v0.4s, v10.4s
        addhn2  v28.8h, v23.4s, v19.4s
        smull   v2.4s, v3.4h, v29.4h
        mul     v1.4s, v1.4s, v15.4s
        ldp     q4, q19, [x0, #288]
        sshr    v0.4s, v0.4s, #16
        smull2  v18.4s, v3.8h, v29.8h
        dup     v29.8h, w10
        addhn   v5.4h, v1.4s, v2.4s
        mov     w10, #0xfa3e
        sub     v1.8h, v4.8h, v27.8h
        add     v2.8h, v4.8h, v27.8h
        mul     v0.4s, v0.4s, v15.4s
        str     q1, [sp, #288]
        str     q2, [sp, #160]
        dup     v4.4s, w9
        ldp     q1, q2, [x0, #192]
        mov     w9, #0x6e1f0000
        addhn2  v5.8h, v0.4s, v18.4s
        sxtl    v18.4s, v1.4h
        dup     v31.4s, w9
        sxtl2   v0.4s, v1.8h
        mov     w9, #0x11f
        mul     v18.4s, v18.4s, v4.4s
        ldr     q3, [sp, #224]
        mul     v23.4s, v0.4s, v4.4s
        ldr     q0, [sp, #128]
        sxtl2   v27.4s, v2.8h
        stp     q3, q0, [x0, #352]
        sshr    v7.4s, v18.4s, #16
        sub     v0.8h, v19.8h, v24.8h
        sshr    v18.4s, v23.4s, #16
        sxtl    v23.4s, v2.4h
        str     q0, [sp, #224]
        add     v0.8h, v19.8h, v24.8h
        smull2  v19.4s, v1.8h, v29.8h
        smull   v1.4s, v1.4h, v29.4h
        str     q0, [sp, #128]
        mul     v7.4s, v7.4s, v15.4s
        ldr     q0, [sp]
        mul     v23.4s, v23.4s, v4.4s
        mul     v24.4s, v18.4s, v15.4s
        addhn   v18.4h, v7.4s, v1.4s
        mul     v1.4s, v27.4s, v4.4s
        sshr    v6.4s, v23.4s, #16
        smull   v7.4s, v2.4h, v29.4h
        mul     v6.4s, v6.4s, v15.4s
        sshr    v1.4s, v1.4s, #16
        addhn2  v18.8h, v24.4s, v19.4s
        ldp     q22, q23, [x0, #320]
        smull2  v24.4s, v2.8h, v29.8h
        mul     v1.4s, v1.4s, v15.4s
        addhn   v19.4h, v6.4s, v7.4s
        sub     v2.8h, v22.8h, v0.8h
        add     v6.8h, v22.8h, v0.8h
        addhn2  v19.8h, v1.4s, v24.4s
        ldp     q22, q24, [x0, #224]
        sub     v0.8h, v23.8h, v26.8h
        add     v21.8h, v23.8h, v26.8h
        stp     q2, q0, [x0, #448]
        sxtl    v27.4s, v22.4h
        stp     q6, q21, [x0, #320]
        sxtl2   v23.4s, v22.8h
        ldp     q1, q7, [x0, #352]
        mul     v10.4s, v27.4s, v4.4s
        mul     v23.4s, v23.4s, v4.4s
        smull2  v16.4s, v22.8h, v29.8h
        smull   v22.4s, v22.4h, v29.4h
        sshr    v17.4s, v10.4s, #16
        sub     v27.8h, v7.8h, v8.8h
        sshr    v23.4s, v23.4s, #16
        add     v7.8h, v7.8h, v8.8h
        sxtl    v8.4s, v24.4h
        mul     v17.4s, v17.4s, v15.4s
        mul     v8.4s, v8.4s, v4.4s
        sub     v26.8h, v1.8h, v11.8h
        add     v1.8h, v1.8h, v11.8h
        sxtl2   v11.4s, v24.8h
        stp     q26, q27, [x0, #480]
        mul     v10.4s, v23.4s, v15.4s
        stp     q1, q7, [x0, #352]
        addhn   v23.4h, v17.4s, v22.4s
        mul     v4.4s, v11.4s, v4.4s
        sshr    v6.4s, v8.4s, #16
        addhn2  v23.8h, v10.4s, v16.4s
        dup     v11.8h, w9
        smull   v16.4s, v24.4h, v29.4h
        mov     w9, #0xbeca0000
        mul     v6.4s, v6.4s, v15.4s
        sshr    v4.4s, v4.4s, #16
        smull2  v22.4s, v24.8h, v29.8h
        dup     v0.4s, w9
        ldp     q21, q29, [x0]
        mul     v4.4s, v4.4s, v15.4s
        mov     w9, #0xae550000
        addhn   v24.4h, v6.4s, v16.4s
        movi    v16.4h, #0xca
        sub     v6.8h, v21.8h, v13.8h
        add     v3.8h, v21.8h, v13.8h
        addhn2  v24.8h, v4.4s, v22.4s
        stp     q6, q3, [sp, #80]
        ldr     q3, [sp, #48]
        ldp     q6, q4, [x0, #320]
        stp     q3, q9, [x0, #32]
        add     v3.8h, v29.8h, v30.8h
        sxtl    v21.4s, v6.4h
        sxtl2   v8.4s, v6.8h
        str     q3, [sp, #64]
        mul     v10.4s, v21.4s, v31.4s
        ldr     q3, [sp, #112]
        mul     v8.4s, v8.4s, v31.4s
        sub     v21.8h, v29.8h, v30.8h
        smull   v30.4s, v6.4h, v11.4h
        sshr    v29.4s, v10.4s, #16
        sshr    v1.4s, v8.4s, #16
        mul     v29.4s, v29.4s, v15.4s
        sxtl    v7.4s, v4.4h
        smull2  v6.4s, v6.8h, v11.8h
        mul     v1.4s, v1.4s, v15.4s
        mul     v7.4s, v7.4s, v31.4s
        addhn   v10.4h, v29.4s, v30.4s
        sxtl2   v29.4s, v4.8h
        mul     v29.4s, v29.4s, v31.4s
        addhn2  v10.8h, v1.4s, v6.4s
        sshr    v6.4s, v7.4s, #16
        ldp     q7, q30, [x0, #352]
        smull2  v1.4s, v4.8h, v11.8h
        sshr    v29.4s, v29.4s, #16
        smull   v4.4s, v4.4h, v11.4h
        mul     v6.4s, v6.4s, v15.4s
        sxtl    v8.4s, v7.4h
        mul     v29.4s, v29.4s, v15.4s
        mul     v8.4s, v8.4s, v31.4s
        sxtl2   v12.4s, v7.8h
        addhn   v9.4h, v6.4s, v4.4s
        mul     v4.4s, v12.4s, v31.4s
        smull   v6.4s, v7.4h, v11.4h
        addhn2  v9.8h, v29.4s, v1.4s
        sshr    v1.4s, v8.4s, #16
        sshr    v4.4s, v4.4s, #16
        mul     v1.4s, v1.4s, v15.4s
        smull2  v7.4s, v7.8h, v11.8h
        mul     v4.4s, v4.4s, v15.4s
        ldp     q29, q13, [x0, #32]
        addhn   v20.4h, v1.4s, v6.4s
        sxtl2   v1.4s, v30.8h
        smull2  v6.4s, v30.8h, v11.8h
        addhn2  v20.8h, v4.4s, v7.4s
        sxtl    v4.4s, v30.4h
        mul     v1.4s, v1.4s, v31.4s
        sub     v25.8h, v29.8h, v28.8h
        add     v8.8h, v29.8h, v28.8h
        mul     v4.4s, v4.4s, v31.4s
        ldp     q7, q29, [x0, #448]
        sshr    v1.4s, v1.4s, #16
        smull   v2.4s, v30.4h, v11.4h
        mul     v28.4s, v1.4s, v15.4s
        sshr    v1.4s, v4.4s, #16
        sxtl    v4.4s, v7.4h
        mul     v1.4s, v1.4s, v15.4s
        mul     v30.4s, v4.4s, v0.4s
        ldr     q4, [sp, #144]
        sub     v22.8h, v13.8h, v5.8h
        add     v5.8h, v13.8h, v5.8h
        stp     q25, q22, [x0, #96]
        stp     q8, q5, [x0, #32]
        stp     q4, q3, [x0, #256]
        addhn   v3.4h, v1.4s, v2.4s
        sshr    v2.4s, v30.4s, #16
        smull   v30.4s, v7.4h, v16.4h
        ldr     q1, [sp, #128]
        mul     v2.4s, v2.4s, v15.4s
        addhn2  v3.8h, v28.4s, v6.4s
        sxtl2   v28.4s, v29.8h
        sxtl2   v6.4s, v7.8h
        addhn   v12.4h, v2.4s, v30.4s
        sxtl    v2.4s, v29.4h
        mul     v26.4s, v28.4s, v0.4s
        mul     v2.4s, v2.4s, v0.4s
        movi    v4.8h, #0xca
        mul     v6.4s, v6.4s, v0.4s
        smull   v28.4s, v29.4h, v16.4h
        sshr    v2.4s, v2.4s, #16
        sshr    v26.4s, v26.4s, #16
        mul     v2.4s, v2.4s, v15.4s
        sshr    v6.4s, v6.4s, #16
        smull2  v27.4s, v29.8h, v4.8h
        mul     v29.4s, v26.4s, v15.4s
        smull2  v7.4s, v7.8h, v4.8h
        addhn   v26.4h, v2.4s, v28.4s
        mul     v6.4s, v6.4s, v15.4s
        addhn2  v26.8h, v29.4s, v27.4s
        ldp     q2, q27, [x0, #480]
        addhn2  v12.8h, v6.4s, v7.4s
        sxtl    v7.4s, v2.4h
        ldp     q28, q6, [x0, #128]
        mul     v29.4s, v7.4s, v0.4s
        smull   v5.4s, v27.4h, v16.4h
        sub     v30.8h, v28.8h, v18.8h
        add     v17.8h, v28.8h, v18.8h
        sxtl2   v18.4s, v2.8h
        ldr     q7, [sp, #160]
        sshr    v28.4s, v29.4s, #16
        mul     v18.4s, v18.4s, v0.4s
        mul     v28.4s, v28.4s, v15.4s
        stp     q7, q1, [x0, #288]
        smull   v29.4s, v2.4h, v16.4h
        sub     v13.8h, v6.8h, v19.8h
        add     v11.8h, v6.8h, v19.8h
        sshr    v6.4s, v18.4s, #16
        stp     q30, q13, [x0, #192]
        smull2  v2.4s, v2.8h, v4.8h
        stp     q17, q11, [x0, #128]
        mul     v6.4s, v6.4s, v15.4s
        addhn   v7.4h, v28.4s, v29.4s
        ldp     q18, q19, [x0, #160]
        smull2  v4.4s, v27.8h, v4.8h
        addhn2  v7.8h, v6.4s, v2.4s
        sub     v28.8h, v18.8h, v23.8h
        add     v14.8h, v18.8h, v23.8h
        ldp     q2, q6, [x0, #256]
        sxtl2   v18.4s, v27.8h
        sub     v31.8h, v19.8h, v24.8h
        add     v19.8h, v19.8h, v24.8h
        sub     v29.8h, v2.8h, v10.8h
        stp     q28, q31, [x0, #224]
        add     v23.8h, v2.8h, v10.8h
        stp     q14, q19, [x0, #160]
        sxtl    v2.4s, v27.4h
        sub     v8.8h, v6.8h, v9.8h
        mul     v2.4s, v2.4s, v0.4s
        mul     v0.4s, v18.4s, v0.4s
        stp     q29, q8, [x0, #320]
        add     v10.8h, v6.8h, v9.8h
        ldp     q6, q16, [x0, #288]
        sshr    v2.4s, v2.4s, #16
        stp     q23, q10, [x0, #256]
        sshr    v0.4s, v0.4s, #16
        mul     v2.4s, v2.4s, v15.4s
        mul     v0.4s, v0.4s, v15.4s
        add     v1.8h, v6.8h, v20.8h
        sub     v27.8h, v16.8h, v3.8h
        addhn   v2.4h, v2.4s, v5.4s
        sub     v5.8h, v6.8h, v20.8h
        dup     v6.4s, w9
        mov     w9, #0x6c6e0000
        stp     q5, q1, [sp, #144]
        ldp     q5, q1, [x0, #32]
        addhn2  v2.8h, v0.4s, v4.4s
        add     v24.8h, v16.8h, v3.8h
        mvni    v16.4h, #0xaa
        sxtl2   v20.4s, v5.8h
        ldr     q4, [sp, #288]
        ldr     q0, [sp, #224]
        mul     v3.4s, v20.4s, v6.4s
        ldr     q19, [sp, #144]
        smull   v20.4s, v5.4h, v16.4h
        stp     q4, q0, [x0, #416]
        ldr     q0, [sp, #80]
        sxtl    v4.4s, v5.4h
        stp     q19, q27, [x0, #352]
        sshr    v3.4s, v3.4s, #16
        mul     v4.4s, v4.4s, v6.4s
        stp     q0, q21, [x0, #64]
        ldr     q0, [sp, #96]
        mvni    v21.8h, #0xaa
        smull2  v5.4s, v5.8h, v21.8h
        sshr    v4.4s, v4.4s, #16
        str     q0, [x0]
        ldr     q0, [sp, #64]
        mul     v4.4s, v4.4s, v15.4s
        mul     v3.4s, v3.4s, v15.4s
        str     q0, [x0, #16]
        ldp     q9, q0, [x0, #384]
        addhn   v4.4h, v4.4s, v20.4s
        sub     v18.8h, v9.8h, v12.8h
        add     v20.8h, v9.8h, v12.8h
        addhn2  v4.8h, v3.4s, v5.4s
        sub     v9.8h, v0.8h, v26.8h
        add     v12.8h, v0.8h, v26.8h
        ldp     q5, q0, [x0, #416]
        sxtl    v26.4s, v1.4h
        stp     q20, q12, [x0, #384]
        stp     q18, q9, [x0, #448]
        mvni    v9.4s, #0xd, lsl #8
        sub     v3.8h, v5.8h, v7.8h
        add     v5.8h, v5.8h, v7.8h
        sxtl2   v7.4s, v1.8h
        str     q5, [sp, #288]
        mul     v5.4s, v26.4s, v6.4s
        sub     v26.8h, v0.8h, v2.8h
        add     v2.8h, v0.8h, v2.8h
        mul     v0.4s, v7.4s, v6.4s
        stp     q3, q26, [x0, #480]
        sshr    v5.4s, v5.4s, #16
        smull   v6.4s, v1.4h, v16.4h
        mul     v5.4s, v5.4s, v15.4s
        sshr    v0.4s, v0.4s, #16
        smull2  v1.4s, v1.8h, v21.8h
        mul     v0.4s, v0.4s, v15.4s
        addhn   v6.4h, v5.4s, v6.4s
        ldp     q7, q21, [x0]
        addhn2  v6.8h, v0.4s, v1.4s
        sub     v5.8h, v7.8h, v4.8h
        add     v4.8h, v7.8h, v4.8h
        ldp     q22, q0, [x0, #96]
        dup     v7.4s, w9
        mov     w9, #0x26e
        sub     v16.8h, v21.8h, v6.8h
        sxtl    v1.4s, v22.4h
        dup     v25.8h, w9
        sxtl2   v17.4s, v22.8h
        mov     w9, #0xf1290000
        mul     v1.4s, v1.4s, v7.4s
        stp     q5, q16, [x0, #32]
        mul     v17.4s, v17.4s, v7.4s
        smull   v30.4s, v22.4h, v25.4h
        smull2  v22.4s, v22.8h, v25.8h
        sshr    v1.4s, v1.4s, #16
        sshr    v17.4s, v17.4s, #16
        dup     v31.4s, w9
        mul     v1.4s, v1.4s, v15.4s
        mov     w9, #0x629
        mul     v11.4s, v17.4s, v15.4s
        add     v17.8h, v21.8h, v6.8h
        sxtl2   v21.4s, v0.8h
        addhn   v1.4h, v1.4s, v30.4s
        stp     q4, q17, [x0]
        sxtl    v30.4s, v0.4h
        mul     v21.4s, v21.4s, v7.4s
        mul     v6.4s, v30.4s, v7.4s
        addhn2  v1.8h, v11.4s, v22.4s
        smull   v22.4s, v0.4h, v25.4h
        smull2  v0.4s, v0.8h, v25.8h
        sshr    v6.4s, v6.4s, #16
        dup     v8.8h, w9
        sshr    v21.4s, v21.4s, #16
        mul     v6.4s, v6.4s, v15.4s
        mov     w9, #0xc2b60000
        mul     v21.4s, v21.4s, v15.4s
        ldp     q30, q11, [x0, #64]
        dup     v13.4s, w9
        mov     w9, #0x29c20000
        addhn   v6.4h, v6.4s, v22.4s
        sub     v7.8h, v30.8h, v1.8h
        addhn2  v6.8h, v21.4s, v0.4s
        ldp     q25, q22, [x0, #160]
        sub     v0.8h, v11.8h, v6.8h
        sxtl    v28.4s, v25.4h
        stp     q7, q0, [x0, #96]
        sxtl2   v29.4s, v25.8h
        mul     v28.4s, v28.4s, v31.4s
        mul     v29.4s, v29.4s, v31.4s
        smull   v23.4s, v25.4h, v8.4h
        smull2  v25.4s, v25.8h, v8.8h
        sshr    v28.4s, v28.4s, #16
        sshr    v29.4s, v29.4s, #16
        mul     v28.4s, v28.4s, v15.4s
        mul     v29.4s, v29.4s, v15.4s
        sxtl    v21.4s, v22.4h
        addhn   v10.4h, v28.4s, v23.4s
        mul     v21.4s, v21.4s, v31.4s
        add     v23.8h, v30.8h, v1.8h
        addhn2  v10.8h, v29.4s, v25.4s
        sxtl2   v29.4s, v22.8h
        smull2  v30.4s, v22.8h, v8.8h
        mul     v29.4s, v29.4s, v31.4s
        smull   v22.4s, v22.4h, v8.4h
        ldp     q31, q8, [x0, #224]
        sshr    v21.4s, v21.4s, #16
        add     v25.8h, v11.8h, v6.8h
        sshr    v29.4s, v29.4s, #16
        mul     v21.4s, v21.4s, v15.4s
        sxtl    v11.4s, v31.4h
        stp     q23, q25, [x0, #64]
        mul     v29.4s, v29.4s, v15.4s
        ldp     q1, q6, [x0, #128]
        mul     v11.4s, v11.4s, v13.4s
        addhn   v21.4h, v21.4s, v22.4s
        movi    v22.4h, #0xb6
        sub     v28.8h, v1.8h, v10.8h
        add     v19.8h, v1.8h, v10.8h
        ldr     q1, [sp, #160]
        sxtl2   v27.4s, v31.8h
        addhn2  v21.8h, v29.4s, v30.4s
        stp     q1, q24, [x0, #288]
        sshr    v1.4s, v11.4s, #16
        smull   v24.4s, v31.4h, v22.4h
        mul     v1.4s, v1.4s, v15.4s
        sxtl    v30.4s, v8.4h
        mul     v27.4s, v27.4s, v13.4s
        mul     v30.4s, v30.4s, v13.4s
        movi    v29.8h, #0xb6
        addhn   v1.4h, v1.4s, v24.4s
        sxtl2   v24.4s, v8.8h
        sshr    v27.4s, v27.4s, #16
        mul     v10.4s, v24.4s, v13.4s
        sshr    v18.4s, v30.4s, #16
        smull2  v31.4s, v31.8h, v29.8h
        mul     v27.4s, v27.4s, v9.4s
        smull   v22.4s, v8.4h, v22.4h
        mul     v18.4s, v18.4s, v9.4s
        sshr    v20.4s, v10.4s, #16
        smull2  v29.4s, v8.8h, v29.8h
        mul     v20.4s, v20.4s, v9.4s
        addhn2  v1.8h, v27.4s, v31.4s
        ldp     q30, q27, [x0, #288]
        addhn   v22.4h, v18.4s, v22.4s
        sub     v24.8h, v6.8h, v21.8h
        add     v18.8h, v6.8h, v21.8h
        addhn2  v22.8h, v20.4s, v29.4s
        stp     q28, q24, [x0, #160]
        sxtl    v6.4s, v30.4h
        stp     q19, q18, [x0, #128]
        dup     v29.4s, w9
        mov     w9, #0x3c2
        ldp     q20, q31, [x0, #192]
        mul     v8.4s, v6.4s, v29.4s
        sxtl2   v9.4s, v30.8h
        mvni    v10.4s, #0xd, lsl #8
        sub     v21.8h, v20.8h, v1.8h
        add     v20.8h, v20.8h, v1.8h
        dup     v1.8h, w9
        mov     w9, #0x54e0000
        sshr    v3.4s, v8.4s, #16
        sub     v6.8h, v31.8h, v22.8h
        smull   v26.4s, v30.4h, v1.4h
        mul     v8.4s, v3.4s, v10.4s
        stp     q21, q6, [x0, #224]
        add     v3.8h, v31.8h, v22.8h
        mul     v22.4s, v9.4s, v29.4s
        ldr     q9, [sp, #288]
        sxtl    v31.4s, v27.4h
        stp     q20, q3, [x0, #192]
        addhn   v26.4h, v8.4s, v26.4s
        sxtl2   v8.4s, v27.8h
        stp     q9, q2, [x0, #416]
        sshr    v22.4s, v22.4s, #16
        mul     v31.4s, v31.4s, v29.4s
        mul     v2.4s, v8.4s, v29.4s
        smull2  v29.4s, v30.8h, v1.8h
        mul     v22.4s, v22.4s, v10.4s
        sshr    v5.4s, v31.4s, #16
        smull   v16.4s, v27.4h, v1.4h
        sshr    v2.4s, v2.4s, #16
        mul     v5.4s, v5.4s, v10.4s
        addhn2  v26.8h, v22.4s, v29.4s
        ldp     q17, q22, [x0, #352]
        smull2  v4.4s, v27.8h, v1.8h
        dup     v27.4s, w9
        mul     v2.4s, v2.4s, v10.4s
        mov     w9, #0xfb4e
        addhn   v16.4h, v5.4s, v16.4s
        sxtl    v1.4s, v17.4h
        dup     v0.8h, w9
        mov     w9, #0xd43e0000
        mul     v31.4s, v1.4s, v27.4s
        addhn2  v16.8h, v2.4s, v4.4s
        smull   v4.4s, v17.4h, v0.4h
        sxtl2   v7.4s, v17.8h
        sshr    v2.4s, v31.4s, #16
        mul     v7.4s, v7.4s, v27.4s
        dup     v18.4s, w9
        mul     v2.4s, v2.4s, v10.4s
        mov     w9, #0x79bc0000
        ldp     q29, q30, [x0, #256]
        mvni    v23.4s, #0xd, lsl #8
        sshr    v7.4s, v7.4s, #16
        addhn   v2.4h, v2.4s, v4.4s
        sxtl    v4.4s, v22.4h
        sub     v5.8h, v29.8h, v26.8h
        mul     v4.4s, v4.4s, v27.4s
        add     v1.8h, v29.8h, v26.8h
        sxtl2   v26.4s, v22.8h
        smull2  v17.4s, v17.8h, v0.8h
        mul     v7.4s, v7.4s, v23.4s
        smull2  v29.4s, v22.8h, v0.8h
        smull   v0.4s, v22.4h, v0.4h
        mul     v22.4s, v26.4s, v27.4s
        sshr    v4.4s, v4.4s, #16
        addhn2  v2.8h, v7.4s, v17.4s
        mul     v4.4s, v4.4s, v23.4s
        ldp     q7, q17, [x0, #416]
        sshr    v22.4s, v22.4s, #16
        mvni    v25.4s, #0xd, lsl #8
        mul     v22.4s, v22.4s, v23.4s
        addhn   v4.4h, v4.4s, v0.4s
        sxtl    v19.4s, v7.4h
        dup     v23.8h, w10
        mov     w10, #0xf3010000
        mul     v19.4s, v19.4s, v18.4s
        addhn2  v4.8h, v22.4s, v29.4s
        sxtl2   v22.4s, v7.8h
        sxtl    v21.4s, v17.4h
        mul     v22.4s, v22.4s, v18.4s
        sshr    v19.4s, v19.4s, #16
        smull2  v24.4s, v7.8h, v23.8h
        smull   v7.4s, v7.4h, v23.4h
        mul     v19.4s, v19.4s, v25.4s
        sshr    v6.4s, v22.4s, #16
        mul     v21.4s, v21.4s, v18.4s
        sxtl2   v22.4s, v17.8h
        mul     v6.4s, v6.4s, v25.4s
        addhn   v7.4h, v19.4s, v7.4s
        mul     v18.4s, v22.4s, v18.4s
        sshr    v3.4s, v21.4s, #16
        addhn2  v7.8h, v6.4s, v24.4s
        smull   v6.4s, v17.4h, v23.4h
        mul     v3.4s, v3.4s, v25.4s
        sub     v0.8h, v30.8h, v16.8h
        sshr    v18.4s, v18.4s, #16
        smull2  v17.4s, v17.8h, v23.8h
        stp     q5, q0, [x0, #288]
        mul     v18.4s, v18.4s, v25.4s
        ldp     q21, q0, [x0, #480]
        addhn   v3.4h, v3.4s, v6.4s
        add     v16.8h, v30.8h, v16.8h
        addhn2  v3.8h, v18.4s, v17.4s
        dup     v17.4s, w9
        sxtl    v5.4s, v21.4h
        mov     w9, #0x5bc
        ldp     q19, q20, [x0, #320]
        mul     v5.4s, v5.4s, v17.4s
        stp     q1, q16, [x0, #256]
        sxtl2   v18.4s, v21.8h
        dup     v1.8h, w9
        .inst   0xd0000029  // adrp x9, 0xf000
        add     x9, x9, #0x840
        mul     v18.4s, v18.4s, v17.4s
        sshr    v5.4s, v5.4s, #16
        sub     v6.8h, v19.8h, v2.8h
        sub     v16.8h, v20.8h, v4.8h
        add     v2.8h, v19.8h, v2.8h
        smull   v19.4s, v21.4h, v1.4h
        stp     q6, q16, [x0, #352]
        mul     v5.4s, v5.4s, v25.4s
        sshr    v6.4s, v18.4s, #16
        smull2  v16.4s, v21.8h, v1.8h
        mul     v6.4s, v6.4s, v25.4s
        add     v4.8h, v20.8h, v4.8h
        addhn   v5.4h, v5.4s, v19.4s
        sxtl    v18.4s, v0.4h
        stp     q2, q4, [x0, #320]
        ldp     q19, q2, [x0, #384]
        mul     v18.4s, v18.4s, v17.4s
        addhn2  v5.8h, v6.4s, v16.4s
        sxtl2   v6.4s, v0.8h
        sub     v4.8h, v19.8h, v7.8h
        mul     v6.4s, v6.4s, v17.4s
        sshr    v16.4s, v18.4s, #16
        sub     v17.8h, v2.8h, v3.8h
        smull   v18.4s, v0.4h, v1.4h
        mul     v16.4s, v16.4s, v25.4s
        stp     q4, q17, [x0, #416]
        sshr    v4.4s, v6.4s, #16
        mvni    v17.4s, #0xd, lsl #8
        smull2  v0.4s, v0.8h, v1.8h
        mul     v1.4s, v4.4s, v17.4s
        addhn   v4.4h, v16.4s, v18.4s
        add     v6.8h, v19.8h, v7.8h
        add     v2.8h, v2.8h, v3.8h
        addhn2  v4.8h, v1.4s, v0.4s
        ldp     q0, q1, [x0, #448]
        stp     q6, q2, [x0, #384]
        sub     v2.8h, v0.8h, v5.8h
        add     v0.8h, v0.8h, v5.8h
        sub     v3.8h, v1.8h, v4.8h
        add     v1.8h, v1.8h, v4.8h
        stp     q2, q3, [x0, #480]
        stp     q0, q1, [x0, #448]
L9e40:
        add     x12, x0, x8, lsl #4
        add     x11, x9, x8
        dup     v4.4s, w10
        add     x8, x8, #0x2
        cmp     x8, #0x20
        ldp     q1, q0, [x12]
        ldrsh   w11, [x11, #32]
        sxtl    v2.4s, v0.4h
        sxtl2   v0.4s, v0.8h
        dup     v3.4s, w11
        mul     v2.4s, v3.4s, v2.4s
        mul     v0.4s, v3.4s, v0.4s
        mul     v3.4s, v2.4s, v4.4s
        mul     v4.4s, v0.4s, v4.4s
        sshr    v3.4s, v3.4s, #16
        sshr    v4.4s, v4.4s, #16
        mul     v3.4s, v3.4s, v17.4s
        mul     v4.4s, v4.4s, v17.4s
        addhn   v2.4h, v3.4s, v2.4s
        addhn2  v2.8h, v4.4s, v0.4s
        sub     v0.8h, v1.8h, v2.8h
        add     v1.8h, v1.8h, v2.8h
        stp     q1, q0, [x12]
        b.ne    L9e40
        mov     w10, #0xf3010000
        mov     x8, xzr
        mvni    v1.4s, #0xd, lsl #8
        dup     v0.4s, w10
L9eb0:
        add     x10, x9, x8
        add     x11, x0, x8, lsl #3
        add     x10, x10, #0x40
        add     x8, x8, #0x2
        cmp     x8, #0x40
        ldp     d4, d3, [x11]
        ld1r    {v2.4h}, [x10]
        smull   v2.4s, v2.4h, v3.4h
        mul     v3.4s, v2.4s, v0.4s
        sshr    v3.4s, v3.4s, #16
        mul     v3.4s, v3.4s, v1.4s
        addhn   v2.4h, v3.4s, v2.4s
        sub     v3.4h, v4.4h, v2.4h
        add     v2.4h, v4.4h, v2.4h
        stp     d2, d3, [x11]
        b.ne    L9eb0
        ld4     {v1.8h-v4.8h}, [x0]
        .inst   0xd000002b  // adrp x11, 0xf000
        .inst   0xd0000029  // adrp x9, 0xf000
        .inst   0xd000002a  // adrp x10, 0xf000
        .inst   0xd0000028  // adrp x8, 0xf000
        .inst   0xd000002d  // adrp x13, 0xf000
        mvni    v14.4s, #0xd, lsl #8
        .inst   0xd000002c  // adrp x12, 0xf000
        .inst   0xd000002e  // adrp x14, 0xf000
        .inst   0xd000002f  // adrp x15, 0xf000
        .inst   0xd0000030  // adrp x16, 0xf000
        ldr     q16, [x11, #1072]
        .inst   0xd000002b  // adrp x11, 0xf000
        ldr     d6, [x9, #1656]
        add     x9, x0, #0x80
        ldr     q7, [x10, #1056]
        .inst   0xd000002a  // adrp x10, 0xf000
        sxtl    v17.4s, v3.4h
        ldr     d5, [x8, #1648]
        sxtl    v21.4s, v4.4h
        mov     x8, x0
        mul     v17.4s, v17.4s, v16.4s
        sxtl2   v18.4s, v3.8h
        mul     v16.4s, v21.4s, v16.4s
        smull   v20.4s, v3.4h, v6.4h
        sxtl2   v22.4s, v4.8h
        smull   v24.4s, v4.4h, v6.4h
        mul     v6.4s, v18.4s, v7.4s
        ext     v19.16b, v3.16b, v3.16b, #8
        sshr    v17.4s, v17.4s, #16
        mul     v7.4s, v22.4s, v7.4s
        sshr    v16.4s, v16.4s, #16
        mul     v17.4s, v17.4s, v14.4s
        ext     v23.16b, v4.16b, v4.16b, #8
        sshr    v6.4s, v6.4s, #16
        smull   v18.4s, v19.4h, v5.4h
        sshr    v7.4s, v7.4s, #16
        mul     v19.4s, v16.4s, v14.4s
        mul     v21.4s, v6.4s, v14.4s
        addhn   v6.4h, v17.4s, v20.4s
        smull   v5.4s, v23.4h, v5.4h
        mul     v16.4s, v7.4s, v14.4s
        addhn   v7.4h, v19.4s, v24.4s
        addhn2  v6.8h, v21.4s, v18.4s
        addhn2  v7.8h, v16.4s, v5.4s
        sub     v18.8h, v1.8h, v6.8h
        add     v16.8h, v1.8h, v6.8h
        sub     v19.8h, v2.8h, v7.8h
        add     v17.8h, v2.8h, v7.8h
        ldr     q4, [x13, #1136]
        .inst   0xd000002d  // adrp x13, 0xf000
        ldr     q3, [x12, #1120]
        st4     {v16.8h-v19.8h}, [x8], #64
        ld4     {v20.8h-v23.8h}, [x9]
        .inst   0xd000002c  // adrp x12, 0xf000
        ld4     {v24.8h-v27.8h}, [x8]
        sxtl    v17.4s, v22.4h
        sxtl    v29.4s, v23.4h
        sxtl2   v18.4s, v22.8h
        sxtl2   v30.4s, v23.8h
        ext     v19.16b, v22.16b, v22.16b, #8
        ldr     q16, [x13, #1200]
        .inst   0xd000002d  // adrp x13, 0xf000
        ldr     d2, [x11, #1688]
        .inst   0xd000002b  // adrp x11, 0xf000
        ldr     d1, [x10, #1680]
        .inst   0xd000002a  // adrp x10, 0xf000
        mul     v17.4s, v17.4s, v16.4s
        ldr     q7, [x12, #1184]
        mul     v16.4s, v29.4s, v16.4s
        ldr     d6, [x11, #1720]
        sxtl    v29.4s, v26.4h
        ldr     d5, [x10, #1712]
        sxtl    v11.4s, v27.4h
        add     x10, x0, #0xc0
        mul     v29.4s, v29.4s, v4.4s
        add     x11, sp, #0x120
        sxtl2   v8.4s, v26.8h
        .inst   0xb000002c  // adrp x12, 0xf000
        mul     v4.4s, v11.4s, v4.4s
        ldr     x29, [sp, #416]
        sxtl2   v12.4s, v27.8h
        mul     v8.4s, v8.4s, v3.4s
        sshr    v29.4s, v29.4s, #16
        ext     v9.16b, v26.16b, v26.16b, #8
        sshr    v4.4s, v4.4s, #16
        mul     v3.4s, v12.4s, v3.4s
        smull   v10.4s, v26.4h, v2.4h
        mul     v29.4s, v29.4s, v14.4s
        ext     v13.16b, v27.16b, v27.16b, #8
        sshr    v8.4s, v8.4s, #16
        smull   v2.4s, v27.4h, v2.4h
        sshr    v3.4s, v3.4s, #16
        mul     v4.4s, v4.4s, v14.4s
        smull   v9.4s, v9.4h, v1.4h
        mul     v8.4s, v8.4s, v14.4s
        addhn   v29.4h, v29.4s, v10.4s
        smull   v1.4s, v13.4h, v1.4h
        mul     v3.4s, v3.4s, v14.4s
        addhn   v10.4h, v4.4s, v2.4s
        addhn2  v29.8h, v8.4s, v9.4s
        mul     v18.4s, v18.4s, v7.4s
        addhn2  v10.8h, v3.4s, v1.4s
        sub     v2.8h, v24.8h, v29.8h
        add     v0.8h, v24.8h, v29.8h
        sub     v3.8h, v25.8h, v10.8h
        add     v1.8h, v25.8h, v10.8h
        ld4     {v24.8h-v27.8h}, [x10]
        mul     v7.4s, v30.4s, v7.4s
        sshr    v16.4s, v16.4s, #16
        st1     {v0.2d-v3.2d}, [x11]
        ext     v31.16b, v23.16b, v23.16b, #8
        sshr    v17.4s, v17.4s, #16
        smull   v28.4s, v22.4h, v6.4h
        .inst   0xb000002b  // adrp x11, 0xf000
        smull   v6.4s, v23.4h, v6.4h
        mul     v16.4s, v16.4s, v14.4s
        mul     v17.4s, v17.4s, v14.4s
        sshr    v7.4s, v7.4s, #16
        sshr    v18.4s, v18.4s, #16
        smull   v19.4s, v19.4h, v5.4h
        smull   v5.4s, v31.4h, v5.4h
        mul     v7.4s, v7.4s, v14.4s
        mul     v18.4s, v18.4s, v14.4s
        addhn   v6.4h, v16.4s, v6.4s
        addhn   v28.4h, v17.4s, v28.4s
        sxtl2   v29.4s, v26.8h
        addhn2  v6.8h, v7.4s, v5.4s
        ldr     q5, [x11, #1264]
        addhn2  v28.8h, v18.4s, v19.4s
        .inst   0xb000002b  // adrp x11, 0xf000
        sxtl    v7.4s, v26.4h
        ext     v30.16b, v26.16b, v26.16b, #8
        mul     v7.4s, v7.4s, v5.4s
        ldr     d31, [x11, #1752]
        sub     v2.8h, v20.8h, v28.8h
        add     x11, sp, #0xe0
        add     v0.8h, v20.8h, v28.8h
        ldr     q28, [x12, #1248]
        sub     v3.8h, v21.8h, v6.8h
        .inst   0xb000002c  // adrp x12, 0xf000
        sshr    v7.4s, v7.4s, #16
        add     v1.8h, v21.8h, v6.8h
        sxtl    v6.4s, v27.4h
        ldr     d9, [x12, #1744]
        smull   v8.4s, v26.4h, v31.4h
        st1     {v0.2d-v3.2d}, [x11]
        mul     v7.4s, v7.4s, v14.4s
        add     x11, x0, #0x100
        mul     v5.4s, v6.4s, v5.4s
        .inst   0xb000002c  // adrp x12, 0xf000
        mul     v29.4s, v29.4s, v28.4s
        sxtl2   v6.4s, v27.8h
        addhn   v10.4h, v7.4s, v8.4s
        mul     v21.4s, v6.4s, v28.4s
        sshr    v22.4s, v5.4s, #16
        ld4     {v5.8h-v8.8h}, [x11]
        sshr    v29.4s, v29.4s, #16
        smull   v30.4s, v30.4h, v9.4h
        mul     v29.4s, v29.4s, v14.4s
        ext     v20.16b, v27.16b, v27.16b, #8
        smull   v23.4s, v27.4h, v31.4h
        mul     v22.4s, v22.4s, v14.4s
        sshr    v21.4s, v21.4s, #16
        addhn2  v10.8h, v29.4s, v30.4s
        ldr     q30, [x13, #1312]
        smull   v28.4s, v20.4h, v9.4h
        add     x13, sp, #0xa0
        mul     v29.4s, v21.4s, v14.4s
        addhn   v9.4h, v22.4s, v23.4s
        sub     v2.8h, v24.8h, v10.8h
        add     v0.8h, v24.8h, v10.8h
        ldr     q10, [x14, #1328]
        addhn2  v9.8h, v29.4s, v28.4s
        ldr     d28, [x12, #1776]
        sxtl2   v29.4s, v7.8h
        .inst   0xb000002c  // adrp x12, 0xf000
        sxtl    v11.4s, v7.4h
        .inst   0xb000002e  // adrp x14, 0xf000
        mul     v29.4s, v29.4s, v30.4s
        mul     v11.4s, v11.4s, v10.4s
        ldr     d12, [x12, #1784]
        mov     v17.16b, v1.16b
        add     x12, x0, #0x140
        ext     v31.16b, v7.16b, v7.16b, #8
        sshr    v29.4s, v29.4s, #16
        sshr    v11.4s, v11.4s, #16
        mul     v1.4s, v29.4s, v14.4s
        sxtl    v29.4s, v8.4h
        smull   v13.4s, v31.4h, v28.4h
        mul     v29.4s, v29.4s, v10.4s
        sxtl2   v10.4s, v8.8h
        smull   v31.4s, v7.4h, v12.4h
        mul     v11.4s, v11.4s, v14.4s
        ext     v15.16b, v8.16b, v8.16b, #8
        mul     v30.4s, v10.4s, v30.4s
        sshr    v29.4s, v29.4s, #16
        mov     v16.16b, v0.16b
        mul     v10.4s, v29.4s, v14.4s
        addhn   v11.4h, v11.4s, v31.4s
        smull   v15.4s, v15.4h, v28.4h
        sshr    v0.4s, v30.4s, #16
        ld4     {v28.8h-v31.8h}, [x12]
        mov     v18.16b, v2.16b
        mov     v19.16b, v3.16b
        smull   v12.4s, v8.4h, v12.4h
        sub     v19.8h, v25.8h, v9.8h
        add     v17.8h, v25.8h, v9.8h
        mul     v0.4s, v0.4s, v14.4s
        addhn   v2.4h, v10.4s, v12.4s
        st1     {v16.2d-v19.2d}, [x13]
        .inst   0xb000002d  // adrp x13, 0xf000
        addhn2  v11.8h, v1.4s, v13.4s
        addhn2  v2.8h, v0.4s, v15.4s
        ldr     q0, [x13, #1392]
        .inst   0xb000002d  // adrp x13, 0xf000
        sxtl    v1.4s, v30.4h
        sub     v26.8h, v5.8h, v11.8h
        mul     v1.4s, v1.4s, v0.4s
        ldr     d10, [x13, #1816]
        add     v24.8h, v5.8h, v11.8h
        add     x13, x0, #0x180
        sub     v27.8h, v6.8h, v2.8h
        add     v25.8h, v6.8h, v2.8h
        ldr     q2, [x14, #1376]
        sshr    v1.4s, v1.4s, #16
        .inst   0xb000002e  // adrp x14, 0xf000
        sxtl2   v3.4s, v30.8h
        ld4     {v6.8h-v9.8h}, [x13]
        smull   v5.4s, v30.4h, v10.4h
        st4     {v24.8h-v27.8h}, [x11]
        mul     v1.4s, v1.4s, v14.4s
        mul     v3.4s, v3.4s, v2.4s
        ext     v4.16b, v30.16b, v30.16b, #8
        sxtl2   v12.4s, v31.8h
        addhn   v20.4h, v1.4s, v5.4s
        sxtl    v1.4s, v31.4h
        ldr     d11, [x14, #1808]
        sshr    v3.4s, v3.4s, #16
        mul     v0.4s, v1.4s, v0.4s
        .inst   0xb000002e  // adrp x14, 0xf000
        mul     v3.4s, v3.4s, v14.4s
        smull   v4.4s, v4.4h, v11.4h
        mul     v1.4s, v12.4s, v2.4s
        sshr    v0.4s, v0.4s, #16
        ext     v2.16b, v31.16b, v31.16b, #8
        addhn2  v20.8h, v3.4s, v4.4s
        ldr     q4, [x14, #1456]
        smull   v3.4s, v31.4h, v10.4h
        .inst   0xb000002e  // adrp x14, 0xf000
        mul     v0.4s, v0.4s, v14.4s
        ldr     q10, [x15, #1440]
        sshr    v1.4s, v1.4s, #16
        .inst   0xb000002f  // adrp x15, 0xf000
        smull   v2.4s, v2.4h, v11.4h
        mul     v1.4s, v1.4s, v14.4s
        addhn   v15.4h, v0.4s, v3.4s
        ldr     d12, [x15, #1840]
        sxtl    v3.4s, v8.4h
        .inst   0xb000002f  // adrp x15, 0xf000
        sxtl2   v11.4s, v8.8h
        mul     v3.4s, v3.4s, v4.4s
        addhn2  v15.8h, v1.4s, v2.4s
        mul     v11.4s, v11.4s, v10.4s
        ext     v1.16b, v8.16b, v8.16b, #8
        sshr    v2.4s, v3.4s, #16
        ldr     d3, [x14, #1848]
        sxtl    v0.4s, v9.4h
        add     x14, x0, #0x1c0
        mul     v2.4s, v2.4s, v14.4s
        smull   v13.4s, v8.4h, v3.4h
        sshr    v11.4s, v11.4s, #16
        ld4     {v16.8h-v19.8h}, [x14]
        mul     v4.4s, v0.4s, v4.4s
        smull   v1.4s, v1.4h, v12.4h
        addhn   v5.4h, v2.4s, v13.4s
        sxtl2   v13.4s, v9.8h
        mul     v11.4s, v11.4s, v14.4s
        mul     v21.4s, v13.4s, v10.4s
        sshr    v4.4s, v4.4s, #16
        ext     v10.16b, v9.16b, v9.16b, #8
        addhn2  v5.8h, v11.4s, v1.4s
        smull   v22.4s, v9.4h, v3.4h
        mul     v4.4s, v4.4s, v14.4s
        sub     v2.8h, v28.8h, v20.8h
        add     v0.8h, v28.8h, v20.8h
        sshr    v20.4s, v21.4s, #16
        smull   v21.4s, v10.4h, v12.4h
        mul     v20.4s, v20.4s, v14.4s
        addhn   v4.4h, v4.4s, v22.4s
        sub     v3.8h, v29.8h, v15.8h
        add     v1.8h, v29.8h, v15.8h
        addhn2  v4.8h, v20.4s, v21.4s
        sub     v22.8h, v6.8h, v5.8h
        st4     {v0.8h-v3.8h}, [x12]
        add     v20.8h, v6.8h, v5.8h
        ldr     q5, [x15, #1520]
        sub     v23.8h, v7.8h, v4.8h
        .inst   0xb000002f  // adrp x15, 0xf000
        add     v21.8h, v7.8h, v4.8h
        ldr     d4, [x16, #1880]
        add     x16, sp, #0x120
        sxtl    v28.4s, v18.4h
        st4     {v20.8h-v23.8h}, [x13]
        sxtl2   v30.4s, v18.8h
        ld1     {v6.2d-v9.2d}, [x16]
        mul     v28.4s, v28.4s, v5.4s
        ext     v31.16b, v18.16b, v18.16b, #8
        ext     v24.16b, v19.16b, v19.16b, #8
        ldp     d13, d12, [sp, #368]
        st4     {v6.8h-v9.8h}, [x8]
        ldr     d6, [x15, #1872]
        add     x15, sp, #0xe0
        sshr    v7.4s, v28.4s, #16
        smull   v28.4s, v18.4h, v4.4h
        .inst   0xb0000028  // adrp x8, 0xf000
        mul     v7.4s, v7.4s, v14.4s
        ld1     {v8.2d-v11.2d}, [x15]
        smull   v4.4s, v19.4h, v4.4h
        smull   v1.4s, v24.4h, v6.4h
        addhn   v7.4h, v7.4s, v28.4s
        sxtl    v28.4s, v19.4h
        mul     v5.4s, v28.4s, v5.4s
        sxtl2   v28.4s, v19.8h
        ldr     q29, [x8, #1504]
        add     x8, sp, #0xa0
        sshr    v5.4s, v5.4s, #16
        mul     v30.4s, v30.4s, v29.4s
        st4     {v8.8h-v11.8h}, [x9]
        mul     v28.4s, v28.4s, v29.4s
        ld1     {v8.2d-v11.2d}, [x8]
        mul     v5.4s, v5.4s, v14.4s
        sshr    v29.4s, v30.4s, #16
        smull   v30.4s, v31.4h, v6.4h
        sshr    v0.4s, v28.4s, #16
        mul     v29.4s, v29.4s, v14.4s
        mul     v0.4s, v0.4s, v14.4s
        addhn   v2.4h, v5.4s, v4.4s
        ldp     d15, d14, [sp, #352]
        addhn2  v7.8h, v29.4s, v30.4s
        addhn2  v2.8h, v0.4s, v1.4s
        st4     {v8.8h-v11.8h}, [x10]
        sub     v5.8h, v16.8h, v7.8h
        add     v3.8h, v16.8h, v7.8h
        ldp     d9, d8, [sp, #400]
        sub     v6.8h, v17.8h, v2.8h
        ldp     d11, d10, [sp, #384]
        add     v4.8h, v17.8h, v2.8h
        st4     {v3.8h-v6.8h}, [x14]
        add     sp, sp, #0x1b0
        ret

// mlkem_poly_invntt_tomont (0x1a30 bytes)
La46c:
        mov     w9, #0x5a1
        mov     w10, #0xd8a10000
        mov     x8, xzr
        mvni    v2.4s, #0xd, lsl #8
        dup     v0.8h, w9
        dup     v1.4s, w10
La484:
        add     x9, x0, x8
        add     x8, x8, #0x20
        cmp     x8, #0x200
        ldp     q3, q4, [x9]
        sxtl    v5.4s, v3.4h
        sxtl2   v6.4s, v3.8h
        sxtl    v7.4s, v4.4h
        mul     v5.4s, v5.4s, v1.4s
        mul     v7.4s, v7.4s, v1.4s
        sxtl2   v16.4s, v4.8h
        mul     v6.4s, v6.4s, v1.4s
        mul     v16.4s, v16.4s, v1.4s
        sshr    v5.4s, v5.4s, #16
        sshr    v7.4s, v7.4s, #16
        smull2  v17.4s, v3.8h, v0.8h
        sshr    v6.4s, v6.4s, #16
        smull   v3.4s, v3.4h, v0.4h
        smull2  v18.4s, v4.8h, v0.8h
        smull   v4.4s, v4.4h, v0.4h
        mul     v5.4s, v5.4s, v2.4s
        mul     v7.4s, v7.4s, v2.4s
        sshr    v16.4s, v16.4s, #16
        mul     v6.4s, v6.4s, v2.4s
        mul     v16.4s, v16.4s, v2.4s
        addhn   v3.4h, v5.4s, v3.4s
        addhn   v4.4h, v7.4s, v4.4s
        addhn2  v3.8h, v6.4s, v17.4s
        addhn2  v4.8h, v16.4s, v18.4s
        stp     q3, q4, [x9]
        b.ne    La484
        stp     d15, d14, [sp, #-80]!
        stp     d13, d12, [sp, #16]
        stp     d11, d10, [sp, #32]
        stp     d9, d8, [sp, #48]
        str     x29, [sp, #64]
        sub     sp, sp, #0x260
        mov     w10, #0x4ebf
        mov     w11, #0xf3010000
        mov     x8, xzr
        .inst   0xb0000029  // adrp x9, 0xf000
        add     x9, x9, #0x930
        dup     v0.8h, w10
        dup     v2.4s, w11
        mvni    v1.8h, #0xd, lsl #8
        mvni    v3.4s, #0xd, lsl #8
La538:
        add     x10, x0, x8
        add     x8, x8, #0x40
        ldr     q16, [x9], #-16
        movi    v17.4s, #0x2, lsl #24
        cmp     x8, #0x200
        ld4     {v4.8h-v7.8h}, [x10]
        rev64   v16.8h, v16.8h
        movi    v18.4s, #0x2, lsl #24
        ext     v16.16b, v16.16b, v16.16b, #8
        sub     v19.8h, v6.8h, v4.8h
        add     v20.8h, v6.8h, v4.8h
        smull   v24.4s, v19.4h, v16.4h
        smlal   v17.4s, v20.4h, v0.4h
        smlal2  v18.4s, v20.8h, v0.8h
        smull2  v19.4s, v19.8h, v16.8h
        mul     v25.4s, v24.4s, v2.4s
        sshr    v17.4s, v17.4s, #26
        sshr    v18.4s, v18.4s, #26
        mul     v26.4s, v19.4s, v2.4s
        uzp1    v17.8h, v17.8h, v18.8h
        sshr    v18.4s, v25.4s, #16
        mul     v18.4s, v18.4s, v3.4s
        sshr    v25.4s, v26.4s, #16
        mla     v20.8h, v17.8h, v1.8h
        mul     v17.4s, v25.4s, v3.4s
        addhn   v22.4h, v18.4s, v24.4s
        sub     v24.8h, v7.8h, v5.8h
        movi    v18.4s, #0x2, lsl #24
        addhn2  v22.8h, v17.4s, v19.4s
        movi    v17.4s, #0x2, lsl #24
        smull   v19.4s, v24.4h, v16.4h
        add     v21.8h, v7.8h, v5.8h
        smull2  v4.4s, v24.8h, v16.8h
        smlal   v18.4s, v21.4h, v0.4h
        smlal2  v17.4s, v21.8h, v0.8h
        mul     v5.4s, v19.4s, v2.4s
        mul     v16.4s, v4.4s, v2.4s
        sshr    v7.4s, v18.4s, #26
        sshr    v6.4s, v17.4s, #26
        sshr    v5.4s, v5.4s, #16
        uzp1    v6.8h, v7.8h, v6.8h
        sshr    v7.4s, v16.4s, #16
        mul     v5.4s, v5.4s, v3.4s
        mla     v21.8h, v6.8h, v1.8h
        mul     v6.4s, v7.4s, v3.4s
        addhn   v23.4h, v5.4s, v19.4s
        addhn2  v23.8h, v6.4s, v4.4s
        st4     {v20.8h-v23.8h}, [x10]
        b.ne    La538
        .inst   0xb0000029  // adrp x9, 0xf000
        .inst   0xb000002a  // adrp x10, 0xf000
        .inst   0xb000002c  // adrp x12, 0xf000
        mov     w11, #0x4ebf
        mov     x8, xzr
        mvni    v17.4h, #0xd, lsl #8
        ldr     q0, [x9, #832]
        .inst   0xb0000029  // adrp x9, 0xf000
        ldr     q1, [x10, #1536]
        .inst   0xb000002a  // adrp x10, 0xf000
        ldr     q2, [x12, #864]
        .inst   0xb000002c  // adrp x12, 0xf000
        ldr     q3, [x9, #1552]
        .inst   0xb0000029  // adrp x9, 0xf000
        ldr     q4, [x10, #896]
        .inst   0xb000002a  // adrp x10, 0xf000
        dup     v6.4h, w11
        ldr     q5, [x12, #1568]
        ldr     q7, [x9, #928]
        .inst   0xb0000029  // adrp x9, 0xf000
        add     x9, x9, #0x8b8
        ldr     q16, [x10, #1584]
        mov     w10, #0xf3010000
        mvni    v18.4s, #0xd, lsl #8
La65c:
        add     x11, x0, x8
        dup     v21.4s, w10
        add     x12, x11, #0x10
        add     x13, x11, #0x18
        add     x14, x11, #0x12
        add     x8, x8, #0x40
        ldr     h20, [x11]
        cmp     x8, #0x200
        ldr     h23, [x11, #8]
        ldr     h24, [x11, #2]
        ld1     {v20.h}[1], [x12]
        add     x12, x11, #0x1a
        ld1     {v23.h}[1], [x13]
        add     x13, x11, #0x20
        ldr     h27, [x11, #10]
        ld1     {v24.h}[1], [x14]
        add     x14, x11, #0x28
        ld1     {v20.h}[2], [x13]
        add     x13, x11, #0x30
        ld1     {v27.h}[1], [x12]
        add     x12, x11, #0x22
        ld1     {v23.h}[2], [x14]
        add     x14, x11, #0x38
        ldr     d22, [x9], #-8
        ld1     {v24.h}[2], [x12]
        add     x12, x11, #0x14
        ld1     {v20.h}[3], [x13]
        add     x13, x11, #0x2a
        ld1     {v23.h}[3], [x14]
        add     x14, x11, #0x32
        ldr     h26, [x11, #4]
        rev64   v25.4h, v22.4h
        ld1     {v27.h}[2], [x13]
        add     x13, x11, #0x1c
        ld1     {v24.h}[3], [x14]
        add     x14, x11, #0x3a
        ldr     h29, [x11, #12]
        sub     v22.4h, v23.4h, v20.4h
        ld1     {v26.h}[1], [x12]
        add     x12, x11, #0x24
        ld1     {v27.h}[3], [x14]
        add     x14, x11, #0x1e
        ld1     {v29.h}[1], [x13]
        add     x13, x11, #0x2c
        movi    v19.4s, #0x2, lsl #24
        ldr     h8, [x11, #14]
        smull   v30.4s, v22.4h, v25.4h
        ld1     {v26.h}[2], [x12]
        add     v22.4h, v23.4h, v20.4h
        add     x12, x11, #0x34
        ld1     {v29.h}[2], [x13]
        add     v20.4h, v27.4h, v24.4h
        add     x13, x11, #0x16
        sub     v24.4h, v27.4h, v24.4h
        ldr     h27, [x11, #6]
        smlal   v19.4s, v22.4h, v6.4h
        ld1     {v8.h}[1], [x14]
        ld1     {v26.h}[3], [x12]
        add     x12, x11, #0x3c
        ld1     {v27.h}[1], [x13]
        add     x13, x11, #0x26
        add     x14, x11, #0x2e
        sshr    v19.4s, v19.4s, #26
        ld1     {v29.h}[3], [x12]
        add     x12, x11, #0x36
        xtn     v19.4h, v19.4s
        ld1     {v27.h}[2], [x13]
        ld1     {v8.h}[2], [x14]
        add     x13, x11, #0x3e
        movi    v28.4s, #0x2, lsl #24
        mla     v22.4h, v19.4h, v17.4h
        movi    v19.4s, #0x2, lsl #24
        add     v23.4h, v29.4h, v26.4h
        ld1     {v27.h}[3], [x12]
        sub     v26.4h, v29.4h, v26.4h
        ld1     {v8.h}[3], [x13]
        smlal   v28.4s, v20.4h, v6.4h
        smlal   v19.4s, v23.4h, v6.4h
        smull   v26.4s, v26.4h, v25.4h
        movi    v29.4s, #0x2, lsl #24
        add     v10.4h, v8.4h, v27.4h
        sub     v27.4h, v8.4h, v27.4h
        sshr    v28.4s, v28.4s, #26
        mul     v31.4s, v30.4s, v21.4s
        sshr    v19.4s, v19.4s, #26
        smull   v24.4s, v24.4h, v25.4h
        smull   v25.4s, v27.4h, v25.4h
        mul     v27.4s, v26.4s, v21.4s
        smlal   v29.4s, v10.4h, v6.4h
        xtn     v28.4h, v28.4s
        xtn     v19.4h, v19.4s
        sshr    v31.4s, v31.4s, #16
        mul     v9.4s, v24.4s, v21.4s
        mla     v20.4h, v28.4h, v17.4h
        mla     v23.4h, v19.4h, v17.4h
        sshr    v19.4s, v27.4s, #16
        sshr    v29.4s, v29.4s, #26
        mul     v21.4s, v25.4s, v21.4s
        mul     v31.4s, v31.4s, v18.4s
        mul     v19.4s, v19.4s, v18.4s
        sshr    v8.4s, v9.4s, #16
        xtn     v27.4h, v29.4s
        mov     v22.d[1], v20.d[0]
        sshr    v20.4s, v21.4s, #16
        addhn   v30.4h, v31.4s, v30.4s
        mul     v8.4s, v8.4s, v18.4s
        mla     v10.4h, v27.4h, v17.4h
        addhn   v31.4h, v19.4s, v26.4s
        mul     v19.4s, v20.4s, v18.4s
        addhn2  v30.8h, v8.4s, v24.4s
        mov     v23.d[1], v10.d[0]
        addhn2  v31.8h, v19.4s, v25.4s
        tbl     v19.16b, {v22.16b-v23.16b}, v0.16b
        tbl     v20.16b, {v22.16b-v23.16b}, v2.16b
        tbl     v21.16b, {v22.16b-v23.16b}, v4.16b
        tbl     v22.16b, {v22.16b-v23.16b}, v7.16b
        tbl     v23.16b, {v30.16b-v31.16b}, v16.16b
        tbl     v24.16b, {v30.16b-v31.16b}, v5.16b
        tbl     v25.16b, {v30.16b-v31.16b}, v3.16b
        tbl     v26.16b, {v30.16b-v31.16b}, v1.16b
        mov     v22.d[1], v23.d[1]
        mov     v21.d[1], v24.d[1]
        mov     v20.d[1], v25.d[1]
        mov     v19.d[1], v26.d[1]
        stp     q21, q22, [x11, #32]
        stp     q19, q20, [x11]
        b.ne    La65c
        mov     w12, #0x4ebf
        .inst   0xb0000028  // adrp x8, 0xf000
        add     x8, x8, #0x87e
        add     x9, x0, #0x10
        mov     x10, #0xfffffffffffffff0
        mov     w11, #0xf3010000
        dup     v0.8h, w12
        mvni    v1.8h, #0xd, lsl #8
        mvni    v2.4s, #0xd, lsl #8
La87c:
        ldp     q3, q5, [x9, #-16]
        movi    v4.4s, #0x2, lsl #24
        dup     v17.4s, w11
        movi    v6.4s, #0x2, lsl #24
        add     x10, x10, #0x10
        cmp     x10, #0xf0
        ldrsh   w12, [x8], #-2
        add     v7.8h, v5.8h, v3.8h
        sub     v3.8h, v5.8h, v3.8h
        dup     v5.4s, w12
        sxtl    v16.4s, v3.4h
        sxtl2   v3.4s, v3.8h
        mul     v16.4s, v5.4s, v16.4s
        mul     v3.4s, v5.4s, v3.4s
        smlal   v4.4s, v7.4h, v0.4h
        smlal2  v6.4s, v7.8h, v0.8h
        mul     v5.4s, v16.4s, v17.4s
        mul     v17.4s, v3.4s, v17.4s
        sshr    v4.4s, v4.4s, #26
        sshr    v6.4s, v6.4s, #26
        sshr    v5.4s, v5.4s, #16
        uzp1    v4.8h, v4.8h, v6.8h
        sshr    v6.4s, v17.4s, #16
        mul     v5.4s, v5.4s, v2.4s
        mul     v6.4s, v6.4s, v2.4s
        mla     v7.8h, v4.8h, v1.8h
        addhn   v5.4h, v5.4s, v16.4s
        addhn2  v5.8h, v6.4s, v3.4s
        stp     q7, q5, [x9, #-16]
        add     x9, x9, #0x20
        b.cc    La87c
        ldp     q11, q1, [x0, #16]
        mov     w10, #0x79bc0000
        mov     w9, #0x5bc
        mvni    v24.4s, #0xd, lsl #8
        mov     x8, xzr
        mvni    v28.4s, #0xd, lsl #8
        dup     v18.4s, w10
        mov     w10, #0x4ebf
        dup     v5.8h, w9
        mov     w9, #0xd43e0000
        ldr     q19, [x0]
        ldp     q0, q30, [x0, #48]
        dup     v13.8h, w10
        ldp     q2, q3, [x0, #80]
        sub     v4.8h, v1.8h, v19.8h
        mov     w10, #0x5d5
        sub     v20.8h, v0.8h, v11.8h
        str     q0, [sp, #544]
        sxtl    v6.4s, v4.4h
        sxtl2   v7.4s, v4.8h
        mul     v6.4s, v6.4s, v18.4s
        mul     v7.4s, v7.4s, v18.4s
        smull2  v17.4s, v4.8h, v5.8h
        ldr     q9, [x0, #112]
        smull   v16.4s, v4.4h, v5.4h
        ldr     q25, [x0, #176]
        sshr    v4.4s, v6.4s, #16
        sxtl    v21.4s, v20.4h
        sshr    v7.4s, v7.4s, #16
        mul     v22.4s, v4.4s, v24.4s
        mul     v21.4s, v21.4s, v18.4s
        mul     v7.4s, v7.4s, v24.4s
        sxtl2   v6.4s, v20.8h
        addhn   v0.4h, v22.4s, v16.4s
        smull2  v4.4s, v20.8h, v5.8h
        smull   v5.4s, v20.4h, v5.4h
        sshr    v20.4s, v21.4s, #16
        addhn2  v0.8h, v7.4s, v17.4s
        sub     v17.8h, v3.8h, v30.8h
        mul     v6.4s, v6.4s, v18.4s
        mul     v7.4s, v20.4s, v24.4s
        str     q0, [sp, #592]
        sxtl    v18.4s, v17.4h
        dup     v20.4s, w9
        mov     w9, #0xfa3e
        sshr    v6.4s, v6.4s, #16
        mul     v18.4s, v18.4s, v20.4s
        mul     v6.4s, v6.4s, v24.4s
        sxtl2   v21.4s, v17.8h
        dup     v22.8h, w9
        mov     w9, #0x54e0000
        addhn   v0.4h, v7.4s, v5.4s
        sshr    v5.4s, v18.4s, #16
        mul     v21.4s, v21.4s, v20.4s
        smull   v7.4s, v17.4h, v22.4h
        mul     v5.4s, v5.4s, v24.4s
        addhn2  v0.8h, v6.4s, v4.4s
        sshr    v18.4s, v21.4s, #16
        smull2  v17.4s, v17.8h, v22.8h
        dup     v21.4s, w9
        addhn   v10.4h, v5.4s, v7.4s
        str     q0, [sp, #576]
        sub     v5.8h, v9.8h, v2.8h
        ldr     q7, [x0, #128]
        ldp     q16, q0, [x0, #144]
        mul     v18.4s, v18.4s, v24.4s
        mov     w9, #0xfb4e
        sxtl    v4.4s, v5.4h
        sxtl2   v6.4s, v5.8h
        mul     v4.4s, v4.4s, v20.4s
        stp     q25, q16, [sp, #384]
        addhn2  v10.8h, v18.4s, v17.4s
        sub     v18.8h, v0.8h, v7.8h
        stp     q0, q7, [sp, #416]
        mul     v6.4s, v6.4s, v20.4s
        ldr     q7, [x0, #192]
        sshr    v4.4s, v4.4s, #16
        sxtl    v20.4s, v18.4h
        dup     v23.8h, w9
        smull2  v17.4s, v5.8h, v22.8h
        mov     w9, #0x29c20000
        smull   v5.4s, v5.4h, v22.4h
        mul     v4.4s, v4.4s, v24.4s
        mul     v20.4s, v20.4s, v21.4s
        sxtl2   v22.4s, v18.8h
        sshr    v6.4s, v6.4s, #16
        mul     v22.4s, v22.4s, v21.4s
        addhn   v27.4h, v4.4s, v5.4s
        sshr    v4.4s, v20.4s, #16
        smull   v5.4s, v18.4h, v23.4h
        mul     v4.4s, v4.4s, v24.4s
        sshr    v20.4s, v22.4s, #16
        smull2  v18.4s, v18.8h, v23.8h
        mul     v20.4s, v20.4s, v24.4s
        addhn   v0.4h, v4.4s, v5.4s
        sub     v4.8h, v25.8h, v16.8h
        ldr     q25, [x0, #240]
        mul     v6.4s, v6.4s, v24.4s
        addhn2  v0.8h, v20.4s, v18.4s
        sxtl    v5.4s, v4.4h
        add     v3.8h, v3.8h, v30.8h
        str     q0, [sp, #560]
        ldp     q16, q0, [x0, #208]
        mul     v5.4s, v5.4s, v21.4s
        addhn2  v27.8h, v6.4s, v17.4s
        sxtl2   v6.4s, v4.8h
        smull2  v17.4s, v4.8h, v23.8h
        stp     q25, q16, [sp, #224]
        sshr    v5.4s, v5.4s, #16
        stp     q10, q27, [x0, #96]
        sub     v18.8h, v0.8h, v7.8h
        stp     q0, q7, [sp, #288]
        mul     v6.4s, v6.4s, v21.4s
        sxtl    v20.4s, v18.4h
        dup     v21.4s, w9
        mov     w9, #0x3c2
        smull   v4.4s, v4.4h, v23.4h
        mul     v5.4s, v5.4s, v24.4s
        mul     v20.4s, v20.4s, v21.4s
        sxtl2   v22.4s, v18.8h
        dup     v23.8h, w9
        mov     w9, #0xc2b60000
        mul     v22.4s, v22.4s, v21.4s
        sshr    v6.4s, v6.4s, #16
        addhn   v0.4h, v5.4s, v4.4s
        sshr    v4.4s, v20.4s, #16
        smull   v5.4s, v18.4h, v23.4h
        mul     v4.4s, v4.4s, v24.4s
        sshr    v20.4s, v22.4s, #16
        mul     v6.4s, v6.4s, v24.4s
        smull2  v18.4s, v18.8h, v23.8h
        mul     v20.4s, v20.4s, v24.4s
        addhn   v7.4h, v4.4s, v5.4s
        sub     v4.8h, v25.8h, v16.8h
        ldr     q25, [x0, #432]
        addhn2  v0.8h, v6.4s, v17.4s
        addhn2  v7.8h, v20.4s, v18.4s
        ldp     q20, q18, [x0, #304]
        sxtl    v5.4s, v4.4h
        str     q0, [sp, #512]
        str     q7, [sp, #480]
        mul     v5.4s, v5.4s, v21.4s
        ldp     q7, q0, [x0, #272]
        sxtl2   v6.4s, v4.8h
        smull2  v17.4s, v4.8h, v23.8h
        mul     v21.4s, v6.4s, v21.4s
        sshr    v5.4s, v5.4s, #16
        str     q7, [sp, #32]
        smull   v4.4s, v4.4h, v23.4h
        ldr     q6, [x0, #256]
        mul     v22.4s, v5.4s, v24.4s
        movi    v30.4s, #0x2, lsl #24
        sub     v23.8h, v0.8h, v6.8h
        stp     q6, q0, [sp, #96]
        dup     v6.4s, w9
        mov     w9, #0xf1290000
        sxtl    v26.4s, v23.4h
        addhn   v14.4h, v22.4s, v4.4s
        mul     v4.4s, v26.4s, v6.4s
        sshr    v22.4s, v21.4s, #16
        movi    v21.4h, #0xb6
        dup     v8.4s, w9
        sxtl2   v26.4s, v23.8h
        mov     w9, #0x629
        sshr    v4.4s, v4.4s, #16
        mul     v29.4s, v22.4s, v24.4s
        mul     v26.4s, v26.4s, v6.4s
        mul     v4.4s, v4.4s, v24.4s
        smull   v31.4s, v23.4h, v21.4h
        movi    v22.8h, #0xb6
        addhn2  v14.8h, v29.4s, v17.4s
        ldr     q17, [x0, #368]
        smlal   v30.4s, v3.4h, v13.4h
        addhn   v5.4h, v4.4s, v31.4s
        sshr    v4.4s, v26.4s, #16
        smull2  v26.4s, v23.8h, v22.8h
        sub     v31.8h, v20.8h, v7.8h
        ldp     q7, q23, [x0, #336]
        sxtl    v12.4s, v31.4h
        sshr    v30.4s, v30.4s, #26
        mul     v29.4s, v4.4s, v24.4s
        mul     v12.4s, v12.4s, v6.4s
        smull   v21.4s, v31.4h, v21.4h
        mvni    v4.4s, #0xd, lsl #8
        sub     v15.8h, v23.8h, v18.8h
        addhn2  v5.8h, v29.4s, v26.4s
        sxtl    v0.4s, v15.4h
        sshr    v26.4s, v12.4s, #16
        mul     v0.4s, v0.4s, v8.4s
        dup     v12.8h, w9
        mul     v26.4s, v26.4s, v24.4s
        str     q5, [sp, #496]
        sxtl2   v29.4s, v31.8h
        mov     w9, #0x6c6e0000
        smull2  v31.4s, v31.8h, v22.8h
        sshr    v0.4s, v0.4s, #16
        mul     v6.4s, v29.4s, v6.4s
        mul     v0.4s, v0.4s, v24.4s
        smull   v24.4s, v15.4h, v12.4h
        addhn   v16.4h, v26.4s, v21.4s
        sshr    v6.4s, v6.4s, #16
        sub     v21.8h, v17.8h, v7.8h
        addhn   v5.4h, v0.4s, v24.4s
        sxtl2   v0.4s, v15.8h
        smull2  v24.4s, v15.8h, v12.8h
        mul     v0.4s, v0.4s, v8.4s
        mul     v6.4s, v6.4s, v4.4s
        sxtl    v22.4s, v21.4h
        smull2  v15.4s, v21.8h, v12.8h
        sshr    v0.4s, v0.4s, #16
        smull   v12.4s, v21.4h, v12.4h
        mul     v0.4s, v0.4s, v4.4s
        sxtl2   v21.4s, v21.8h
        mul     v22.4s, v22.4s, v8.4s
        mul     v21.4s, v21.4s, v8.4s
        addhn2  v16.8h, v6.4s, v31.4s
        addhn2  v5.8h, v0.4s, v24.4s
        sshr    v22.4s, v22.4s, #16
        sshr    v21.4s, v21.4s, #16
        stp     q16, q5, [sp, #448]
        ldp     q16, q0, [x0, #400]
        mul     v22.4s, v22.4s, v4.4s
        mul     v21.4s, v21.4s, v4.4s
        add     v6.8h, v1.8h, v19.8h
        dup     v19.4s, w9
        mov     w9, #0x26e
        addhn   v22.4h, v22.4s, v12.4s
        stp     q25, q16, [sp, #160]
        ldr     q4, [x0, #384]
        movi    v24.4s, #0x2, lsl #24
        addhn2  v22.8h, v21.4s, v15.4s
        stp     q4, q0, [sp, #256]
        sub     v0.8h, v0.8h, v4.8h
        movi    v12.4s, #0x2, lsl #24
        sxtl    v1.4s, v0.4h
        sxtl2   v31.4s, v0.8h
        mul     v21.4s, v1.4s, v19.4s
        mul     v31.4s, v31.4s, v19.4s
        smlal   v24.4s, v6.4h, v13.4h
        smlal2  v12.4s, v6.8h, v13.8h
        sshr    v8.4s, v21.4s, #16
        dup     v21.8h, w9
        sshr    v31.4s, v31.4s, #16
        mul     v8.4s, v8.4s, v28.4s
        sshr    v24.4s, v24.4s, #26
        smull   v15.4s, v0.4h, v21.4h
        mov     w9, #0xae550000
        smull2  v0.4s, v0.8h, v21.8h
        mul     v31.4s, v31.4s, v28.4s
        add     v2.8h, v9.8h, v2.8h
        addhn   v1.4h, v8.4s, v15.4s
        sshr    v8.4s, v12.4s, #26
        movi    v9.4s, #0x2, lsl #24
        addhn2  v1.8h, v31.4s, v0.4s
        uzp1    v0.8h, v24.8h, v8.8h
        movi    v8.4s, #0x2, lsl #24
        str     q1, [sp, #528]
        ldr     q1, [sp, #544]
        movi    v24.4s, #0x2, lsl #24
        movi    v15.4s, #0x2, lsl #24
        add     v31.8h, v1.8h, v11.8h
        mvni    v11.8h, #0xd, lsl #8
        smlal2  v8.4s, v31.8h, v13.8h
        mla     v6.8h, v0.8h, v11.8h
        smlal   v24.4s, v31.4h, v13.4h
        smlal   v9.4s, v2.4h, v13.4h
        sshr    v0.4s, v8.4s, #26
        movi    v8.4s, #0x2, lsl #24
        sshr    v24.4s, v24.4s, #26
        smlal2  v15.4s, v2.8h, v13.8h
        sshr    v9.4s, v9.4s, #26
        uzp1    v5.8h, v24.8h, v0.8h
        smlal2  v8.4s, v3.8h, v13.8h
        sub     v0.8h, v25.8h, v16.8h
        ldr     q16, [x0, #448]
        sxtl    v12.4s, v0.4h
        sshr    v24.4s, v8.4s, #26
        sshr    v8.4s, v15.4s, #26
        uzp1    v4.8h, v30.8h, v24.8h
        dup     v30.4s, w9
        ldp     q24, q1, [x0, #464]
        mul     v12.4s, v12.4s, v19.4s
        mov     w9, #0xbeca0000
        uzp1    v8.8h, v9.8h, v8.8h
        mla     v3.8h, v4.8h, v11.8h
        mla     v31.8h, v5.8h, v11.8h
        str     q24, [sp, #80]
        sshr    v4.4s, v12.4s, #16
        sub     v26.8h, v1.8h, v16.8h
        stp     q16, q1, [sp, #128]
        mla     v2.8h, v8.8h, v11.8h
        ldr     q9, [x0, #496]
        sxtl    v16.4s, v26.4h
        stp     q6, q31, [x0]
        mul     v4.4s, v4.4s, v28.4s
        mul     v16.4s, v16.4s, v30.4s
        smull   v8.4s, v0.4h, v21.4h
        stp     q3, q2, [x0, #64]
        mvni    v12.4h, #0xaa
        smull   v25.4s, v26.4h, v12.4h
        sshr    v5.4s, v16.4s, #16
        sxtl2   v16.4s, v0.8h
        mul     v5.4s, v5.4s, v28.4s
        mul     v16.4s, v16.4s, v19.4s
        addhn   v15.4h, v4.4s, v8.4s
        sxtl2   v4.4s, v26.8h
        addhn   v29.4h, v5.4s, v25.4s
        sshr    v5.4s, v16.4s, #16
        mul     v4.4s, v4.4s, v30.4s
        smull2  v0.4s, v0.8h, v21.8h
        mul     v5.4s, v5.4s, v28.4s
        sub     v19.8h, v9.8h, v24.8h
        sshr    v4.4s, v4.4s, #16
        sxtl    v25.4s, v19.4h
        mvni    v6.8h, #0xaa
        addhn2  v15.8h, v5.4s, v0.4s
        mul     v0.4s, v25.4s, v30.4s
        smull2  v16.4s, v26.8h, v6.8h
        mul     v4.4s, v4.4s, v28.4s
        ldp     q1, q31, [x0, #64]
        sshr    v0.4s, v0.4s, #16
        smull2  v3.4s, v19.8h, v6.8h
        addhn2  v29.8h, v4.4s, v16.4s
        smull   v4.4s, v19.4h, v12.4h
        mul     v0.4s, v0.4s, v28.4s
        ldp     q2, q24, [x0]
        sxtl2   v5.4s, v19.8h
        movi    v12.8h, #0xca
        mul     v5.4s, v5.4s, v30.4s
        sub     v16.8h, v1.8h, v2.8h
        stp     q2, q1, [sp, #352]
        dup     v2.4s, w9
        mov     w9, #0x6e1f0000
        sxtl    v6.4s, v16.4h
        addhn   v21.4h, v0.4s, v4.4s
        stp     q31, q24, [sp, #320]
        mul     v19.4s, v6.4s, v2.4s
        ldp     q1, q6, [sp, #576]
        sxtl2   v0.4s, v16.8h
        movi    v4.4h, #0xca
        mul     v0.4s, v0.4s, v2.4s
        sshr    v5.4s, v5.4s, #16
        sshr    v19.4s, v19.4s, #16
        stp     q6, q1, [x0, #32]
        mul     v5.4s, v5.4s, v28.4s
        mul     v25.4s, v19.4s, v28.4s
        smull   v26.4s, v16.4h, v4.4h
        sshr    v0.4s, v0.4s, #16
        smull2  v16.4s, v16.8h, v12.8h
        mul     v0.4s, v0.4s, v28.4s
        addhn   v1.4h, v25.4s, v26.4s
        addhn2  v21.8h, v5.4s, v3.4s
        sub     v3.8h, v31.8h, v24.8h
        addhn2  v1.8h, v0.4s, v16.4s
        sxtl    v0.4s, v3.4h
        stp     q29, q21, [x0, #480]
        sxtl2   v5.4s, v3.8h
        mul     v0.4s, v0.4s, v2.4s
        str     q1, [sp, #576]
        mul     v5.4s, v5.4s, v2.4s
        smull2  v16.4s, v3.8h, v12.8h
        smull   v3.4s, v3.4h, v4.4h
        sshr    v0.4s, v0.4s, #16
        ldp     q1, q8, [x0, #96]
        mul     v0.4s, v0.4s, v28.4s
        sshr    v5.4s, v5.4s, #16
        movi    v31.4s, #0x2, lsl #24
        mul     v5.4s, v5.4s, v28.4s
        movi    v21.4s, #0x2, lsl #24
        movi    v29.4s, #0x2, lsl #24
        ldp     q6, q24, [x0, #32]
        stp     q6, q1, [sp, #192]
        sub     v25.8h, v1.8h, v6.8h
        addhn   v1.4h, v0.4s, v3.4s
        stp     q8, q24, [sp, #48]
        sxtl    v26.4s, v25.4h
        smull   v27.4s, v25.4h, v4.4h
        addhn2  v1.8h, v5.4s, v16.4s
        mul     v0.4s, v26.4s, v2.4s
        movi    v16.4s, #0x2, lsl #24
        str     q1, [sp, #544]
        ldp     q5, q1, [sp, #416]
        sshr    v0.4s, v0.4s, #16
        sxtl2   v26.4s, v25.8h
        mul     v0.4s, v0.4s, v28.4s
        mul     v26.4s, v26.4s, v2.4s
        smull2  v25.4s, v25.8h, v12.8h
        add     v5.8h, v5.8h, v1.8h
        ldp     q6, q1, [sp, #384]
        smlal2  v16.4s, v5.8h, v13.8h
        movi    v3.4s, #0x2, lsl #24
        add     v30.8h, v6.8h, v1.8h
        addhn   v1.4h, v0.4s, v27.4s
        sshr    v0.4s, v16.4s, #26
        sshr    v16.4s, v26.4s, #16
        smlal   v3.4s, v5.4h, v13.4h
        mul     v16.4s, v16.4s, v28.4s
        movi    v26.4s, #0x2, lsl #24
        movi    v27.4s, #0x2, lsl #24
        sshr    v3.4s, v3.4s, #26
        addhn2  v1.8h, v16.4s, v25.4s
        smlal   v26.4s, v30.4h, v13.4h
        smlal2  v27.4s, v30.8h, v13.8h
        str     q1, [sp, #592]
        ldp     q6, q1, [sp, #288]
        uzp1    v0.8h, v3.8h, v0.8h
        sshr    v16.4s, v26.4s, #26
        sshr    v3.4s, v27.4s, #26
        movi    v27.4s, #0x2, lsl #24
        mla     v5.8h, v0.8h, v11.8h
        add     v25.8h, v6.8h, v1.8h
        ldp     q6, q1, [sp, #224]
        uzp1    v0.8h, v16.8h, v3.8h
        movi    v3.4s, #0x2, lsl #24
        movi    v16.4s, #0x2, lsl #24
        mla     v30.8h, v0.8h, v11.8h
        add     v26.8h, v6.8h, v1.8h
        smlal   v3.4s, v25.4h, v13.4h
        smlal2  v16.4s, v25.8h, v13.8h
        smlal   v27.4s, v26.4h, v13.4h
        stp     q5, q30, [x0, #128]
        smlal2  v31.4s, v26.8h, v13.8h
        ldp     q6, q1, [sp, #96]
        sshr    v16.4s, v16.4s, #26
        sshr    v3.4s, v3.4s, #26
        movi    v5.4s, #0x2, lsl #24
        uzp1    v3.8h, v3.8h, v16.8h
        sshr    v0.4s, v31.4s, #26
        sshr    v16.4s, v27.4s, #26
        movi    v27.4s, #0x2, lsl #24
        uzp1    v0.8h, v16.8h, v0.8h
        add     v16.8h, v1.8h, v6.8h
        ldr     q1, [sp, #32]
        mla     v25.8h, v3.8h, v11.8h
        movi    v3.4s, #0x2, lsl #24
        add     v19.8h, v20.8h, v1.8h
        ldr     q1, [sp, #560]
        movi    v20.4s, #0x2, lsl #24
        movi    v31.4s, #0x2, lsl #24
        smlal   v3.4s, v16.4h, v13.4h
        smlal2  v27.4s, v16.8h, v13.8h
        smlal   v20.4s, v19.4h, v13.4h
        smlal2  v31.4s, v19.8h, v13.8h
        sshr    v3.4s, v3.4s, #26
        sshr    v27.4s, v27.4s, #26
        mla     v26.8h, v0.8h, v11.8h
        sshr    v20.4s, v20.4s, #26
        sshr    v0.4s, v31.4s, #26
        uzp1    v3.8h, v3.8h, v27.8h
        uzp1    v0.8h, v20.8h, v0.8h
        movi    v20.4s, #0x2, lsl #24
        stp     q25, q26, [x0, #192]
        movi    v27.4s, #0x2, lsl #24
        add     v6.8h, v23.8h, v18.8h
        add     v23.8h, v17.8h, v7.8h
        smlal   v20.4s, v6.4h, v13.4h
        smlal2  v27.4s, v6.8h, v13.8h
        movi    v7.4s, #0x2, lsl #24
        smlal   v5.4s, v23.4h, v13.4h
        sshr    v18.4s, v20.4s, #26
        sshr    v17.4s, v27.4s, #26
        smlal2  v7.4s, v23.8h, v13.8h
        mla     v19.8h, v0.8h, v11.8h
        uzp1    v0.8h, v18.8h, v17.8h
        sshr    v5.4s, v5.4s, #26
        sshr    v7.4s, v7.4s, #26
        dup     v18.4s, w9
        sub     v17.8h, v8.8h, v24.8h
        mov     w9, #0x11f
        uzp1    v5.8h, v5.8h, v7.8h
        sxtl    v7.4s, v17.4h
        mla     v6.8h, v0.8h, v11.8h
        ldp     q0, q27, [x0, #192]
        mul     v7.4s, v7.4s, v2.4s
        mla     v23.8h, v5.8h, v11.8h
        smull   v4.4s, v17.4h, v4.4h
        mla     v16.8h, v3.8h, v11.8h
        str     q0, [sp, #96]
        sshr    v5.4s, v7.4s, #16
        ldp     q24, q8, [x0, #128]
        sxtl2   v7.4s, v17.8h
        stp     q6, q23, [x0, #320]
        mul     v5.4s, v5.4s, v28.4s
        stp     q16, q19, [x0, #256]
        mul     v2.4s, v7.4s, v2.4s
        sub     v25.8h, v0.8h, v24.8h
        smull2  v20.4s, v17.8h, v12.8h
        sxtl    v26.4s, v25.4h
        ldr     q0, [sp, #512]
        sub     v30.8h, v27.8h, v8.8h
        mul     v26.4s, v26.4s, v18.4s
        sxtl    v31.4s, v30.4h
        stp     q1, q0, [x0, #160]
        addhn   v3.4h, v5.4s, v4.4s
        ldr     q0, [sp, #480]
        mul     v7.4s, v31.4s, v18.4s
        sshr    v4.4s, v26.4s, #16
        dup     v31.8h, w9
        stp     q0, q14, [x0, #224]
        mul     v4.4s, v4.4s, v28.4s
        sshr    v2.4s, v2.4s, #16
        sshr    v5.4s, v7.4s, #16
        mov     w9, #0xcf8e0000
        smull   v7.4s, v25.4h, v31.4h
        sxtl2   v26.4s, v25.8h
        mul     v5.4s, v5.4s, v28.4s
        smull   v10.4s, v30.4h, v31.4h
        addhn   v1.4h, v4.4s, v7.4s
        mul     v4.4s, v26.4s, v18.4s
        ldp     q17, q7, [x0, #160]
        addhn   v14.4h, v5.4s, v10.4s
        sxtl2   v0.4s, v30.8h
        sshr    v10.4s, v4.4s, #16
        mul     v0.4s, v0.4s, v18.4s
        mul     v5.4s, v2.4s, v28.4s
        ldp     q26, q4, [x0, #224]
        smull2  v30.4s, v30.8h, v31.8h
        sshr    v0.4s, v0.4s, #16
        addhn2  v3.8h, v5.4s, v20.4s
        sub     v12.8h, v26.8h, v17.8h
        mul     v0.4s, v0.4s, v28.4s
        sxtl    v2.4s, v12.4h
        str     q3, [sp, #480]
        smull2  v25.4s, v25.8h, v31.8h
        mul     v2.4s, v2.4s, v18.4s
        mul     v10.4s, v10.4s, v28.4s
        addhn2  v14.8h, v0.4s, v30.4s
        sub     v0.8h, v4.8h, v7.8h
        sshr    v2.4s, v2.4s, #16
        smull   v16.4s, v12.4h, v31.4h
        mul     v2.4s, v2.4s, v28.4s
        sxtl    v3.4s, v0.4h
        addhn2  v1.8h, v10.4s, v25.4s
        mul     v3.4s, v3.4s, v18.4s
        addhn   v23.4h, v2.4s, v16.4s
        sxtl2   v2.4s, v12.8h
        stp     q1, q14, [sp, #288]
        smull2  v5.4s, v12.8h, v31.8h
        ldr     q1, [x0, #320]
        ldp     q19, q12, [x0, #256]
        sshr    v3.4s, v3.4s, #16
        smull2  v6.4s, v0.8h, v31.8h
        smull   v16.4s, v0.4h, v31.4h
        sxtl2   v0.4s, v0.8h
        stp     q1, q19, [sp, #416]
        mul     v31.4s, v3.4s, v28.4s
        sub     v25.8h, v1.8h, v19.8h
        ldr     q3, [x0, #336]
        mul     v2.4s, v2.4s, v18.4s
        mul     v0.4s, v0.4s, v18.4s
        sxtl    v30.4s, v25.4h
        stp     q3, q12, [sp, #384]
        dup     v18.4s, w9
        mov     w9, #0x58e
        addhn   v14.4h, v31.4s, v16.4s
        sshr    v2.4s, v2.4s, #16
        mul     v16.4s, v30.4s, v18.4s
        sxtl2   v30.4s, v25.8h
        sshr    v0.4s, v0.4s, #16
        mul     v30.4s, v30.4s, v18.4s
        mul     v31.4s, v2.4s, v28.4s
        sshr    v16.4s, v16.4s, #16
        dup     v2.8h, w9
        mov     w9, #0x34d50000
        mul     v0.4s, v0.4s, v28.4s
        sshr    v30.4s, v30.4s, #16
        mul     v16.4s, v16.4s, v28.4s
        smull   v10.4s, v25.4h, v2.4h
        smull2  v25.4s, v25.8h, v2.8h
        addhn2  v14.8h, v0.4s, v6.4s
        sub     v0.8h, v3.8h, v12.8h
        mul     v30.4s, v30.4s, v28.4s
        addhn   v1.4h, v16.4s, v10.4s
        sxtl    v6.4s, v0.4h
        addhn2  v23.8h, v31.4s, v5.4s
        mul     v6.4s, v6.4s, v18.4s
        addhn2  v1.8h, v30.4s, v25.4s
        sxtl2   v25.4s, v0.8h
        stp     q23, q14, [x0, #224]
        smull   v31.4s, v0.4h, v2.4h
        mul     v25.4s, v25.4s, v18.4s
        str     q1, [sp, #560]
        ldp     q3, q1, [sp, #256]
        sshr    v6.4s, v6.4s, #16
        smull2  v0.4s, v0.8h, v2.8h
        mul     v6.4s, v6.4s, v28.4s
        sshr    v25.4s, v25.4s, #16
        movi    v5.4s, #0x2, lsl #24
        mul     v25.4s, v25.4s, v28.4s
        add     v16.8h, v1.8h, v3.8h
        addhn   v1.4h, v6.4s, v31.4s
        movi    v30.4s, #0x2, lsl #24
        smlal   v5.4s, v16.4h, v13.4h
        addhn2  v1.8h, v25.4s, v0.4s
        movi    v31.4s, #0x2, lsl #24
        smlal2  v30.4s, v16.8h, v13.8h
        str     q1, [sp, #512]
        sshr    v5.4s, v5.4s, #26
        ldp     q3, q1, [sp, #160]
        movi    v10.4s, #0x2, lsl #24
        sshr    v6.4s, v30.4s, #26
        mvni    v12.4s, #0xd, lsl #8
        uzp1    v0.8h, v5.8h, v6.8h
        movi    v5.4s, #0x2, lsl #24
        add     v25.8h, v3.8h, v1.8h
        ldp     q3, q1, [sp, #128]
        movi    v6.4s, #0x2, lsl #24
        smlal   v5.4s, v25.4h, v13.4h
        mla     v16.8h, v0.8h, v11.8h
        add     v17.8h, v26.8h, v17.8h
        smlal2  v6.4s, v25.8h, v13.8h
        add     v30.8h, v1.8h, v3.8h
        ldr     q3, [sp, #496]
        ldp     q1, q0, [sp, #448]
        sshr    v5.4s, v5.4s, #26
        smlal   v31.4s, v30.4h, v13.4h
        smlal2  v10.4s, v30.8h, v13.8h
        sshr    v6.4s, v6.4s, #26
        stp     q3, q1, [x0, #288]
        stp     q0, q22, [x0, #352]
        uzp1    v5.8h, v5.8h, v6.8h
        sshr    v6.4s, v31.4s, #26
        sshr    v0.4s, v10.4s, #26
        ldp     q1, q20, [x0, #352]
        uzp1    v0.8h, v6.8h, v0.8h
        mla     v25.8h, v5.8h, v11.8h
        movi    v5.4s, #0x2, lsl #24
        movi    v22.4s, #0x2, lsl #24
        mla     v30.8h, v0.8h, v11.8h
        ldp     q3, q19, [x0, #288]
        stp     q16, q25, [x0, #384]
        str     q20, [sp, #176]
        add     v7.8h, v4.8h, v7.8h
        sub     v31.8h, v1.8h, v3.8h
        stp     q3, q1, [sp, #256]
        mvni    v1.4s, #0xd, lsl #8
        ldr     q6, [sp, #80]
        str     q19, [sp, #224]
        smull2  v16.4s, v31.8h, v2.8h
        movi    v4.4s, #0x2, lsl #24
        add     v6.8h, v9.8h, v6.8h
        sxtl    v9.4s, v31.4h
        smlal   v5.4s, v6.4h, v13.4h
        smlal2  v22.4s, v6.8h, v13.8h
        mul     v9.4s, v9.4s, v18.4s
        smlal   v4.4s, v7.4h, v13.4h
        sshr    v5.4s, v5.4s, #26
        sshr    v0.4s, v22.4s, #26
        sshr    v22.4s, v9.4s, #16
        uzp1    v0.8h, v5.8h, v0.8h
        sshr    v4.4s, v4.4s, #26
        mul     v5.4s, v22.4s, v28.4s
        smull   v22.4s, v31.4h, v2.4h
        sub     v9.8h, v20.8h, v19.8h
        mla     v6.8h, v0.8h, v11.8h
        sxtl    v0.4s, v9.4h
        addhn   v3.4h, v5.4s, v22.4s
        mul     v0.4s, v0.4s, v18.4s
        sxtl2   v5.4s, v31.8h
        stp     q30, q6, [x0, #448]
        sxtl2   v22.4s, v9.8h
        mul     v5.4s, v5.4s, v18.4s
        mul     v18.4s, v22.4s, v18.4s
        sshr    v0.4s, v0.4s, #16
        smull   v22.4s, v9.4h, v2.4h
        sshr    v5.4s, v5.4s, #16
        mul     v0.4s, v0.4s, v1.4s
        sshr    v6.4s, v18.4s, #16
        ldp     q19, q20, [x0, #384]
        mul     v5.4s, v5.4s, v1.4s
        mul     v6.4s, v6.4s, v1.4s
        addhn   v1.4h, v0.4s, v22.4s
        smull2  v2.4s, v9.8h, v2.8h
        addhn2  v3.8h, v5.4s, v16.4s
        ldr     q18, [x0, #448]
        dup     v22.4s, w9
        mov     w9, #0x3130000
        addhn2  v1.8h, v6.4s, v2.4s
        str     q3, [sp, #464]
        sub     v0.8h, v18.8h, v19.8h
        ldr     q3, [x0, #464]
        stp     q19, q18, [sp, #144]
        sxtl    v5.4s, v0.4h
        str     q1, [sp, #496]
        sxtl2   v2.4s, v0.8h
        stp     q3, q20, [sp, #112]
        mul     v5.4s, v5.4s, v22.4s
        mul     v6.4s, v2.4s, v22.4s
        dup     v2.8h, w10
        mov     w10, #0x7b0a0000
        sub     v18.8h, v3.8h, v20.8h
        sshr    v5.4s, v5.4s, #16
        smull2  v16.4s, v0.8h, v2.8h
        sshr    v6.4s, v6.4s, #16
        smull   v0.4s, v0.4h, v2.4h
        mul     v5.4s, v5.4s, v12.4s
        sxtl    v25.4s, v18.4h
        mul     v6.4s, v6.4s, v12.4s
        mul     v25.4s, v25.4s, v22.4s
        addhn   v1.4h, v5.4s, v0.4s
        sxtl2   v30.4s, v18.8h
        movi    v20.4s, #0x2, lsl #24
        addhn2  v1.8h, v6.4s, v16.4s
        mul     v0.4s, v30.4s, v22.4s
        sshr    v5.4s, v25.4s, #16
        str     q1, [sp, #448]
        ldr     q1, [sp, #528]
        mul     v5.4s, v5.4s, v12.4s
        smull   v6.4s, v18.4h, v2.4h
        sshr    v0.4s, v0.4s, #16
        stp     q1, q15, [x0, #416]
        smull2  v16.4s, v18.8h, v2.8h
        mul     v0.4s, v0.4s, v12.4s
        addhn   v1.4h, v5.4s, v6.4s
        ldp     q3, q28, [x0, #416]
        add     v19.8h, v27.8h, v8.8h
        addhn2  v1.8h, v0.4s, v16.4s
        movi    v27.4s, #0x2, lsl #24
        str     q3, [sp, #80]
        str     q1, [sp, #240]
        ldp     q5, q15, [x0, #480]
        movi    v30.4s, #0x2, lsl #24
        smlal   v27.4s, v19.4h, v13.4h
        movi    v14.4s, #0x2, lsl #24
        sub     v0.8h, v5.8h, v3.8h
        stp     q28, q5, [sp, #16]
        movi    v5.4s, #0x2, lsl #24
        sxtl    v6.4s, v0.4h
        sxtl2   v18.4s, v0.8h
        mul     v6.4s, v6.4s, v22.4s
        mul     v18.4s, v18.4s, v22.4s
        ldp     q3, q1, [sp, #352]
        smull   v25.4s, v0.4h, v2.4h
        sshr    v27.4s, v27.4s, #26
        sshr    v6.4s, v6.4s, #16
        sshr    v18.4s, v18.4s, #16
        mul     v6.4s, v6.4s, v12.4s
        smull2  v0.4s, v0.8h, v2.8h
        mul     v18.4s, v18.4s, v12.4s
        add     v16.8h, v1.8h, v3.8h
        addhn   v1.4h, v6.4s, v25.4s
        smlal   v5.4s, v16.4h, v13.4h
        smlal2  v21.4s, v16.8h, v13.8h
        addhn2  v1.8h, v18.4s, v0.4s
        movi    v25.4s, #0x2, lsl #24
        sshr    v5.4s, v5.4s, #26
        str     q1, [sp, #528]
        sshr    v6.4s, v21.4s, #26
        ldp     q3, q1, [sp, #320]
        uzp1    v0.8h, v5.8h, v6.8h
        movi    v5.4s, #0x2, lsl #24
        movi    v6.4s, #0x2, lsl #24
        mla     v16.8h, v0.8h, v11.8h
        add     v18.8h, v3.8h, v1.8h
        ldp     q3, q1, [sp, #192]
        smlal   v5.4s, v18.4h, v13.4h
        smlal2  v6.4s, v18.8h, v13.8h
        sshr    v5.4s, v5.4s, #26
        add     v21.8h, v1.8h, v3.8h
        sshr    v6.4s, v6.4s, #26
        ldp     q3, q1, [sp, #48]
        uzp1    v5.8h, v5.8h, v6.8h
        smlal   v25.4s, v21.4h, v13.4h
        smlal2  v29.4s, v21.8h, v13.8h
        mla     v18.8h, v5.8h, v11.8h
        add     v5.8h, v3.8h, v1.8h
        ldr     q1, [sp, #96]
        sshr    v6.4s, v25.4s, #26
        movi    v25.4s, #0x2, lsl #24
        sshr    v0.4s, v29.4s, #26
        add     v24.8h, v1.8h, v24.8h
        stp     q16, q18, [x0]
        movi    v29.4s, #0x2, lsl #24
        ldr     q3, [x0]
        uzp1    v0.8h, v6.8h, v0.8h
        movi    v6.4s, #0x2, lsl #24
        smlal   v25.4s, v24.4h, v13.4h
        smlal2  v20.4s, v24.8h, v13.8h
        smlal2  v29.4s, v19.8h, v13.8h
        smlal   v6.4s, v5.4h, v13.4h
        smlal2  v30.4s, v5.8h, v13.8h
        sshr    v20.4s, v20.4s, #26
        sshr    v25.4s, v25.4s, #26
        sshr    v29.4s, v29.4s, #26
        sshr    v6.4s, v6.4s, #26
        uzp1    v20.8h, v25.8h, v20.8h
        uzp1    v25.8h, v27.8h, v29.8h
        sshr    v27.4s, v30.4s, #26
        mla     v21.8h, v0.8h, v11.8h
        dup     v29.4s, w9
        uzp1    v0.8h, v6.8h, v27.8h
        mov     w9, #0xfa13
        mla     v24.8h, v20.8h, v11.8h
        movi    v6.4s, #0x2, lsl #24
        movi    v20.4s, #0x2, lsl #24
        movi    v16.4s, #0x2, lsl #24
        mla     v19.8h, v25.8h, v11.8h
        smlal   v6.4s, v17.4h, v13.4h
        smlal2  v20.4s, v17.8h, v13.8h
        smlal2  v16.4s, v7.8h, v13.8h
        mla     v5.8h, v0.8h, v11.8h
        stp     q24, q19, [x0, #128]
        sshr    v6.4s, v6.4s, #26
        sshr    v18.4s, v20.4s, #26
        dup     v27.8h, w9
        ldp     q1, q19, [x0, #128]
        uzp1    v0.8h, v6.8h, v18.8h
        sshr    v6.4s, v16.4s, #26
        sub     v16.8h, v15.8h, v28.8h
        stp     q21, q5, [x0, #32]
        uzp1    v4.8h, v4.8h, v6.8h
        mov     w9, #0x39990000
        sxtl    v6.4s, v16.4h
        stp     q3, q1, [sp, #192]
        mla     v17.8h, v0.8h, v11.8h
        mul     v0.4s, v6.4s, v22.4s
        str     q19, [sp, #64]
        sub     v18.8h, v1.8h, v3.8h
        ldr     q8, [sp, #64]
        mla     v7.8h, v4.8h, v11.8h
        sxtl    v5.4s, v18.4h
        sshr    v0.4s, v0.4s, #16
        smull2  v4.4s, v16.8h, v2.8h
        smull   v2.4s, v16.4h, v2.4h
        stp     q17, q7, [x0, #160]
        sxtl2   v6.4s, v16.8h
        mul     v16.4s, v0.4s, v12.4s
        ldr     q0, [x0, #16]
        mul     v5.4s, v5.4s, v29.4s
        sxtl2   v17.4s, v18.8h
        sub     v19.8h, v19.8h, v0.8h
        str     q0, [sp, #96]
        addhn   v3.4h, v16.4s, v2.4s
        sxtl    v20.4s, v19.4h
        sshr    v2.4s, v5.4s, #16
        ldr     q5, [x0, #160]
        mul     v20.4s, v20.4s, v29.4s
        mul     v2.4s, v2.4s, v12.4s
        smull   v16.4s, v18.4h, v27.4h
        str     q5, [sp]
        mul     v6.4s, v6.4s, v22.4s
        sshr    v7.4s, v20.4s, #16
        smull   v20.4s, v19.4h, v27.4h
        addhn   v0.4h, v2.4s, v16.4s
        mul     v16.4s, v17.4s, v29.4s
        sxtl2   v17.4s, v19.8h
        mul     v7.4s, v7.4s, v12.4s
        mul     v17.4s, v17.4s, v29.4s
        ldp     q2, q31, [x0, #32]
        sshr    v6.4s, v6.4s, #16
        addhn   v1.4h, v7.4s, v20.4s
        sshr    v7.4s, v16.4s, #16
        sshr    v17.4s, v17.4s, #16
        sub     v16.8h, v5.8h, v2.8h
        str     q2, [sp, #48]
        smull2  v18.4s, v18.8h, v27.8h
        mul     v7.4s, v7.4s, v12.4s
        ldr     q20, [x0, #176]
        smull2  v19.4s, v19.8h, v27.8h
        ldr     q2, [sp, #576]
        mul     v17.4s, v17.4s, v12.4s
        mul     v6.4s, v6.4s, v12.4s
        sxtl    v25.4s, v16.4h
        addhn2  v0.8h, v7.4s, v18.4s
        mul     v25.4s, v25.4s, v29.4s
        addhn2  v1.8h, v17.4s, v19.4s
        addhn2  v3.8h, v6.4s, v4.4s
        sxtl2   v4.4s, v16.8h
        stp     q1, q0, [sp, #352]
        ldr     q0, [sp, #544]
        sshr    v25.4s, v25.4s, #16
        str     q3, [sp, #320]
        mul     v4.4s, v4.4s, v29.4s
        sub     v6.8h, v20.8h, v31.8h
        stp     q2, q0, [x0, #64]
        mul     v25.4s, v25.4s, v12.4s
        ldp     q2, q0, [sp, #288]
        smull   v26.4s, v16.4h, v27.4h
        sxtl    v7.4s, v6.4h
        sshr    v4.4s, v4.4s, #16
        mul     v7.4s, v7.4s, v29.4s
        stp     q2, q0, [x0, #192]
        addhn   v1.4h, v25.4s, v26.4s
        smull2  v17.4s, v16.8h, v27.8h
        mul     v4.4s, v4.4s, v12.4s
        ldp     q24, q26, [x0, #192]
        sxtl2   v16.4s, v6.8h
        sshr    v7.4s, v7.4s, #16
        smull   v18.4s, v6.4h, v27.4h
        mul     v16.4s, v16.4s, v29.4s
        addhn2  v1.8h, v4.4s, v17.4s
        mul     v7.4s, v7.4s, v12.4s
        ldp     q22, q21, [x0, #64]
        sshr    v16.4s, v16.4s, #16
        str     q1, [sp, #544]
        smull2  v25.4s, v6.8h, v27.8h
        addhn   v0.4h, v7.4s, v18.4s
        sub     v4.8h, v24.8h, v22.8h
        mul     v28.4s, v16.4s, v12.4s
        sxtl    v17.4s, v4.4h
        sxtl2   v7.4s, v4.8h
        mul     v17.4s, v17.4s, v29.4s
        mul     v7.4s, v7.4s, v29.4s
        addhn2  v0.8h, v28.4s, v25.4s
        smull2  v25.4s, v4.8h, v27.8h
        sshr    v17.4s, v17.4s, #16
        smull   v4.4s, v4.4h, v27.4h
        sshr    v7.4s, v7.4s, #16
        mul     v17.4s, v17.4s, v12.4s
        str     q0, [sp, #576]
        mul     v7.4s, v7.4s, v12.4s
        sub     v28.8h, v26.8h, v21.8h
        ldp     q18, q16, [x0, #224]
        addhn   v0.4h, v17.4s, v4.4s
        sxtl    v30.4s, v28.4h
        sxtl2   v10.4s, v28.8h
        addhn2  v0.8h, v7.4s, v25.4s
        mul     v9.4s, v30.4s, v29.4s
        mul     v4.4s, v10.4s, v29.4s
        str     q0, [sp, #336]
        ldr     q1, [sp, #592]
        smull2  v23.4s, v28.8h, v27.8h
        sshr    v17.4s, v9.4s, #16
        ldr     q0, [sp, #480]
        mul     v7.4s, v17.4s, v12.4s
        sshr    v4.4s, v4.4s, #16
        smull   v17.4s, v28.4h, v27.4h
        stp     q1, q0, [x0, #96]
        mul     v25.4s, v4.4s, v12.4s
        ldp     q19, q30, [x0, #96]
        addhn   v1.4h, v7.4s, v17.4s
        movi    v11.4s, #0x2, lsl #24
        mvni    v4.8h, #0xd, lsl #8
        addhn2  v1.8h, v25.4s, v23.4s
        sub     v23.8h, v18.8h, v19.8h
        movi    v25.4s, #0x2, lsl #24
        sxtl    v9.4s, v23.4h
        str     q1, [sp, #592]
        ldp     q1, q0, [sp, #416]
        mul     v9.4s, v9.4s, v29.4s
        sxtl2   v10.4s, v23.8h
        smull2  v2.4s, v23.8h, v27.8h
        mul     v10.4s, v10.4s, v29.4s
        sshr    v9.4s, v9.4s, #16
        add     v28.8h, v1.8h, v0.8h
        ldp     q3, q1, [sp, #384]
        mul     v9.4s, v9.4s, v12.4s
        sshr    v10.4s, v10.4s, #16
        smull   v0.4s, v23.4h, v27.4h
        smlal   v25.4s, v28.4h, v13.4h
        smlal2  v11.4s, v28.8h, v13.8h
        mul     v10.4s, v10.4s, v12.4s
        addhn   v23.4h, v9.4s, v0.4s
        sshr    v25.4s, v25.4s, #26
        sshr    v0.4s, v11.4s, #26
        add     v5.8h, v3.8h, v1.8h
        ldp     q3, q1, [sp, #256]
        addhn2  v23.8h, v10.4s, v2.4s
        uzp1    v0.8h, v25.8h, v0.8h
        movi    v2.4s, #0x2, lsl #24
        movi    v25.4s, #0x2, lsl #24
        movi    v9.4s, #0x2, lsl #24
        movi    v10.4s, #0x2, lsl #24
        add     v11.8h, v1.8h, v3.8h
        ldr     q1, [sp, #176]
        smlal   v2.4s, v5.4h, v13.4h
        smlal2  v25.4s, v5.8h, v13.8h
        smlal   v9.4s, v11.4h, v13.4h
        smlal2  v10.4s, v11.8h, v13.8h
        sshr    v2.4s, v2.4s, #26
        sshr    v25.4s, v25.4s, #26
        mla     v28.8h, v0.8h, v4.8h
        uzp1    v2.8h, v2.8h, v25.8h
        sshr    v0.4s, v10.4s, #26
        sshr    v25.4s, v9.4s, #26
        add     v20.8h, v20.8h, v31.8h
        uzp1    v3.8h, v25.8h, v0.8h
        ldr     q0, [sp, #224]
        mla     v5.8h, v2.8h, v4.8h
        movi    v2.4s, #0x2, lsl #24
        add     v9.8h, v1.8h, v0.8h
        ldp     q1, q0, [sp, #144]
        movi    v25.4s, #0x2, lsl #24
        stp     q28, q5, [x0, #256]
        smlal   v2.4s, v9.4h, v13.4h
        mla     v11.8h, v3.8h, v4.8h
        movi    v3.4s, #0x2, lsl #24
        smlal2  v25.4s, v9.8h, v13.8h
        add     v10.8h, v0.8h, v1.8h
        ldr     q5, [sp, #512]
        movi    v0.4s, #0x2, lsl #24
        str     q11, [x0, #288]
        movi    v1.4s, #0x2, lsl #24
        sshr    v25.4s, v25.4s, #26
        str     q5, [x0, #336]
        sshr    v2.4s, v2.4s, #26
        smlal   v0.4s, v10.4h, v13.4h
        smlal2  v1.4s, v10.8h, v13.8h
        uzp1    v2.8h, v2.8h, v25.8h
        movi    v31.4s, #0x2, lsl #24
        sshr    v0.4s, v0.4s, #26
        sshr    v1.4s, v1.4s, #26
        mla     v9.8h, v2.8h, v4.8h
        uzp1    v1.8h, v0.8h, v1.8h
        ldp     q6, q0, [sp, #112]
        movi    v2.4s, #0x2, lsl #24
        smlal2  v31.4s, v20.8h, v13.8h
        mla     v10.8h, v1.8h, v4.8h
        add     v26.8h, v26.8h, v21.8h
        add     v25.8h, v6.8h, v0.8h
        ldr     q0, [sp, #80]
        ldr     q6, [sp, #32]
        smlal   v2.4s, v25.4h, v13.4h
        smlal2  v3.4s, v25.8h, v13.8h
        add     v6.8h, v6.8h, v0.8h
        movi    v0.4s, #0x2, lsl #24
        sshr    v2.4s, v2.4s, #26
        sshr    v3.4s, v3.4s, #26
        smlal2  v14.4s, v6.8h, v13.8h
        smlal   v0.4s, v6.4h, v13.4h
        uzp1    v2.8h, v2.8h, v3.8h
        ldr     q3, [sp, #16]
        sshr    v1.4s, v14.4s, #26
        add     v15.8h, v15.8h, v3.8h
        sshr    v0.4s, v0.4s, #26
        ldp     q7, q3, [sp, #192]
        mla     v25.8h, v2.8h, v4.8h
        uzp1    v0.8h, v0.8h, v1.8h
        movi    v1.4s, #0x2, lsl #24
        movi    v2.4s, #0x2, lsl #24
        movi    v14.4s, #0x2, lsl #24
        stp     q10, q25, [x0, #384]
        add     v17.8h, v3.8h, v7.8h
        ldr     q7, [sp, #96]
        movi    v3.4s, #0x2, lsl #24
        ldr     q25, [sp, #496]
        smlal   v1.4s, v15.4h, v13.4h
        smlal2  v2.4s, v15.8h, v13.8h
        smlal2  v14.4s, v17.8h, v13.8h
        smlal   v3.4s, v17.4h, v13.4h
        sshr    v1.4s, v1.4s, #26
        sshr    v2.4s, v2.4s, #26
        mla     v6.8h, v0.8h, v4.8h
        uzp1    v1.8h, v1.8h, v2.8h
        sshr    v2.4s, v14.4s, #26
        movi    v14.4s, #0x2, lsl #24
        sshr    v3.4s, v3.4s, #26
        movi    v0.4s, #0x2, lsl #24
        add     v7.8h, v8.8h, v7.8h
        ldr     q8, [sp]
        uzp1    v2.8h, v3.8h, v2.8h
        smlal   v14.4s, v7.4h, v13.4h
        smlal2  v0.4s, v7.8h, v13.8h
        mla     v15.8h, v1.8h, v4.8h
        mla     v17.8h, v2.8h, v4.8h
        ldr     q2, [sp, #48]
        sshr    v1.4s, v14.4s, #26
        sshr    v0.4s, v0.4s, #26
        movi    v3.4s, #0x2, lsl #24
        stp     q6, q15, [x0, #416]
        movi    v14.4s, #0x2, lsl #24
        add     v2.8h, v8.8h, v2.8h
        uzp1    v0.8h, v1.8h, v0.8h
        add     v1.8h, v24.8h, v22.8h
        movi    v24.4s, #0x2, lsl #24
        smlal   v3.4s, v2.4h, v13.4h
        smlal2  v14.4s, v2.8h, v13.8h
        movi    v8.4s, #0x2, lsl #24
        smlal   v24.4s, v20.4h, v13.4h
        sshr    v3.4s, v3.4s, #26
        sshr    v22.4s, v14.4s, #26
        movi    v14.4s, #0x2, lsl #24
        uzp1    v3.8h, v3.8h, v22.8h
        sshr    v22.4s, v31.4s, #26
        sshr    v24.4s, v24.4s, #26
        smlal   v8.4s, v1.4h, v13.4h
        uzp1    v22.8h, v24.8h, v22.8h
        smlal2  v14.4s, v1.8h, v13.8h
        mla     v2.8h, v3.8h, v4.8h
        movi    v3.4s, #0x2, lsl #24
        mla     v20.8h, v22.8h, v4.8h
        movi    v22.4s, #0x2, lsl #24
        sshr    v31.4s, v14.4s, #26
        sshr    v8.4s, v8.4s, #26
        smlal   v3.4s, v26.4h, v13.4h
        stp     q2, q20, [x0, #32]
        uzp1    v24.8h, v8.8h, v31.8h
        smlal2  v22.4s, v26.8h, v13.8h
        mla     v7.8h, v0.8h, v4.8h
        add     v0.8h, v18.8h, v19.8h
        movi    v18.4s, #0x2, lsl #24
        movi    v19.4s, #0x2, lsl #24
        mla     v1.8h, v24.8h, v4.8h
        stp     q17, q7, [x0]
        sshr    v4.4s, v22.4s, #26
        ldr     q17, [sp, #352]
        sshr    v3.4s, v3.4s, #26
        smlal   v18.4s, v0.4h, v13.4h
        uzp1    v3.8h, v3.8h, v4.8h
        ldr     q4, [sp, #560]
        smlal2  v19.4s, v0.8h, v13.8h
        mvni    v14.8h, #0xd, lsl #8
        stp     q9, q4, [x0, #304]
        sshr    v18.4s, v18.4s, #26
        sub     v4.8h, v16.8h, v30.8h
        sshr    v19.4s, v19.4s, #26
        sxtl    v21.4s, v4.4h
        uzp1    v18.8h, v18.8h, v19.8h
        mul     v19.4s, v21.4s, v29.4s
        sxtl2   v21.4s, v4.8h
        mla     v26.8h, v3.8h, v14.8h
        mul     v3.4s, v21.4s, v29.4s
        sshr    v19.4s, v19.4s, #16
        mla     v0.8h, v18.8h, v14.8h
        mul     v18.4s, v19.4s, v12.4s
        stp     q1, q26, [x0, #64]
        smull   v19.4s, v4.4h, v27.4h
        sshr    v3.4s, v3.4s, #16
        smull2  v4.4s, v4.8h, v27.8h
        ldp     q29, q27, [sp, #448]
        mul     v3.4s, v3.4s, v12.4s
        addhn   v5.4h, v18.4s, v19.4s
        add     v21.8h, v16.8h, v30.8h
        stp     q27, q25, [x0, #352]
        ldp     q16, q24, [x0, #384]
        addhn2  v5.8h, v3.4s, v4.4s
        movi    v3.4s, #0x2, lsl #24
        movi    v18.4s, #0x2, lsl #24
        movi    v4.4s, #0x2, lsl #24
        stp     q23, q5, [x0, #224]
        movi    v8.4s, #0x2, lsl #24
        ldp     q19, q22, [x0, #256]
        smlal2  v3.4s, v21.8h, v13.8h
        smlal   v18.4s, v21.4h, v13.4h
        movi    v20.4s, #0x2, lsl #24
        add     v11.8h, v16.8h, v19.8h
        sub     v16.8h, v16.8h, v19.8h
        movi    v19.4s, #0x2, lsl #24
        ldr     q30, [sp, #528]
        smlal   v4.4s, v11.4h, v13.4h
        sshr    v25.4s, v3.4s, #26
        sxtl    v27.4s, v16.4h
        dup     v3.4s, w9
        smlal2  v19.4s, v11.8h, v13.8h
        mov     w9, #0xfe99
        sshr    v18.4s, v18.4s, #26
        mul     v27.4s, v27.4s, v3.4s
        sshr    v4.4s, v4.4s, #26
        uzp1    v18.8h, v18.8h, v25.8h
        ldr     q25, [sp, #240]
        sshr    v19.4s, v19.4s, #26
        add     v28.8h, v24.8h, v22.8h
        stp     q29, q25, [x0, #448]
        sshr    v25.4s, v27.4s, #16
        uzp1    v19.8h, v4.8h, v19.8h
        dup     v4.8h, w9
        mul     v25.4s, v25.4s, v12.4s
        ldr     q29, [sp, #320]
        smull   v27.4s, v16.4h, v4.4h
        mov     w9, #0xfd0a
        mla     v21.8h, v18.8h, v14.8h
        mla     v11.8h, v19.8h, v14.8h
        stp     q30, q29, [x0, #480]
        sxtl2   v18.4s, v16.8h
        ldr     q30, [sp, #368]
        addhn   v19.4h, v25.4s, v27.4s
        movi    v25.4s, #0x2, lsl #24
        stp     q0, q21, [x0, #96]
        movi    v27.4s, #0x2, lsl #24
        stp     q30, q17, [x0, #128]
        mul     v18.4s, v18.4s, v3.4s
        ldr     q30, [sp, #544]
        sub     v22.8h, v24.8h, v22.8h
        ldr     q17, [sp, #576]
        smlal   v25.4s, v28.4h, v13.4h
        smlal2  v27.4s, v28.8h, v13.8h
        smull2  v6.4s, v16.8h, v4.8h
        stp     q30, q17, [x0, #160]
        sshr    v16.4s, v18.4s, #16
        ldr     q17, [sp, #592]
        sshr    v24.4s, v25.4s, #26
        sshr    v18.4s, v27.4s, #26
        sxtl    v25.4s, v22.4h
        uzp1    v18.8h, v24.8h, v18.8h
        mul     v24.4s, v25.4s, v3.4s
        sxtl2   v25.4s, v22.8h
        smull   v27.4s, v22.4h, v4.4h
        mul     v25.4s, v25.4s, v3.4s
        sshr    v24.4s, v24.4s, #16
        mul     v16.4s, v16.4s, v12.4s
        mul     v24.4s, v24.4s, v12.4s
        sshr    v25.4s, v25.4s, #16
        smull2  v31.4s, v22.8h, v4.8h
        mul     v25.4s, v25.4s, v12.4s
        addhn   v22.4h, v24.4s, v27.4s
        addhn2  v19.8h, v16.4s, v6.4s
        mla     v28.8h, v18.8h, v14.8h
        ldp     q16, q18, [x0, #288]
        addhn2  v22.8h, v25.4s, v31.4s
        movi    v25.4s, #0x2, lsl #24
        movi    v10.4s, #0x2, lsl #24
        stp     q11, q28, [x0, #256]
        movi    v21.4s, #0x2, lsl #24
        stp     q19, q22, [x0, #384]
        movi    v22.4s, #0x2, lsl #24
        ldp     q6, q31, [x0, #416]
        sub     v27.8h, v6.8h, v16.8h
        add     v24.8h, v6.8h, v16.8h
        sxtl    v9.4s, v27.4h
        sxtl2   v16.4s, v27.8h
        mul     v6.4s, v9.4s, v3.4s
        mul     v16.4s, v16.4s, v3.4s
        smlal   v25.4s, v24.4h, v13.4h
        smlal2  v8.4s, v24.8h, v13.8h
        sshr    v6.4s, v6.4s, #16
        smull   v29.4s, v27.4h, v4.4h
        sshr    v16.4s, v16.4s, #16
        mul     v6.4s, v6.4s, v12.4s
        sshr    v7.4s, v8.4s, #26
        sshr    v25.4s, v25.4s, #26
        smull2  v8.4s, v27.8h, v4.8h
        mul     v16.4s, v16.4s, v12.4s
        addhn   v27.4h, v6.4s, v29.4s
        uzp1    v6.8h, v25.8h, v7.8h
        sub     v7.8h, v31.8h, v18.8h
        addhn2  v27.8h, v16.4s, v8.4s
        sxtl    v16.4s, v7.4h
        add     v29.8h, v31.8h, v18.8h
        mul     v16.4s, v16.4s, v3.4s
        sxtl2   v18.4s, v7.8h
        smull   v31.4s, v7.4h, v4.4h
        mul     v18.4s, v18.4s, v3.4s
        sshr    v16.4s, v16.4s, #16
        smull2  v7.4s, v7.8h, v4.8h
        mul     v16.4s, v16.4s, v12.4s
        sshr    v2.4s, v18.4s, #16
        movi    v25.4s, #0x2, lsl #24
        mul     v18.4s, v2.4s, v12.4s
        addhn   v2.4h, v16.4s, v31.4s
        ldp     q16, q9, [x0, #448]
        smlal   v25.4s, v29.4h, v13.4h
        addhn2  v2.8h, v18.4s, v7.4s
        movi    v7.4s, #0x2, lsl #24
        smlal2  v20.4s, v29.8h, v13.8h
        sshr    v25.4s, v25.4s, #26
        stp     q27, q2, [x0, #416]
        ldp     q31, q8, [x0, #320]
        mla     v24.8h, v6.8h, v14.8h
        sshr    v20.4s, v20.4s, #26
        add     v18.8h, v16.8h, v31.8h
        uzp1    v6.8h, v25.8h, v20.8h
        smlal   v7.4s, v18.4h, v13.4h
        smlal2  v10.4s, v18.8h, v13.8h
        sub     v16.8h, v16.8h, v31.8h
        mla     v29.8h, v6.8h, v14.8h
        sshr    v7.4s, v7.4s, #26
        sshr    v1.4s, v10.4s, #26
        sxtl2   v20.4s, v16.8h
        uzp1    v1.8h, v7.8h, v1.8h
        stp     q24, q29, [x0, #288]
        sxtl    v7.4s, v16.4h
        mul     v6.4s, v20.4s, v3.4s
        ldr     q20, [sp, #336]
        mul     v7.4s, v7.4s, v3.4s
        mla     v18.8h, v1.8h, v14.8h
        stp     q20, q17, [x0, #192]
        sub     v20.8h, v9.8h, v8.8h
        sshr    v0.4s, v6.4s, #16
        sshr    v1.4s, v7.4s, #16
        sxtl    v25.4s, v20.4h
        smull   v7.4s, v16.4h, v4.4h
        mul     v1.4s, v1.4s, v12.4s
        mul     v25.4s, v25.4s, v3.4s
        sxtl2   v26.4s, v20.8h
        smull2  v16.4s, v16.8h, v4.8h
        mul     v5.4s, v26.4s, v3.4s
        addhn   v6.4h, v1.4s, v7.4s
        add     v7.8h, v9.8h, v8.8h
        sshr    v23.4s, v25.4s, #16
        smlal2  v21.4s, v7.8h, v13.8h
        sshr    v5.4s, v5.4s, #16
        smull   v25.4s, v20.4h, v4.4h
        mul     v23.4s, v23.4s, v12.4s
        movi    v1.4s, #0x2, lsl #24
        mul     v0.4s, v0.4s, v12.4s
        smull2  v20.4s, v20.8h, v4.8h
        mul     v5.4s, v5.4s, v12.4s
        sshr    v17.4s, v21.4s, #26
        addhn   v21.4h, v23.4s, v25.4s
        smlal   v1.4s, v7.4h, v13.4h
        addhn2  v6.8h, v0.4s, v16.4s
        ldp     q0, q16, [x0, #352]
        addhn2  v21.8h, v5.4s, v20.4s
        sshr    v1.4s, v1.4s, #26
        movi    v20.4s, #0x2, lsl #24
        movi    v25.4s, #0x2, lsl #24
        stp     q6, q21, [x0, #448]
        uzp1    v1.8h, v1.8h, v17.8h
        ldp     q23, q5, [x0, #480]
        mla     v7.8h, v1.8h, v14.8h
        add     v17.8h, v23.8h, v0.8h
        sub     v0.8h, v23.8h, v0.8h
        smlal   v20.4s, v17.4h, v13.4h
        smlal2  v25.4s, v17.8h, v13.8h
        stp     q18, q7, [x0, #320]
        movi    v23.4s, #0x2, lsl #24
        sxtl    v1.4s, v0.4h
        sshr    v20.4s, v20.4s, #26
        sshr    v19.4s, v25.4s, #26
        add     v24.8h, v5.8h, v16.8h
        mul     v1.4s, v1.4s, v3.4s
        uzp1    v19.8h, v20.8h, v19.8h
        smlal   v22.4s, v24.4h, v13.4h
        smlal2  v23.4s, v24.8h, v13.8h
        sshr    v1.4s, v1.4s, #16
        mla     v17.8h, v19.8h, v14.8h
        sshr    v19.4s, v22.4s, #26
        sshr    v2.4s, v23.4s, #26
        smull   v20.4s, v0.4h, v4.4h
        mul     v1.4s, v1.4s, v12.4s
        sub     v5.8h, v5.8h, v16.8h
        uzp1    v2.8h, v19.8h, v2.8h
        sxtl    v19.4s, v5.4h
        addhn   v1.4h, v1.4s, v20.4s
        mvni    v20.8h, #0xd, lsl #8
        mul     v19.4s, v19.4s, v3.4s
        sxtl2   v16.4s, v0.8h
        mla     v24.8h, v2.8h, v20.8h
        sxtl2   v2.4s, v5.8h
        mul     v16.4s, v16.4s, v3.4s
        mul     v2.4s, v2.4s, v3.4s
        sshr    v7.4s, v19.4s, #16
        stp     q17, q24, [x0, #352]
        smull   v3.4s, v5.4h, v4.4h
        mul     v7.4s, v7.4s, v12.4s
        sshr    v6.4s, v16.4s, #16
        sshr    v2.4s, v2.4s, #16
        mvni    v16.4s, #0xd, lsl #8
        smull2  v0.4s, v0.8h, v4.8h
        smull2  v4.4s, v5.8h, v4.8h
        mul     v5.4s, v6.4s, v16.4s
        mul     v2.4s, v2.4s, v16.4s
        addhn   v3.4h, v7.4s, v3.4s
        addhn2  v1.8h, v5.4s, v0.4s
        addhn2  v3.8h, v2.4s, v4.4s
        stp     q1, q3, [x0, #480]
Lbe00:
        add     x11, x0, x8
        dup     v4.4s, w10
        movi    v1.4s, #0x2, lsl #24
        add     x8, x8, #0x10
        movi    v3.4s, #0x2, lsl #24
        cmp     x8, #0x100
        ldr     q0, [x11]
        ldr     q2, [x11, #256]
        add     v5.8h, v2.8h, v0.8h
        sub     v0.8h, v2.8h, v0.8h
        smlal   v1.4s, v5.4h, v13.4h
        sxtl    v2.4s, v0.4h
        smlal2  v3.4s, v5.8h, v13.8h
        mul     v2.4s, v2.4s, v4.4s
        sxtl2   v6.4s, v0.8h
        sshr    v1.4s, v1.4s, #26
        mul     v4.4s, v6.4s, v4.4s
        sshr    v3.4s, v3.4s, #26
        dup     v6.8h, w9
        sshr    v2.4s, v2.4s, #16
        uzp1    v1.8h, v1.8h, v3.8h
        smull   v3.4s, v0.4h, v6.4h
        mul     v2.4s, v2.4s, v16.4s
        sshr    v4.4s, v4.4s, #16
        smull2  v0.4s, v0.8h, v6.8h
        mul     v4.4s, v4.4s, v16.4s
        addhn   v2.4h, v2.4s, v3.4s
        mla     v5.8h, v1.8h, v20.8h
        addhn2  v2.8h, v4.4s, v0.4s
        str     q5, [x11]
        str     q2, [x11, #256]
        b.ne    Lbe00
        add     sp, sp, #0x260
        ldp     d9, d8, [sp, #48]
        ldp     d11, d10, [sp, #32]
        ldp     d13, d12, [sp, #16]
        ldr     x29, [sp, #64]
        ldp     d15, d14, [sp], #80
        ret

// mlkem512_polyvec_compress_du (0x28 bytes)
Lbe9c:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L2d14
        add     x0, x20, #0x140
        add     x1, x19, #0x200
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L2d14

// mlkem512_polyvec_decompress_du (0x28 bytes)
Lbec4:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L317c
        add     x0, x20, #0x200
        add     x1, x19, #0x140
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L317c

// mlkem512_polyvec_tobytes (0x28 bytes)
Lbeec:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L4080
        add     x0, x20, #0x180
        add     x1, x19, #0x200
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L4080

// mlkem512_polyvec_frombytes (0x28 bytes)
Lbf14:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L42d0
        add     x0, x20, #0x200
        add     x1, x19, #0x180
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L42d0

// mlkem512_polyvec_ntt (0x18 bytes)
Lbf3c:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L8c28
        add     x0, x19, #0x200
        ldp     x30, x19, [sp], #16
        b       L8c28

// mlkem512_polyvec_invntt_tomont (0x18 bytes)
Lbf54:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      La46c
        add     x0, x19, #0x200
        ldp     x30, x19, [sp], #16
        b       La46c

// mlkem512_polyvec_basemul_acc_montgomery_cached (0x1b0 bytes)
Lbf6c:
        add     x8, x3, #0x200
        add     x10, x0, #0x200
        cmp     x8, x0
        add     x9, x2, #0x400
        ccmp    x10, x3, #0x0, hi
        add     x11, x1, #0x400
        cset    w8, hi
        cmp     x9, x0
        ccmp    x10, x2, #0x0, hi
        cset    w9, hi
        cmp     x10, x1
        ccmp    x11, x0, #0x0, hi
        b.hi    Lc07c
        tbnz    w8, #0, Lc07c
        cbnz    w9, Lc07c
        mov     w10, #0xf3010000
        mov     x8, xzr
        add     x9, x3, #0x100
        mvni    v1.4s, #0xd, lsl #8
        dup     v0.4s, w10
Lbfbc:
        add     x10, x1, x8
        add     x11, x2, x8
        ldur    q17, [x9, #-256]
        ldr     q18, [x9], #16
        ld2     {v2.8h-v3.8h}, [x10]
        add     x10, x10, #0x200
        ld2     {v4.8h-v5.8h}, [x11]
        ld2     {v6.8h-v7.8h}, [x10]
        add     x10, x11, #0x200
        smull   v16.4s, v4.4h, v2.4h
        smull2  v19.4s, v4.8h, v2.8h
        ld2     {v21.8h-v22.8h}, [x10]
        smull   v20.4s, v5.4h, v2.4h
        add     x10, x0, x8
        smull2  v23.4s, v5.8h, v2.8h
        add     x8, x8, #0x20
        smlal   v16.4s, v17.4h, v3.4h
        cmp     x8, #0x200
        smlal2  v19.4s, v17.8h, v3.8h
        smlal   v20.4s, v4.4h, v3.4h
        smlal2  v23.4s, v4.8h, v3.8h
        smlal   v16.4s, v18.4h, v7.4h
        smlal2  v19.4s, v18.8h, v7.8h
        smlal   v20.4s, v21.4h, v7.4h
        smlal2  v23.4s, v21.8h, v7.8h
        smlal   v16.4s, v21.4h, v6.4h
        smlal2  v19.4s, v21.8h, v6.8h
        smlal   v20.4s, v22.4h, v6.4h
        smlal2  v23.4s, v22.8h, v6.8h
        mul     v2.4s, v16.4s, v0.4s
        mul     v3.4s, v19.4s, v0.4s
        mul     v4.4s, v20.4s, v0.4s
        mul     v5.4s, v23.4s, v0.4s
        sshr    v2.4s, v2.4s, #16
        sshr    v3.4s, v3.4s, #16
        mul     v2.4s, v2.4s, v1.4s
        sshr    v4.4s, v4.4s, #16
        mul     v3.4s, v3.4s, v1.4s
        addhn   v6.4h, v2.4s, v16.4s
        mul     v2.4s, v4.4s, v1.4s
        sshr    v4.4s, v5.4s, #16
        addhn2  v6.8h, v3.4s, v19.4s
        mul     v3.4s, v4.4s, v1.4s
        addhn   v7.4h, v2.4s, v20.4s
        addhn2  v7.8h, v3.4s, v23.4s
        st2     {v6.8h-v7.8h}, [x10]
        b.ne    Lbfbc
        b       Lc118
Lc07c:
        mov     x8, xzr
        mov     w9, #0xf3010000
        add     x10, x3, #0x100
        mov     w11, #0xfffff2ff
Lc08c:
        add     x12, x1, x8
        add     x14, x2, x8
        ldursh  w13, [x10, #-256]
        ldrsh   w15, [x10]
        add     x10, x10, #0x2
        ldrsh   w16, [x12, #2]
        ldrsh   w17, [x14]
        ldrsh   w18, [x12]
        ldrsh   w3, [x14, #2]
        mul     w13, w13, w16
        mul     w16, w17, w16
        ldrsh   w4, [x12, #514]
        madd    w13, w17, w18, w13
        ldrsh   w17, [x14, #512]
        madd    w16, w3, w18, w16
        ldrsh   w12, [x12, #512]
        ldrsh   w14, [x14, #514]
        madd    w13, w15, w4, w13
        madd    w15, w17, w4, w16
        madd    w13, w17, w12, w13
        madd    w12, w14, w12, w15
        mul     w14, w13, w9
        mul     w15, w12, w9
        asr     w14, w14, #16
        asr     w15, w15, #16
        madd    w13, w14, w11, w13
        add     x14, x0, x8
        madd    w12, w15, w11, w12
        add     x8, x8, #0x4
        lsr     w13, w13, #16
        cmp     x8, #0x200
        lsr     w12, w12, #16
        strh    w13, [x14]
        strh    w12, [x14, #2]
        b.ne    Lc08c
Lc118:
        ret

// mlkem512_polyvec_mulcache_compute (0x28 bytes)
Lc11c:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L867c
        add     x0, x20, #0x100
        add     x1, x19, #0x200
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L867c

// mlkem512_polyvec_reduce (0x18 bytes)
Lc144:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L832c
        add     x0, x19, #0x200
        ldp     x30, x19, [sp], #16
        b       L832c

// mlkem512_polyvec_add (0x28 bytes)
Lc15c:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L837c
        add     x0, x20, #0x200
        add     x1, x19, #0x200
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L837c

// mlkem512_polyvec_tomont (0x18 bytes)
Lc184:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L8298
        add     x0, x19, #0x200
        ldp     x30, x19, [sp], #16
        b       L8298

// mlkem512_poly_getnoise_eta1_4x (0x15c bytes)
Lc19c:
        stp     x29, x30, [sp, #-80]!
        stp     x28, x25, [sp, #16]
        stp     x24, x23, [sp, #32]
        stp     x22, x21, [sp, #48]
        stp     x20, x19, [sp, #64]
        mov     x29, sp
        sub     x9, sp, #0x430
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xf0000108  // adrp x8, 0x2f000
        ldrb    w10, [x29, #80]
        add     x11, sp, #0x20
        add     x12, sp, #0x120
        add     x9, x11, #0x80
        add     x24, x12, #0xc0
        ldr     x8, [x8, #4088]
        add     x25, x12, #0x180
        add     x20, x12, #0x240
        mov     x19, x3
        mov     x21, x2
        mov     x22, x1
        ldr     x8, [x8]
        mov     x23, x0
        add     x0, sp, #0x120
        mov     x1, x24
        mov     x2, x25
        mov     x3, x20
        str     x8, [sp, #1064]
        add     x8, x11, #0x40
        ldp     q0, q1, [x4]
        strb    w5, [sp, #64]
        add     x11, x11, #0xc0
        strb    w6, [sp, #128]
        add     x5, sp, #0x20
        strb    w7, [sp, #192]
        mov     w4, #0xc0
        strb    w10, [sp, #256]
        mov     w10, #0x21
        mov     x6, x8
        mov     x7, x9
        stp     q0, q1, [sp, #32]
        stp     q0, q1, [sp, #96]
        stp     q0, q1, [sp, #160]
        stp     q0, q1, [sp, #224]
        stp     x11, x10, [sp]
        bl      L5770
        add     x1, sp, #0x120
        mov     x0, x23
        bl      Lce28
        mov     x0, x22
        mov     x1, x24
        bl      Lce28
        mov     x0, x21
        mov     x1, x25
        bl      Lce28
        cbz     x19, Lc284
        mov     x0, x19
        mov     x1, x20
        bl      Lce28
Lc284:
        add     x0, sp, #0x120
        mov     w1, wzr
        mov     w2, #0x300
        add     x19, sp, #0x120
        bl      L0840
        movi    v0.2d, #0x0
        add     x8, sp, #0x20
        stp     q0, q0, [sp, #32]
        stp     q0, q0, [sp, #64]
        stp     q0, q0, [sp, #96]
        stp     q0, q0, [sp, #128]
        stp     q0, q0, [sp, #160]
        stp     q0, q0, [sp, #192]
        stp     q0, q0, [sp, #224]
        stp     q0, q0, [sp, #256]
        .inst   0xf0000108  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #1064]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    Lc2f4
        mov     sp, x29
        ldp     x20, x19, [sp, #64]
        ldp     x22, x21, [sp, #48]
        ldp     x24, x23, [sp, #32]
        ldp     x28, x25, [sp, #16]
        ldp     x29, x30, [sp], #80
        ret
Lc2f4:
        bl      L0830

// mlkem512_poly_getnoise_eta2 (0xac bytes)
Lc2f8:
        stp     x29, x30, [sp, #-48]!
        stp     x28, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0xd0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xf0000108  // adrp x8, 0x2f000
        mov     x19, x0
        add     x0, sp, #0x40
        mov     w3, #0x21
        add     x20, sp, #0x40
        mov     x21, sp
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #200]
        ldp     q0, q1, [x1]
        strb    w2, [sp, #32]
        mov     x2, sp
        mov     w1, #0x80
        stp     q0, q1, [sp]
        bl      L52f0
        add     x1, sp, #0x40
        mov     x0, x19
        bl      Lcc10
        movi    v0.2d, #0x0
        .inst   0xf0000108  // adrp x8, 0x2f000
        stp     q0, q0, [sp, #64]
        stp     q0, q0, [sp, #96]
        stp     q0, q0, [sp, #128]
        stp     q0, q0, [sp, #160]
        strb    wzr, [sp, #32]
        stp     q0, q0, [sp]
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #200]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    Lc3a0
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldp     x28, x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
Lc3a0:
        bl      L0830

// mlkem512_poly_getnoise_eta1122_4x (0x158 bytes)
Lc3a4:
        stp     x29, x30, [sp, #-96]!
        stp     x28, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0x440
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xf0000108  // adrp x8, 0x2f000
        ldrb    w10, [x29, #96]
        add     x26, sp, #0x20
        add     x27, sp, #0x120
        add     x9, x26, #0x80
        add     x23, x27, #0xc0
        ldr     x8, [x8, #4088]
        add     x24, x27, #0x180
        add     x25, x27, #0x240
        mov     x19, x3
        mov     x20, x2
        mov     x21, x1
        ldr     x8, [x8]
        mov     x22, x0
        add     x11, x26, #0xc0
        add     x0, sp, #0x120
        mov     x1, x23
        mov     x2, x24
        str     x8, [sp, #1080]
        add     x8, x26, #0x40
        ldp     q0, q1, [x4]
        strb    w5, [sp, #64]
        add     x5, sp, #0x20
        strb    w6, [sp, #128]
        mov     x3, x25
        strb    w7, [sp, #192]
        mov     w4, #0xc0
        strb    w10, [sp, #256]
        mov     w10, #0x21
        mov     x6, x8
        mov     x7, x9
        stp     q0, q1, [sp, #32]
        stp     q0, q1, [sp, #96]
        stp     q0, q1, [sp, #160]
        stp     q0, q1, [sp, #224]
        stp     x11, x10, [sp]
        bl      L5770
        add     x1, sp, #0x120
        mov     x0, x22
        bl      Lce28
        mov     x0, x21
        mov     x1, x23
        bl      Lce28
        mov     x0, x20
        mov     x1, x24
        bl      Lcc10
        mov     x0, x19
        mov     x1, x25
        bl      Lcc10
        add     x0, sp, #0x120
        mov     w1, wzr
        mov     w2, #0x300
        bl      L0840
        movi    v0.2d, #0x0
        .inst   0xf0000108  // adrp x8, 0x2f000
        stp     q0, q0, [sp, #32]
        stp     q0, q0, [sp, #64]
        stp     q0, q0, [sp, #96]
        stp     q0, q0, [sp, #128]
        stp     q0, q0, [sp, #160]
        stp     q0, q0, [sp, #192]
        stp     q0, q0, [sp, #224]
        stp     q0, q0, [sp, #256]
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #1080]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    Lc4f8
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
Lc4f8:
        bl      L0830

// mlkem_poly_rej_uniform_x4 (0x534 bytes)
Lc4fc:
        stp     x29, x30, [sp, #-96]!
        stp     x28, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0xb80
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xf0000108  // adrp x8, 0x2f000
        mov     x22, x0
        add     x0, sp, #0x40
        mov     x23, x4
        mov     x19, x3
        mov     x20, x2
        ldr     x8, [x8, #4088]
        mov     x21, x1
        ldr     x8, [x8]
        str     x8, [sp, #2936]
        bl      L5750
        add     x2, x23, #0x40
        add     x3, x23, #0x80
        add     x4, x23, #0xc0
        add     x0, sp, #0x40
        mov     x1, x23
        mov     w5, #0x22
        bl      L550c
        add     x23, sp, #0x360
        add     x0, sp, #0x360
        add     x1, x23, #0x200
        add     x2, x23, #0x400
        add     x3, x23, #0x600
        add     x5, sp, #0x40
        mov     w4, #0x3
        stp     x2, x1, [sp, #40]
        str     x3, [sp, #32]
        bl      L56d0
        mov     x8, xzr
        mov     x26, xzr
Lc598:
        add     x9, x23, x8
        ldrb    w11, [x9]
        ldrb    w10, [x9, #1]
        bfi     w11, w10, #8, #4
        cmp     w11, #0xd00
        b.hi    Lc5bc
        add     x12, x26, #0x1
        strh    w11, [x22, x26, lsl #1]
        mov     x26, x12
Lc5bc:
        cmp     x26, #0xff
        b.hi    Lc5e4
        ldrb    w9, [x9, #2]
        lsr     w10, w10, #4
        orr     w9, w10, w9, lsl #4
        cmp     w9, #0xd00
        b.hi    Lc5e4
        add     x10, x26, #0x1
        strh    w9, [x22, x26, lsl #1]
        mov     x26, x10
Lc5e4:
        cmp     x26, #0x100
        cset    w16, cc
        cmp     x26, #0xff
        b.hi    Lc604
        add     x9, x8, #0x3
        add     x8, x8, #0x3
        cmp     x9, #0x1f6
        b.cc    Lc598
Lc604:
        mov     x8, xzr
        mov     x27, xzr
        add     x9, sp, #0x360
Lc610:
        add     x10, x9, x8
        ldrb    w12, [x10, #512]
        ldrb    w11, [x10, #513]
        bfi     w12, w11, #8, #4
        cmp     w12, #0xd00
        b.hi    Lc634
        add     x13, x27, #0x1
        strh    w12, [x21, x27, lsl #1]
        mov     x27, x13
Lc634:
        cmp     x27, #0xff
        b.hi    Lc65c
        ldrb    w10, [x10, #514]
        lsr     w11, w11, #4
        orr     w10, w11, w10, lsl #4
        cmp     w10, #0xd00
        b.hi    Lc65c
        add     x11, x27, #0x1
        strh    w10, [x21, x27, lsl #1]
        mov     x27, x11
Lc65c:
        cmp     x27, #0x100
        cset    w15, cc
        cmp     x27, #0xff
        b.hi    Lc67c
        add     x10, x8, #0x3
        add     x8, x8, #0x3
        cmp     x10, #0x1f6
        b.cc    Lc610
Lc67c:
        mov     x8, xzr
        mov     x28, xzr
        add     x9, sp, #0x360
Lc688:
        add     x10, x9, x8
        ldrb    w12, [x10, #1024]
        ldrb    w11, [x10, #1025]
        bfi     w12, w11, #8, #4
        cmp     w12, #0xd00
        b.hi    Lc6ac
        add     x13, x28, #0x1
        strh    w12, [x20, x28, lsl #1]
        mov     x28, x13
Lc6ac:
        cmp     x28, #0xff
        b.hi    Lc6d4
        ldrb    w10, [x10, #1026]
        lsr     w11, w11, #4
        orr     w10, w11, w10, lsl #4
        cmp     w10, #0xd00
        b.hi    Lc6d4
        add     x11, x28, #0x1
        strh    w10, [x20, x28, lsl #1]
        mov     x28, x11
Lc6d4:
        cmp     x28, #0x100
        cset    w14, cc
        cmp     x28, #0xff
        b.hi    Lc6f4
        add     x10, x8, #0x3
        add     x8, x8, #0x3
        cmp     x10, #0x1f6
        b.cc    Lc688
Lc6f4:
        mov     x8, xzr
        mov     x23, xzr
        add     x9, sp, #0x360
Lc700:
        add     x10, x9, x8
        ldrb    w12, [x10, #1536]
        ldrb    w11, [x10, #1537]
        bfi     w12, w11, #8, #4
        cmp     w12, #0xd00
        b.hi    Lc724
        add     x13, x23, #0x1
        strh    w12, [x19, x23, lsl #1]
        mov     x23, x13
Lc724:
        cmp     x23, #0xff
        b.hi    Lc74c
        ldrb    w10, [x10, #1538]
        lsr     w11, w11, #4
        orr     w10, w11, w10, lsl #4
        cmp     w10, #0xd00
        b.hi    Lc74c
        add     x11, x23, #0x1
        strh    w10, [x19, x23, lsl #1]
        mov     x23, x11
Lc74c:
        cmp     x23, #0x100
        cset    w25, cc
        cmp     x23, #0xff
        b.hi    Lc76c
        add     x10, x8, #0x3
        add     x8, x8, #0x3
        cmp     x10, #0x1f6
        b.cc    Lc700
Lc76c:
        cmp     x26, #0x100
        str     x21, [sp, #24]
        b.cc    Lc790
        cmp     x27, #0x100
        b.cc    Lc790
        cmp     x28, #0x100
        b.cc    Lc790
        cmp     x23, #0xff
        b.hi    Lc9d8
Lc790:
        add     x24, sp, #0x360
        str     x22, [sp, #16]
Lc798:
        ldp     x2, x1, [sp, #40]
        add     x0, sp, #0x360
        add     x5, sp, #0x40
        ldr     x3, [sp, #32]
        mov     w4, #0x1
        str     w15, [sp, #60]
        mov     x21, x20
        mov     x20, x19
        mov     w19, w14
        mov     w22, w16
        bl      L56d0
        tbz     w22, #0, Lc844
        ldp     x22, x15, [sp, #16]
        mov     x8, xzr
        mov     w14, w19
        mov     x19, x20
        mov     x20, x21
Lc7dc:
        add     x9, x24, x8
        ldrb    w11, [x9]
        ldrb    w10, [x9, #1]
        bfi     w11, w10, #8, #4
        cmp     w11, #0xd00
        b.hi    Lc800
        add     x12, x26, #0x1
        strh    w11, [x22, x26, lsl #1]
        mov     x26, x12
Lc800:
        cmp     x26, #0xff
        b.hi    Lc828
        ldrb    w9, [x9, #2]
        lsr     w10, w10, #4
        orr     w9, w10, w9, lsl #4
        cmp     w9, #0xd00
        b.hi    Lc828
        add     x10, x26, #0x1
        strh    w9, [x22, x26, lsl #1]
        mov     x26, x10
Lc828:
        cmp     x26, #0xff
        b.hi    Lc854
        add     x9, x8, #0x3
        add     x8, x8, #0x3
        cmp     x9, #0xa6
        b.cc    Lc7dc
        b       Lc854
Lc844:
        ldr     x15, [sp, #24]
        mov     w14, w19
        mov     x19, x20
        mov     x20, x21
Lc854:
        ldr     w8, [sp, #60]
        tbz     w8, #0, Lc8c4
        mov     x8, xzr
Lc860:
        add     x9, x24, x8
        ldrb    w11, [x9, #512]
        ldrb    w10, [x9, #513]
        bfi     w11, w10, #8, #4
        cmp     w11, #0xd00
        b.hi    Lc884
        add     x12, x27, #0x1
        strh    w11, [x15, x27, lsl #1]
        mov     x27, x12
Lc884:
        cmp     x27, #0xff
        b.hi    Lc8ac
        ldrb    w9, [x9, #514]
        lsr     w10, w10, #4
        orr     w9, w10, w9, lsl #4
        cmp     w9, #0xd00
        b.hi    Lc8ac
        add     x10, x27, #0x1
        strh    w9, [x15, x27, lsl #1]
        mov     x27, x10
Lc8ac:
        cmp     x27, #0xff
        b.hi    Lc8c4
        add     x9, x8, #0x3
        add     x8, x8, #0x3
        cmp     x9, #0xa6
        b.cc    Lc860
Lc8c4:
        tbz     w14, #0, Lc930
        mov     x8, xzr
Lc8cc:
        add     x9, x24, x8
        ldrb    w11, [x9, #1024]
        ldrb    w10, [x9, #1025]
        bfi     w11, w10, #8, #4
        cmp     w11, #0xd00
        b.hi    Lc8f0
        add     x12, x28, #0x1
        strh    w11, [x20, x28, lsl #1]
        mov     x28, x12
Lc8f0:
        cmp     x28, #0xff
        b.hi    Lc918
        ldrb    w9, [x9, #1026]
        lsr     w10, w10, #4
        orr     w9, w10, w9, lsl #4
        cmp     w9, #0xd00
        b.hi    Lc918
        add     x10, x28, #0x1
        strh    w9, [x20, x28, lsl #1]
        mov     x28, x10
Lc918:
        cmp     x28, #0xff
        b.hi    Lc930
        add     x9, x8, #0x3
        add     x8, x8, #0x3
        cmp     x9, #0xa6
        b.cc    Lc8cc
Lc930:
        tbz     w25, #0, Lc99c
        mov     x8, xzr
Lc938:
        add     x9, x24, x8
        ldrb    w11, [x9, #1536]
        ldrb    w10, [x9, #1537]
        bfi     w11, w10, #8, #4
        cmp     w11, #0xd00
        b.hi    Lc95c
        add     x12, x23, #0x1
        strh    w11, [x19, x23, lsl #1]
        mov     x23, x12
Lc95c:
        cmp     x23, #0xff
        b.hi    Lc984
        ldrb    w9, [x9, #1538]
        lsr     w10, w10, #4
        orr     w9, w10, w9, lsl #4
        cmp     w9, #0xd00
        b.hi    Lc984
        add     x10, x23, #0x1
        strh    w9, [x19, x23, lsl #1]
        mov     x23, x10
Lc984:
        cmp     x23, #0xff
        b.hi    Lc99c
        add     x9, x8, #0x3
        add     x8, x8, #0x3
        cmp     x9, #0xa6
        b.cc    Lc938
Lc99c:
        cmp     x27, #0x100
        cset    w15, cc
        cmp     x28, #0x100
        cset    w14, cc
        cmp     x23, #0x100
        cset    w25, cc
        cmp     x26, #0x100
        cset    w16, cc
        b.cc    Lc798
        cmp     x27, #0x100
        b.cc    Lc798
        cmp     x28, #0x100
        b.cc    Lc798
        cmp     x23, #0x100
        b.cc    Lc798
Lc9d8:
        add     x0, sp, #0x40
        bl      L5754
        add     x0, sp, #0x360
        mov     w1, wzr
        mov     w2, #0x800
        add     x19, sp, #0x360
        bl      L0840
        .inst   0xf0000108  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #2936]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    Lca2c
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
Lca2c:
        bl      L0830

// mlkem_poly_rej_uniform (0x1e0 bytes)
Lca30:
        stp     x29, x30, [sp, #-48]!
        stp     x28, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0x2f0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xf0000108  // adrp x8, 0x2f000
        mov     x19, x0
        add     x0, sp, #0x200
        mov     x20, x1
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #744]
        bl      L52c8
        add     x0, sp, #0x200
        mov     x1, x20
        mov     w2, #0x22
        bl      L513c
        mov     x0, sp
        add     x2, sp, #0x200
        mov     w1, #0x3
        mov     x21, sp
        bl      L527c
        mov     x8, xzr
        mov     x20, xzr
Lca94:
        add     x9, x21, x8
        ldrb    w11, [x9]
        ldrb    w10, [x9, #1]
        bfi     w11, w10, #8, #4
        cmp     w11, #0xd00
        b.hi    Lcab8
        add     x12, x20, #0x1
        strh    w11, [x19, x20, lsl #1]
        mov     x20, x12
Lcab8:
        cmp     x20, #0xff
        b.hi    Lcae0
        ldrb    w9, [x9, #2]
        lsr     w10, w10, #4
        orr     w9, w10, w9, lsl #4
        cmp     w9, #0xd00
        b.hi    Lcae0
        add     x10, x20, #0x1
        strh    w9, [x19, x20, lsl #1]
        mov     x20, x10
Lcae0:
        cmp     x20, #0xff
        b.hi    Lcaf8
        add     x9, x8, #0x3
        add     x8, x8, #0x3
        cmp     x9, #0x1f6
        b.cc    Lca94
Lcaf8:
        cmp     x20, #0xff
        b.hi    Lcb8c
        mov     x21, sp
        b       Lcb10
Lcb08:
        cmp     x20, #0x100
        b.cs    Lcb8c
Lcb10:
        mov     x0, sp
        add     x2, sp, #0x200
        mov     w1, #0x1
        bl      L527c
        mov     x8, xzr
Lcb24:
        add     x10, x21, x8
        ldrb    w11, [x10]
        ldrb    w9, [x10, #1]
        ldrb    w10, [x10, #2]
        bfi     w11, w9, #8, #4
        cmp     w11, #0xd00
        b.hi    Lcb4c
        add     x12, x20, #0x1
        strh    w11, [x19, x20, lsl #1]
        mov     x20, x12
Lcb4c:
        cmp     x20, #0xff
        b.hi    Lcb70
        lsr     w9, w9, #4
        orr     w9, w9, w10, lsl #4
        cmp     w9, #0xd00
        b.hi    Lcb70
        add     x10, x20, #0x1
        strh    w9, [x19, x20, lsl #1]
        mov     x20, x10
Lcb70:
        cmp     x20, #0xff
        b.hi    Lcb08
        add     x9, x8, #0x3
        add     x8, x8, #0x3
        cmp     x9, #0xa6
        b.cc    Lcb24
        b       Lcb08
Lcb8c:
        add     x0, sp, #0x200
        bl      L52cc
        movi    v0.2d, #0x0
        str     xzr, [sp, #496]
        mov     x8, sp
        stp     q0, q0, [sp, #16]
        stp     q0, q0, [sp, #48]
        stp     q0, q0, [sp, #80]
        stp     q0, q0, [sp, #112]
        stp     q0, q0, [sp, #144]
        stp     q0, q0, [sp, #176]
        stp     q0, q0, [sp, #208]
        stp     q0, q0, [sp, #240]
        stp     q0, q0, [sp, #272]
        stp     q0, q0, [sp, #304]
        stp     q0, q0, [sp, #336]
        stp     q0, q0, [sp, #368]
        stp     q0, q0, [sp, #400]
        stp     q0, q0, [sp, #432]
        stp     q0, q0, [sp, #464]
        str     q0, [sp]
        .inst   0xf0000108  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #744]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    Lcc0c
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldp     x28, x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
Lcc0c:
        bl      L0830

// mlkem_poly_cbd2 (0x218 bytes)
Lcc10:
        add     x8, x1, #0x80
        cmp     x8, x0
        b.ls    Lccd8
        add     x8, x0, #0x200
        cmp     x8, x1
        b.ls    Lccd8
        .inst   0xf0000009  // adrp x9, 0xf000
        .inst   0xf000000a  // adrp x10, 0xf000
        .inst   0xf000000b  // adrp x11, 0xf000
        .inst   0xf000000c  // adrp x12, 0xf000
        movi    v2.4s, #0x3
        mov     x8, xzr
        ldr     d0, [x9, #1888]
        mov     w9, #0x55555555
        ldr     q1, [x10, #1600]
        add     x10, x0, #0x8
        ldr     d3, [x11, #1896]
        ldr     q4, [x12, #1616]
Lcc58:
        ldr     w11, [x1, x8]
        add     x8, x8, #0x4
        cmp     x8, #0x80
        and     w12, w11, w9
        and     w11, w9, w11, lsr #1
        add     w11, w11, w12
        lsr     w12, w11, #26
        dup     v5.4s, w11
        fmov    s16, w11
        ushl    v6.2s, v5.2s, v3.2s
        ushl    v17.2s, v5.2s, v0.2s
        mov     v6.s[2], w12
        lsr     w12, w11, #4
        mov     v16.s[1], w12
        and     v7.16b, v6.16b, v2.16b
        mov     v6.s[3], w11
        mov     v16.d[1], v17.d[0]
        ushr    v6.4s, v6.4s, #30
        mov     v7.s[3], v6.s[3]
        ushl    v6.4s, v5.4s, v1.4s
        ushl    v5.4s, v5.4s, v4.4s
        and     v6.16b, v6.16b, v2.16b
        and     v16.16b, v16.16b, v2.16b
        and     v5.16b, v5.16b, v2.16b
        sub     v6.4s, v16.4s, v6.4s
        sub     v5.4s, v5.4s, v7.4s
        xtn     v6.4h, v6.4s
        xtn     v5.4h, v5.4s
        stur    d6, [x10, #-8]
        str     d5, [x10], #16
        b.ne    Lcc58
        b       Lce24
Lccd8:
        .inst   0xf0000009  // adrp x9, 0xf000
        .inst   0xf000000a  // adrp x10, 0xf000
        .inst   0xf000000b  // adrp x11, 0xf000
        mov     x8, xzr
        movi    v7.16b, #0x55
        ldr     q0, [x9, #1536]
        .inst   0xf0000009  // adrp x9, 0xf000
        ldr     q1, [x10, #832]
        .inst   0xf000000a  // adrp x10, 0xf000
        ldr     q2, [x11, #1552]
        .inst   0xf000000b  // adrp x11, 0xf000
        ldr     q3, [x9, #864]
        .inst   0xf0000009  // adrp x9, 0xf000
        movi    v16.4s, #0x3
        ldr     q4, [x10, #1568]
        ldr     q5, [x11, #896]
        ldr     q6, [x9, #1584]
        .inst   0xf0000009  // adrp x9, 0xf000
        ldr     q17, [x9, #928]
Lcd24:
        ldr     q18, [x1, x8]
        add     x8, x8, #0x10
        cmp     x8, #0x80
        ushr    v19.4s, v18.4s, #1
        and     v18.16b, v18.16b, v7.16b
        and     v19.16b, v19.16b, v7.16b
        add     v18.4s, v19.4s, v18.4s
        ushr    v20.4s, v18.4s, #2
        ushr    v21.4s, v18.4s, #4
        ushr    v22.4s, v18.4s, #6
        ushr    v23.4s, v18.4s, #8
        ushr    v24.4s, v18.4s, #10
        ushr    v25.4s, v18.4s, #26
        and     v19.16b, v18.16b, v16.16b
        ushr    v26.4s, v18.4s, #30
        and     v20.16b, v20.16b, v16.16b
        and     v21.16b, v21.16b, v16.16b
        and     v22.16b, v22.16b, v16.16b
        and     v23.16b, v23.16b, v16.16b
        sub     v19.4s, v19.4s, v20.4s
        sub     v20.4s, v21.4s, v22.4s
        and     v21.16b, v24.16b, v16.16b
        sub     v21.4s, v23.4s, v21.4s
        ushr    v22.4s, v18.4s, #16
        ushr    v23.4s, v18.4s, #18
        ushr    v24.4s, v18.4s, #22
        and     v22.16b, v22.16b, v16.16b
        ushr    v27.4s, v18.4s, #12
        and     v23.16b, v23.16b, v16.16b
        sub     v22.4s, v22.4s, v23.4s
        ushr    v23.4s, v18.4s, #20
        and     v24.16b, v24.16b, v16.16b
        and     v23.16b, v23.16b, v16.16b
        sub     v23.4s, v23.4s, v24.4s
        ushr    v24.4s, v18.4s, #24
        bic     v25.4s, #0x3c
        bic     v24.4s, #0xfc
        sub     v24.4s, v24.4s, v25.4s
        ushr    v25.4s, v18.4s, #28
        ushr    v18.4s, v18.4s, #14
        bic     v25.4s, #0xc
        sub     v25.4s, v25.4s, v26.4s
        and     v26.16b, v27.16b, v16.16b
        and     v18.16b, v18.16b, v16.16b
        sub     v18.4s, v26.4s, v18.4s
        uzp1    v22.8h, v22.8h, v23.8h
        uzp1    v19.8h, v19.8h, v20.8h
        uzp1    v23.8h, v24.8h, v25.8h
        uzp1    v20.8h, v21.8h, v18.8h
        tbl     v18.16b, {v22.16b-v23.16b}, v0.16b
        tbl     v21.16b, {v22.16b-v23.16b}, v2.16b
        tbl     v24.16b, {v22.16b-v23.16b}, v4.16b
        tbl     v22.16b, {v22.16b-v23.16b}, v6.16b
        tbl     v23.16b, {v19.16b-v20.16b}, v17.16b
        tbl     v25.16b, {v19.16b-v20.16b}, v5.16b
        tbl     v26.16b, {v19.16b-v20.16b}, v3.16b
        tbl     v19.16b, {v19.16b-v20.16b}, v1.16b
        mov     v23.d[1], v22.d[1]
        mov     v25.d[1], v24.d[1]
        mov     v26.d[1], v21.d[1]
        mov     v19.d[1], v18.d[1]
        stp     q25, q23, [x0, #32]
        stp     q19, q26, [x0], #64
        b.ne    Lcd24
Lce24:
        ret

// mlkem_poly_cbd3 (0x984 bytes)
Lce28:
        add     x8, x1, #0xc0
        cmp     x8, x0
        b.ls    Lcee0
        add     x8, x0, #0x200
        cmp     x8, x1
        b.ls    Lcee0
        .inst   0xf000000a  // adrp x10, 0xf000
        .inst   0xf000000b  // adrp x11, 0xf000
        mov     w9, #0x9249
        movi    v0.2s, #0x7
        mov     x8, xzr
        movk    w9, #0x24, lsl #16
        ldr     d1, [x10, #1904]
        add     x10, x1, #0x1
        ldr     d2, [x11, #1912]
Lce64:
        ldurh   w11, [x10, #-1]
        add     x14, x0, x8
        ldrb    w12, [x10, #1]
        add     x8, x8, #0x8
        add     x10, x10, #0x3
        cmp     x8, #0x200
        orr     w11, w11, w12, lsl #16
        and     w12, w11, w9
        and     w13, w9, w11, lsr #1
        and     w11, w9, w11, lsr #2
        add     w12, w13, w12
        add     w11, w12, w11
        and     w12, w11, #0x7
        ubfx    w13, w11, #3, #3
        sub     w12, w12, w13
        dup     v3.2s, w11
        strh    w12, [x14]
        ubfx    w12, w11, #18, #3
        sub     w11, w12, w11, lsr #21
        ushl    v4.2s, v3.2s, v1.2s
        ushl    v3.2s, v3.2s, v2.2s
        and     v4.8b, v4.8b, v0.8b
        and     v3.8b, v3.8b, v0.8b
        sub     v3.2s, v4.2s, v3.2s
        strh    w11, [x14, #6]
        mov     w15, v3.s[1]
        fmov    w13, s3
        strh    w13, [x14, #2]
        strh    w15, [x14, #4]
        b.ne    Lce64
        ret
Lcee0:
        mov     x8, x1
        mov     w9, #0x9249
        movk    w9, #0x24, lsl #16
        ld3     {v0.16b-v2.16b}, [x8], #48
        uxtl2   v3.8h, v0.16b
        uxtl2   v7.8h, v1.16b
        uxtl    v5.4s, v3.4h
        uxtl2   v3.4s, v3.8h
        ushll   v17.4s, v7.4h, #8
        ushll2  v7.4s, v7.8h, #8
        uxtl    v4.8h, v0.8b
        uxtl    v16.8h, v1.8b
        orr     v3.16b, v7.16b, v3.16b
        uxtl    v7.8h, v2.8b
        uxtl2   v0.8h, v2.16b
        uxtl    v6.4s, v4.4h
        uxtl2   v4.4s, v4.8h
        ushll2  v18.4s, v16.8h, #8
        ushll   v16.4s, v16.4h, #8
        shll2   v2.4s, v7.8h, #16
        shll    v1.4s, v7.4h, #16
        shll    v7.4s, v0.4h, #16
        shll2   v0.4s, v0.8h, #16
        orr     v4.16b, v18.16b, v4.16b
        orr     v6.16b, v16.16b, v6.16b
        orr     v5.16b, v17.16b, v5.16b
        orr     v5.16b, v5.16b, v7.16b
        orr     v0.16b, v3.16b, v0.16b
        orr     v3.16b, v6.16b, v1.16b
        orr     v2.16b, v4.16b, v2.16b
        dup     v1.4s, w9
        mov     x9, x0
        ushr    v17.4s, v5.4s, #1
        ushr    v18.4s, v2.4s, #1
        ushr    v19.4s, v0.4s, #1
        ushr    v20.4s, v3.4s, #1
        and     v4.16b, v2.16b, v1.16b
        ushr    v2.4s, v2.4s, #2
        and     v6.16b, v3.16b, v1.16b
        and     v7.16b, v0.16b, v1.16b
        and     v16.16b, v5.16b, v1.16b
        and     v18.16b, v18.16b, v1.16b
        and     v20.16b, v20.16b, v1.16b
        and     v19.16b, v19.16b, v1.16b
        and     v17.16b, v17.16b, v1.16b
        ushr    v5.4s, v5.4s, #2
        ushr    v3.4s, v3.4s, #2
        ushr    v0.4s, v0.4s, #2
        add     v16.4s, v17.4s, v16.4s
        add     v7.4s, v19.4s, v7.4s
        add     v6.4s, v20.4s, v6.4s
        add     v4.4s, v18.4s, v4.4s
        and     v5.16b, v5.16b, v1.16b
        and     v17.16b, v0.16b, v1.16b
        and     v3.16b, v3.16b, v1.16b
        and     v0.16b, v2.16b, v1.16b
        add     v2.4s, v4.4s, v0.4s
        movi    v0.4s, #0x7
        add     v4.4s, v6.4s, v3.4s
        add     v3.4s, v16.4s, v5.4s
        add     v5.4s, v7.4s, v17.4s
        ushr    v19.4s, v3.4s, #3
        ushr    v21.4s, v5.4s, #3
        ushr    v18.4s, v2.4s, #3
        and     v6.16b, v3.16b, v0.16b
        ushr    v20.4s, v4.4s, #3
        and     v7.16b, v5.16b, v0.16b
        and     v19.16b, v19.16b, v0.16b
        and     v21.16b, v21.16b, v0.16b
        sub     v7.4s, v7.4s, v21.4s
        sub     v6.4s, v6.4s, v19.4s
        ushr    v21.4s, v3.4s, #6
        and     v16.16b, v4.16b, v0.16b
        ushr    v23.4s, v5.4s, #9
        and     v17.16b, v2.16b, v0.16b
        and     v20.16b, v20.16b, v0.16b
        and     v18.16b, v18.16b, v0.16b
        sub     v22.4s, v17.4s, v18.4s
        sub     v20.4s, v16.4s, v20.4s
        uzp1    v16.8h, v6.8h, v7.8h
        ushr    v6.4s, v5.4s, #6
        and     v7.16b, v21.16b, v0.16b
        ushr    v21.4s, v3.4s, #9
        and     v6.16b, v6.16b, v0.16b
        and     v21.16b, v21.16b, v0.16b
        and     v23.16b, v23.16b, v0.16b
        sub     v6.4s, v6.4s, v23.4s
        ushr    v23.4s, v3.4s, #12
        sub     v7.4s, v7.4s, v21.4s
        ushr    v21.4s, v5.4s, #12
        ushr    v24.4s, v3.4s, #15
        ushr    v25.4s, v5.4s, #15
        ushr    v26.4s, v2.4s, #9
        and     v23.16b, v23.16b, v0.16b
        and     v21.16b, v21.16b, v0.16b
        and     v24.16b, v24.16b, v0.16b
        and     v25.16b, v25.16b, v0.16b
        sub     v21.4s, v21.4s, v25.4s
        sub     v23.4s, v23.4s, v24.4s
        uzp1    v17.8h, v7.8h, v6.8h
        ushr    v7.4s, v4.4s, #6
        ushr    v24.4s, v2.4s, #6
        ushr    v25.4s, v4.4s, #9
        and     v7.16b, v7.16b, v0.16b
        ushr    v6.4s, v3.4s, #18
        and     v24.16b, v24.16b, v0.16b
        and     v25.16b, v25.16b, v0.16b
        and     v26.16b, v26.16b, v0.16b
        sub     v24.4s, v24.4s, v26.4s
        sub     v7.4s, v7.4s, v25.4s
        uzp1    v18.8h, v23.8h, v21.8h
        uzp1    v20.8h, v20.8h, v22.8h
        uzp1    v21.8h, v7.8h, v24.8h
        ushr    v7.4s, v2.4s, #12
        ushr    v24.4s, v2.4s, #15
        ushr    v26.4s, v4.4s, #15
        and     v7.16b, v7.16b, v0.16b
        ushr    v25.4s, v5.4s, #18
        and     v24.16b, v24.16b, v0.16b
        sub     v7.4s, v7.4s, v24.4s
        ushr    v24.4s, v4.4s, #12
        and     v26.16b, v26.16b, v0.16b
        ushr    v5.4s, v5.4s, #21
        and     v24.16b, v24.16b, v0.16b
        sub     v24.4s, v24.4s, v26.4s
        ushr    v26.4s, v2.4s, #18
        ushr    v2.4s, v2.4s, #21
        bic     v26.4s, #0x38
        sub     v2.4s, v26.4s, v2.4s
        ushr    v26.4s, v4.4s, #18
        ushr    v4.4s, v4.4s, #21
        bic     v26.4s, #0x38
        sub     v4.4s, v26.4s, v4.4s
        uzp1    v22.8h, v24.8h, v7.8h
        uzp1    v23.8h, v4.8h, v2.8h
        ushr    v2.4s, v3.4s, #21
        bic     v6.4s, #0x38
        bic     v25.4s, #0x38
        sub     v3.4s, v25.4s, v5.4s
        sub     v2.4s, v6.4s, v2.4s
        st4     {v20.8h-v23.8h}, [x9], #64
        uzp1    v19.8h, v2.8h, v3.8h
        st4     {v16.8h-v19.8h}, [x9]
        add     x9, x1, #0x60
        ld3     {v2.16b-v4.16b}, [x8]
        add     x8, x0, #0x80
        uxtl2   v5.8h, v2.16b
        uxtl2   v17.8h, v3.16b
        uxtl    v6.4s, v5.4h
        uxtl2   v5.4s, v5.8h
        ushll   v19.4s, v17.4h, #8
        ushll2  v17.4s, v17.8h, #8
        uxtl    v7.8h, v2.8b
        uxtl    v18.8h, v3.8b
        orr     v5.16b, v17.16b, v5.16b
        uxtl    v17.8h, v4.8b
        uxtl2   v2.8h, v4.16b
        uxtl    v16.4s, v7.4h
        uxtl2   v7.4s, v7.8h
        ushll2  v20.4s, v18.8h, #8
        shll2   v3.4s, v17.8h, #16
        shll    v4.4s, v17.4h, #16
        shll    v17.4s, v2.4h, #16
        shll2   v2.4s, v2.8h, #16
        ushll   v18.4s, v18.4h, #8
        orr     v7.16b, v20.16b, v7.16b
        orr     v6.16b, v19.16b, v6.16b
        orr     v6.16b, v6.16b, v17.16b
        orr     v2.16b, v5.16b, v2.16b
        orr     v3.16b, v7.16b, v3.16b
        orr     v16.16b, v18.16b, v16.16b
        ushr    v18.4s, v6.4s, #1
        ushr    v19.4s, v3.4s, #1
        ushr    v20.4s, v2.4s, #1
        orr     v4.16b, v16.16b, v4.16b
        and     v5.16b, v3.16b, v1.16b
        and     v16.16b, v2.16b, v1.16b
        and     v17.16b, v6.16b, v1.16b
        ushr    v21.4s, v4.4s, #1
        and     v19.16b, v19.16b, v1.16b
        ushr    v3.4s, v3.4s, #2
        and     v20.16b, v20.16b, v1.16b
        and     v18.16b, v18.16b, v1.16b
        ushr    v6.4s, v6.4s, #2
        ushr    v2.4s, v2.4s, #2
        and     v7.16b, v4.16b, v1.16b
        ushr    v4.4s, v4.4s, #2
        add     v17.4s, v18.4s, v17.4s
        add     v16.4s, v20.4s, v16.4s
        add     v5.4s, v19.4s, v5.4s
        and     v21.16b, v21.16b, v1.16b
        and     v6.16b, v6.16b, v1.16b
        and     v18.16b, v2.16b, v1.16b
        and     v3.16b, v3.16b, v1.16b
        add     v7.4s, v21.4s, v7.4s
        and     v2.16b, v4.16b, v1.16b
        add     v5.4s, v5.4s, v3.4s
        add     v4.4s, v17.4s, v6.4s
        add     v3.4s, v16.4s, v18.4s
        add     v2.4s, v7.4s, v2.4s
        ushr    v19.4s, v4.4s, #3
        ushr    v21.4s, v3.4s, #3
        ushr    v18.4s, v5.4s, #3
        and     v6.16b, v4.16b, v0.16b
        ushr    v20.4s, v2.4s, #3
        and     v7.16b, v3.16b, v0.16b
        and     v19.16b, v19.16b, v0.16b
        and     v21.16b, v21.16b, v0.16b
        sub     v7.4s, v7.4s, v21.4s
        sub     v6.4s, v6.4s, v19.4s
        ushr    v21.4s, v4.4s, #6
        and     v16.16b, v2.16b, v0.16b
        ushr    v23.4s, v3.4s, #9
        and     v17.16b, v5.16b, v0.16b
        and     v20.16b, v20.16b, v0.16b
        and     v18.16b, v18.16b, v0.16b
        sub     v22.4s, v17.4s, v18.4s
        sub     v20.4s, v16.4s, v20.4s
        uzp1    v16.8h, v6.8h, v7.8h
        ushr    v6.4s, v3.4s, #6
        and     v7.16b, v21.16b, v0.16b
        ushr    v21.4s, v4.4s, #9
        and     v6.16b, v6.16b, v0.16b
        and     v21.16b, v21.16b, v0.16b
        and     v23.16b, v23.16b, v0.16b
        sub     v6.4s, v6.4s, v23.4s
        sub     v7.4s, v7.4s, v21.4s
        ushr    v21.4s, v4.4s, #15
        uzp1    v17.8h, v7.8h, v6.8h
        ushr    v6.4s, v4.4s, #12
        ushr    v7.4s, v3.4s, #12
        ushr    v23.4s, v3.4s, #15
        ushr    v24.4s, v2.4s, #9
        and     v6.16b, v6.16b, v0.16b
        ushr    v25.4s, v5.4s, #9
        and     v7.16b, v7.16b, v0.16b
        and     v21.16b, v21.16b, v0.16b
        and     v23.16b, v23.16b, v0.16b
        sub     v7.4s, v7.4s, v23.4s
        sub     v6.4s, v6.4s, v21.4s
        ushr    v21.4s, v2.4s, #6
        ushr    v23.4s, v5.4s, #6
        and     v21.16b, v21.16b, v0.16b
        and     v23.16b, v23.16b, v0.16b
        and     v24.16b, v24.16b, v0.16b
        and     v25.16b, v25.16b, v0.16b
        sub     v23.4s, v23.4s, v25.4s
        sub     v21.4s, v21.4s, v24.4s
        uzp1    v24.8h, v20.8h, v22.8h
        ushr    v20.4s, v5.4s, #12
        ushr    v22.4s, v5.4s, #15
        and     v20.16b, v20.16b, v0.16b
        and     v22.16b, v22.16b, v0.16b
        uzp1    v25.8h, v21.8h, v23.8h
        ushr    v21.4s, v2.4s, #12
        sub     v20.4s, v20.4s, v22.4s
        ushr    v22.4s, v2.4s, #15
        and     v21.16b, v21.16b, v0.16b
        and     v22.16b, v22.16b, v0.16b
        sub     v21.4s, v21.4s, v22.4s
        ushr    v22.4s, v4.4s, #18
        uzp1    v26.8h, v21.8h, v20.8h
        ushr    v21.4s, v5.4s, #18
        ushr    v5.4s, v5.4s, #21
        bic     v21.4s, #0x38
        ushr    v20.4s, v3.4s, #18
        sub     v5.4s, v21.4s, v5.4s
        ushr    v21.4s, v2.4s, #18
        ushr    v2.4s, v2.4s, #21
        ushr    v4.4s, v4.4s, #21
        bic     v21.4s, #0x38
        ushr    v3.4s, v3.4s, #21
        sub     v2.4s, v21.4s, v2.4s
        bic     v22.4s, #0x38
        bic     v20.4s, #0x38
        uzp1    v27.8h, v2.8h, v5.8h
        sub     v2.4s, v20.4s, v3.4s
        sub     v3.4s, v22.4s, v4.4s
        uzp1    v18.8h, v6.8h, v7.8h
        uzp1    v19.8h, v3.8h, v2.8h
        st4     {v24.8h-v27.8h}, [x8]
        add     x8, x0, #0xc0
        st4     {v16.8h-v19.8h}, [x8]
        add     x8, x0, #0x100
        ld3     {v2.16b-v4.16b}, [x9]
        add     x9, x1, #0x90
        uxtl2   v5.8h, v2.16b
        uxtl2   v17.8h, v3.16b
        uxtl    v6.4s, v5.4h
        uxtl2   v5.4s, v5.8h
        ushll   v19.4s, v17.4h, #8
        ushll2  v17.4s, v17.8h, #8
        uxtl    v7.8h, v2.8b
        uxtl    v18.8h, v3.8b
        orr     v5.16b, v17.16b, v5.16b
        uxtl    v17.8h, v4.8b
        uxtl2   v2.8h, v4.16b
        uxtl    v16.4s, v7.4h
        uxtl2   v7.4s, v7.8h
        ushll2  v20.4s, v18.8h, #8
        ushll   v18.4s, v18.4h, #8
        shll2   v3.4s, v17.8h, #16
        shll    v4.4s, v17.4h, #16
        shll    v17.4s, v2.4h, #16
        shll2   v2.4s, v2.8h, #16
        orr     v7.16b, v20.16b, v7.16b
        orr     v16.16b, v18.16b, v16.16b
        orr     v6.16b, v19.16b, v6.16b
        orr     v6.16b, v6.16b, v17.16b
        orr     v2.16b, v5.16b, v2.16b
        orr     v4.16b, v16.16b, v4.16b
        orr     v3.16b, v7.16b, v3.16b
        ushr    v18.4s, v6.4s, #1
        ushr    v19.4s, v3.4s, #1
        ushr    v20.4s, v2.4s, #1
        ushr    v21.4s, v4.4s, #1
        and     v5.16b, v3.16b, v1.16b
        ushr    v3.4s, v3.4s, #2
        and     v7.16b, v4.16b, v1.16b
        and     v16.16b, v2.16b, v1.16b
        and     v17.16b, v6.16b, v1.16b
        and     v19.16b, v19.16b, v1.16b
        and     v21.16b, v21.16b, v1.16b
        and     v20.16b, v20.16b, v1.16b
        and     v18.16b, v18.16b, v1.16b
        ushr    v6.4s, v6.4s, #2
        ushr    v4.4s, v4.4s, #2
        ushr    v2.4s, v2.4s, #2
        add     v17.4s, v18.4s, v17.4s
        add     v16.4s, v20.4s, v16.4s
        add     v7.4s, v21.4s, v7.4s
        add     v5.4s, v19.4s, v5.4s
        and     v6.16b, v6.16b, v1.16b
        and     v18.16b, v2.16b, v1.16b
        and     v2.16b, v4.16b, v1.16b
        and     v3.16b, v3.16b, v1.16b
        add     v5.4s, v5.4s, v3.4s
        add     v4.4s, v7.4s, v2.4s
        add     v2.4s, v17.4s, v6.4s
        add     v3.4s, v16.4s, v18.4s
        ushr    v19.4s, v2.4s, #3
        ushr    v21.4s, v3.4s, #3
        ushr    v18.4s, v5.4s, #3
        and     v6.16b, v2.16b, v0.16b
        ushr    v20.4s, v4.4s, #3
        and     v7.16b, v3.16b, v0.16b
        and     v19.16b, v19.16b, v0.16b
        and     v21.16b, v21.16b, v0.16b
        sub     v7.4s, v7.4s, v21.4s
        sub     v6.4s, v6.4s, v19.4s
        and     v16.16b, v4.16b, v0.16b
        and     v17.16b, v5.16b, v0.16b
        and     v20.16b, v20.16b, v0.16b
        and     v18.16b, v18.16b, v0.16b
        sub     v22.4s, v17.4s, v18.4s
        sub     v20.4s, v16.4s, v20.4s
        uzp1    v16.8h, v6.8h, v7.8h
        ushr    v6.4s, v2.4s, #6
        ushr    v7.4s, v3.4s, #6
        ushr    v21.4s, v2.4s, #9
        ushr    v23.4s, v3.4s, #9
        ushr    v24.4s, v5.4s, #6
        ushr    v26.4s, v5.4s, #9
        ushr    v25.4s, v4.4s, #6
        and     v6.16b, v6.16b, v0.16b
        and     v7.16b, v7.16b, v0.16b
        and     v21.16b, v21.16b, v0.16b
        and     v23.16b, v23.16b, v0.16b
        sub     v7.4s, v7.4s, v23.4s
        sub     v6.4s, v6.4s, v21.4s
        ushr    v21.4s, v2.4s, #12
        and     v24.16b, v24.16b, v0.16b
        ushr    v23.4s, v3.4s, #15
        and     v26.16b, v26.16b, v0.16b
        sub     v24.4s, v24.4s, v26.4s
        ushr    v26.4s, v4.4s, #9
        uzp1    v17.8h, v6.8h, v7.8h
        ushr    v6.4s, v3.4s, #12
        and     v7.16b, v21.16b, v0.16b
        ushr    v21.4s, v2.4s, #15
        and     v25.16b, v25.16b, v0.16b
        and     v26.16b, v26.16b, v0.16b
        and     v6.16b, v6.16b, v0.16b
        and     v21.16b, v21.16b, v0.16b
        and     v23.16b, v23.16b, v0.16b
        sub     v25.4s, v25.4s, v26.4s
        sub     v6.4s, v6.4s, v23.4s
        sub     v7.4s, v7.4s, v21.4s
        uzp1    v20.8h, v20.8h, v22.8h
        ushr    v26.4s, v5.4s, #12
        uzp1    v21.8h, v25.8h, v24.8h
        ushr    v24.4s, v5.4s, #15
        and     v25.16b, v26.16b, v0.16b
        and     v24.16b, v24.16b, v0.16b
        ushr    v26.4s, v4.4s, #12
        sub     v24.4s, v25.4s, v24.4s
        ushr    v25.4s, v4.4s, #15
        and     v26.16b, v26.16b, v0.16b
        and     v25.16b, v25.16b, v0.16b
        sub     v25.4s, v26.4s, v25.4s
        uzp1    v18.8h, v7.8h, v6.8h
        uzp1    v22.8h, v25.8h, v24.8h
        ushr    v24.4s, v5.4s, #18
        ushr    v25.4s, v4.4s, #18
        ushr    v5.4s, v5.4s, #21
        ushr    v4.4s, v4.4s, #21
        bic     v24.4s, #0x38
        bic     v25.4s, #0x38
        sub     v5.4s, v24.4s, v5.4s
        sub     v4.4s, v25.4s, v4.4s
        ushr    v24.4s, v2.4s, #18
        uzp1    v23.8h, v4.8h, v5.8h
        ushr    v4.4s, v3.4s, #18
        ushr    v3.4s, v3.4s, #21
        ushr    v2.4s, v2.4s, #21
        bic     v24.4s, #0x38
        bic     v4.4s, #0x38
        st4     {v20.8h-v23.8h}, [x8]
        sub     v3.4s, v4.4s, v3.4s
        add     x8, x0, #0x140
        sub     v2.4s, v24.4s, v2.4s
        uzp1    v19.8h, v2.8h, v3.8h
        st4     {v16.8h-v19.8h}, [x8]
        add     x8, x0, #0x180
        ld3     {v2.16b-v4.16b}, [x9]
        uxtl2   v5.8h, v2.16b
        uxtl2   v17.8h, v3.16b
        uxtl    v6.4s, v5.4h
        uxtl2   v5.4s, v5.8h
        ushll   v19.4s, v17.4h, #8
        ushll2  v17.4s, v17.8h, #8
        uxtl    v7.8h, v2.8b
        uxtl    v18.8h, v3.8b
        orr     v5.16b, v17.16b, v5.16b
        uxtl    v17.8h, v4.8b
        uxtl2   v2.8h, v4.16b
        uxtl    v16.4s, v7.4h
        uxtl2   v7.4s, v7.8h
        ushll2  v20.4s, v18.8h, #8
        ushll   v18.4s, v18.4h, #8
        shll2   v3.4s, v17.8h, #16
        shll    v4.4s, v17.4h, #16
        shll    v17.4s, v2.4h, #16
        orr     v7.16b, v20.16b, v7.16b
        orr     v16.16b, v18.16b, v16.16b
        orr     v6.16b, v19.16b, v6.16b
        shll2   v2.4s, v2.8h, #16
        orr     v6.16b, v6.16b, v17.16b
        orr     v4.16b, v16.16b, v4.16b
        orr     v3.16b, v7.16b, v3.16b
        ushr    v18.4s, v6.4s, #1
        ushr    v19.4s, v3.4s, #1
        ushr    v21.4s, v4.4s, #1
        orr     v2.16b, v5.16b, v2.16b
        and     v5.16b, v3.16b, v1.16b
        and     v7.16b, v4.16b, v1.16b
        and     v16.16b, v2.16b, v1.16b
        and     v17.16b, v6.16b, v1.16b
        ushr    v20.4s, v2.4s, #1
        and     v19.16b, v19.16b, v1.16b
        ushr    v3.4s, v3.4s, #2
        and     v21.16b, v21.16b, v1.16b
        and     v18.16b, v18.16b, v1.16b
        ushr    v6.4s, v6.4s, #2
        ushr    v4.4s, v4.4s, #2
        ushr    v2.4s, v2.4s, #2
        add     v17.4s, v18.4s, v17.4s
        add     v7.4s, v21.4s, v7.4s
        add     v5.4s, v19.4s, v5.4s
        and     v20.16b, v20.16b, v1.16b
        and     v6.16b, v6.16b, v1.16b
        and     v18.16b, v2.16b, v1.16b
        and     v2.16b, v4.16b, v1.16b
        and     v1.16b, v3.16b, v1.16b
        add     v16.4s, v20.4s, v16.4s
        add     v4.4s, v5.4s, v1.4s
        add     v3.4s, v7.4s, v2.4s
        add     v2.4s, v17.4s, v6.4s
        add     v1.4s, v16.4s, v18.4s
        ushr    v17.4s, v4.4s, #3
        ushr    v18.4s, v2.4s, #3
        ushr    v19.4s, v3.4s, #3
        and     v5.16b, v2.16b, v0.16b
        ushr    v20.4s, v1.4s, #3
        and     v7.16b, v3.16b, v0.16b
        and     v16.16b, v4.16b, v0.16b
        and     v18.16b, v18.16b, v0.16b
        and     v19.16b, v19.16b, v0.16b
        and     v17.16b, v17.16b, v0.16b
        sub     v21.4s, v16.4s, v17.4s
        sub     v7.4s, v7.4s, v19.4s
        ushr    v16.4s, v2.4s, #6
        sub     v5.4s, v5.4s, v18.4s
        ushr    v17.4s, v1.4s, #6
        ushr    v18.4s, v2.4s, #9
        ushr    v19.4s, v1.4s, #9
        ushr    v24.4s, v4.4s, #9
        and     v6.16b, v1.16b, v0.16b
        and     v20.16b, v20.16b, v0.16b
        sub     v6.4s, v6.4s, v20.4s
        and     v16.16b, v16.16b, v0.16b
        and     v17.16b, v17.16b, v0.16b
        and     v18.16b, v18.16b, v0.16b
        and     v19.16b, v19.16b, v0.16b
        sub     v20.4s, v17.4s, v19.4s
        sub     v22.4s, v16.4s, v18.4s
        uzp1    v16.8h, v5.8h, v6.8h
        uzp1    v17.8h, v22.8h, v20.8h
        uzp1    v20.8h, v7.8h, v21.8h
        ushr    v5.4s, v3.4s, #6
        ushr    v6.4s, v4.4s, #6
        ushr    v7.4s, v3.4s, #9
        and     v5.16b, v5.16b, v0.16b
        and     v6.16b, v6.16b, v0.16b
        and     v7.16b, v7.16b, v0.16b
        and     v24.16b, v24.16b, v0.16b
        sub     v6.4s, v6.4s, v24.4s
        sub     v5.4s, v5.4s, v7.4s
        ushr    v7.4s, v3.4s, #12
        uzp1    v21.8h, v5.8h, v6.8h
        ushr    v5.4s, v4.4s, #12
        and     v6.16b, v7.16b, v0.16b
        ushr    v7.4s, v3.4s, #15
        ushr    v24.4s, v4.4s, #15
        and     v5.16b, v5.16b, v0.16b
        and     v7.16b, v7.16b, v0.16b
        and     v24.16b, v24.16b, v0.16b
        sub     v5.4s, v5.4s, v24.4s
        sub     v6.4s, v6.4s, v7.4s
        ushr    v7.4s, v1.4s, #12
        uzp1    v22.8h, v6.8h, v5.8h
        ushr    v5.4s, v4.4s, #18
        ushr    v4.4s, v4.4s, #21
        bic     v5.4s, #0x38
        ushr    v24.4s, v2.4s, #12
        sub     v4.4s, v5.4s, v4.4s
        ushr    v5.4s, v3.4s, #18
        ushr    v3.4s, v3.4s, #21
        bic     v5.4s, #0x38
        sub     v3.4s, v5.4s, v3.4s
        and     v6.16b, v7.16b, v0.16b
        ushr    v7.4s, v2.4s, #15
        ushr    v5.4s, v1.4s, #15
        uzp1    v23.8h, v3.8h, v4.8h
        ushr    v3.4s, v1.4s, #18
        ushr    v4.4s, v2.4s, #18
        and     v24.16b, v24.16b, v0.16b
        ushr    v2.4s, v2.4s, #21
        and     v7.16b, v7.16b, v0.16b
        and     v0.16b, v5.16b, v0.16b
        st4     {v20.8h-v23.8h}, [x8]
        ushr    v1.4s, v1.4s, #21
        add     x8, x0, #0x1c0
        sub     v0.4s, v6.4s, v0.4s
        sub     v5.4s, v24.4s, v7.4s
        bic     v4.4s, #0x38
        bic     v3.4s, #0x38
        sub     v1.4s, v3.4s, v1.4s
        sub     v2.4s, v4.4s, v2.4s
        uzp1    v18.8h, v5.8h, v0.8h
        uzp1    v19.8h, v2.8h, v1.8h
        st4     {v16.8h-v19.8h}, [x8]
        ret

// mlkem768_gen_matrix (0x15c bytes)
Ld7ac:
        stp     x29, x30, [sp, #-96]!
        stp     x28, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0x140
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd0000108  // adrp x8, 0x2f000
        cmp     w2, #0x0
        cset    w9, eq
        add     x2, x0, #0x400
        add     x3, x0, #0x600
        lsl     w24, w9, #1
        ldr     x8, [x8, #4088]
        add     x4, sp, #0x20
        mov     w10, #0x1
        add     x19, x0, #0x800
        add     x20, x0, #0xa00
        add     x21, x0, #0xc00
        ldr     x8, [x8]
        add     x22, x0, #0xe00
        add     x23, x0, #0x1, lsl #12
        cinc    w26, w10, eq
        cinc    w27, w10, ne
        add     x28, sp, #0x20
        str     x8, [sp, #312]
        cset    w8, ne
        ldp     q0, q1, [x1]
        add     x1, x0, #0x200
        lsl     w25, w8, #1
        strh    wzr, [sp, #64]
        strb    w9, [sp, #128]
        strb    w8, [sp, #129]
        strb    w24, [sp, #192]
        stp     q0, q1, [sp, #32]
        stp     q0, q1, [sp, #96]
        stp     q0, q1, [sp, #160]
        stp     q0, q1, [sp, #224]
        strb    w25, [sp, #193]
        strb    w8, [sp, #256]
        strb    w9, [sp, #257]
        bl      Lc4fc
        mov     w8, #0x101
        add     x4, sp, #0x20
        mov     x0, x19
        mov     x1, x20
        mov     x2, x21
        mov     x3, x22
        strb    w26, [sp, #128]
        strb    w27, [sp, #129]
        strb    w25, [sp, #192]
        strh    w8, [sp, #64]
        strb    w24, [sp, #193]
        strb    w27, [sp, #256]
        strb    w26, [sp, #257]
        bl      Lc4fc
        mov     w8, #0x202
        add     x1, sp, #0x20
        mov     x0, x23
        strh    w8, [sp, #64]
        bl      Lca30
        movi    v0.2d, #0x0
        .inst   0xd0000108  // adrp x8, 0x2f000
        stp     q0, q0, [sp, #32]
        stp     q0, q0, [sp, #64]
        stp     q0, q0, [sp, #96]
        stp     q0, q0, [sp, #128]
        stp     q0, q0, [sp, #160]
        stp     q0, q0, [sp, #192]
        stp     q0, q0, [sp, #224]
        stp     q0, q0, [sp, #256]
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #312]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    Ld904
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
Ld904:
        bl      L0830

// mlkem768_indcpa_keypair_derand (0x368 bytes)
Ld908:
        stp     x29, x30, [sp, #-96]!
        stp     x28, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0x2, lsl #12
        sub     x9, x9, #0x7c0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd0000108  // adrp x8, 0x2f000
        str     x1, [sp, #24]
        mov     x19, x0
        add     x10, sp, #0x2, lsl #12
        add     x0, sp, #0x2, lsl #12
        add     x1, sp, #0x2, lsl #12
        ldr     x8, [x8, #4088]
        add     x10, x10, #0x720
        add     x0, x0, #0x760
        add     x1, x1, #0x720
        add     x9, sp, #0x2, lsl #12
        ldr     x8, [x8]
        add     x9, x9, #0x760
        add     x23, x9, #0x20
        str     x8, [sp, #10168]
        mov     w8, #0x3
        ldp     q0, q1, [x2]
        mov     w2, #0x21
        strb    w8, [x10, #32]
        str     q0, [sp, #10016]
        str     q1, [sp, #10032]
        bl      L5468
        add     x28, sp, #0x1, lsl #12
        mov     w8, #0x1
        add     x28, x28, #0x520
        add     x0, sp, #0x1, lsl #12
        add     x21, x28, #0x600
        ldr     q0, [sp, #10080]
        ldr     q1, [sp, #10096]
        add     x1, x28, #0x200
        add     x2, x28, #0x400
        mov     w9, #0x2
        strh    w8, [sp, #3968]
        mov     w8, #0x100
        add     x0, x0, #0x520
        add     x4, sp, #0xf20
        mov     x3, x21
        str     q0, [sp, #3872]
        str     q1, [sp, #3888]
        add     x24, x28, #0x800
        str     q0, [sp, #3936]
        add     x25, x28, #0xa00
        str     q1, [sp, #3952]
        add     x22, x28, #0xc00
        str     q0, [sp, #4000]
        add     x26, x28, #0xe00
        str     q1, [sp, #4016]
        add     x27, x28, #0x1, lsl #12
        str     q1, [sp, #4080]
        add     x20, sp, #0xf20
        str     q0, [sp, #4064]
        strh    w9, [sp, #4032]
        strh    wzr, [sp, #3904]
        strh    w8, [sp, #4096]
        bl      Lc4fc
        mov     w8, #0x101
        mov     w9, #0x102
        mov     w10, #0x200
        mov     w11, #0x201
        add     x4, sp, #0xf20
        mov     x0, x24
        mov     x1, x25
        mov     x2, x22
        mov     x3, x26
        strh    w8, [sp, #3904]
        strh    w9, [sp, #3968]
        strh    w10, [sp, #4032]
        strh    w11, [sp, #4096]
        bl      Lc4fc
        mov     w8, #0x202
        add     x1, sp, #0xf20
        mov     x0, x27
        strh    w8, [sp, #3904]
        bl      Lca30
        movi    v0.2d, #0x0
        add     x24, sp, #0x320
        add     x1, x24, #0x200
        add     x2, x24, #0x400
        mov     w25, #0xff
        add     x0, sp, #0x320
        mov     x3, xzr
        mov     x4, x23
        str     q0, [sp, #4112]
        mov     w5, wzr
        str     q0, [sp, #4096]
        mov     w6, #0x1
        str     q0, [sp, #4080]
        mov     w7, #0x2
        str     q0, [sp, #4064]
        str     q0, [sp, #4048]
        str     q0, [sp, #4032]
        str     q0, [sp, #4016]
        str     q0, [sp, #4000]
        str     q0, [sp, #3984]
        str     q0, [sp, #3968]
        str     q0, [sp, #3952]
        str     q0, [sp, #3936]
        str     q0, [sp, #3920]
        str     q0, [sp, #3904]
        str     q0, [sp, #3888]
        str     q0, [sp, #3872]
        strb    w25, [sp]
        bl      Lefc8
        add     x1, x20, #0x200
        add     x2, x20, #0x400
        add     x0, sp, #0xf20
        mov     x3, xzr
        mov     x4, x23
        mov     w5, #0x3
        mov     w6, #0x4
        mov     w7, #0x5
        strb    w25, [sp]
        bl      Lefc8
        add     x0, sp, #0x320
        bl      Lecd4
        add     x0, sp, #0xf20
        bl      Lecd4
        add     x0, sp, #0x20
        add     x1, sp, #0x320
        add     x25, sp, #0x20
        bl      Lef20
        add     x1, sp, #0x1, lsl #12
        add     x0, sp, #0x920
        add     x1, x1, #0x520
        add     x2, sp, #0x320
        add     x3, sp, #0x20
        add     x23, sp, #0x920
        bl      Led14
        add     x0, x23, #0x200
        add     x2, sp, #0x320
        add     x3, sp, #0x20
        mov     x1, x21
        bl      Led14
        add     x0, x23, #0x400
        add     x2, sp, #0x320
        add     x3, sp, #0x20
        mov     x1, x22
        bl      Led14
        add     x0, sp, #0x920
        bl      Lefa8
        add     x0, sp, #0x920
        add     x1, sp, #0xf20
        bl      Lef74
        add     x0, sp, #0x920
        bl      Lef54
        add     x0, sp, #0x320
        bl      Lef54
        add     x1, sp, #0x320
        ldr     x0, [sp, #24]
        bl      Lec6c
        add     x1, sp, #0x920
        mov     x0, x19
        bl      Lec6c
        ldr     q0, [sp, #10080]
        add     x0, sp, #0x20
        ldr     q1, [sp, #10096]
        mov     w1, wzr
        mov     w2, #0x300
        str     q0, [x19, #1152]
        str     q1, [x19, #1168]
        bl      L0840
        add     x0, sp, #0x320
        mov     w1, wzr
        mov     w2, #0x600
        bl      L0840
        add     x0, sp, #0x920
        mov     w1, wzr
        mov     w2, #0x600
        bl      L0840
        add     x0, sp, #0xf20
        mov     w1, wzr
        mov     w2, #0x600
        bl      L0840
        add     x0, sp, #0x1, lsl #12
        add     x0, x0, #0x520
        mov     w1, wzr
        mov     w2, #0x1200
        bl      L0840
        add     x8, sp, #0x2, lsl #12
        add     x8, x8, #0x720
        movi    v0.2d, #0x0
        strb    wzr, [x8, #32]
        add     x8, sp, #0x2, lsl #12
        add     x8, x8, #0x720
        str     q0, [sp, #10032]
        str     q0, [sp, #10016]
        add     x8, sp, #0x2, lsl #12
        str     q0, [sp, #10128]
        add     x8, x8, #0x760
        str     q0, [sp, #10112]
        str     q0, [sp, #10096]
        str     q0, [sp, #10080]
        .inst   0xd0000108  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #10168]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    Ldc6c
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
Ldc6c:
        bl      L0830

// mlkem768_indcpa_enc (0x51c bytes)
Ldc70:
        stp     x29, x30, [sp, #-96]!
        stp     x28, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0x3, lsl #12
        sub     x9, x9, #0x360
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd0000108  // adrp x8, 0x2f000
        mov     x19, x0
        add     x0, sp, #0x1, lsl #12
        mov     x22, x1
        add     x0, x0, #0x520
        mov     x1, x2
        ldr     x8, [x8, #4088]
        mov     x20, x3
        mov     x21, x2
        ldr     x8, [x8]
        str     x8, [sp, #13144]
        bl      Leca0
        ldr     q0, [x21, #1152]
        add     x0, sp, #0x520
        ldr     q1, [x21, #1168]
        mov     x1, x22
        str     q0, [sp, #13088]
        str     q1, [sp, #13104]
        bl      L45c0
        add     x28, sp, #0x2, lsl #12
        mov     w8, #0x100
        add     x28, x28, #0x120
        add     x0, sp, #0x2, lsl #12
        add     x21, x28, #0x600
        add     x4, sp, #0x1, lsl #12
        ldr     q0, [sp, #13088]
        add     x1, x28, #0x200
        ldr     q1, [sp, #13104]
        add     x2, x28, #0x400
        mov     w9, #0x200
        strh    w8, [sp, #7040]
        mov     w8, #0x1
        add     x0, x0, #0x120
        add     x4, x4, #0xb20
        mov     x3, x21
        add     x27, sp, #0x1, lsl #12
        str     q0, [sp, #6944]
        str     q1, [sp, #6960]
        add     x23, x28, #0x800
        str     q0, [sp, #7008]
        add     x24, x28, #0xa00
        str     q1, [sp, #7024]
        add     x22, x28, #0xc00
        str     q0, [sp, #7072]
        add     x25, x28, #0xe00
        str     q1, [sp, #7088]
        add     x26, x28, #0x1, lsl #12
        str     q1, [sp, #7152]
        add     x27, x27, #0xb20
        str     q0, [sp, #7136]
        strh    w9, [sp, #7104]
        strh    wzr, [sp, #6976]
        strh    w8, [sp, #7168]
        bl      Lc4fc
        add     x4, sp, #0x1, lsl #12
        mov     w8, #0x101
        mov     w9, #0x201
        mov     w10, #0x2
        mov     w11, #0x102
        add     x4, x4, #0xb20
        mov     x0, x23
        mov     x1, x24
        mov     x2, x22
        mov     x3, x25
        strh    w8, [sp, #6976]
        strh    w9, [sp, #7040]
        strh    w10, [sp, #7104]
        strh    w11, [sp, #7168]
        bl      Lc4fc
        add     x1, sp, #0x1, lsl #12
        mov     w8, #0x202
        add     x1, x1, #0xb20
        mov     x0, x26
        strh    w8, [sp, #6976]
        bl      Lca30
        movi    v0.2d, #0x0
        add     x0, sp, #0x1, lsl #12
        add     x1, x27, #0x200
        add     x2, x27, #0x400
        mov     w8, #0xff
        add     x0, x0, #0xb20
        mov     x3, xzr
        mov     x4, x20
        str     q0, [sp, #7184]
        mov     w5, wzr
        str     q0, [sp, #7168]
        mov     w6, #0x1
        str     q0, [sp, #7152]
        mov     w7, #0x2
        str     q0, [sp, #7136]
        str     q0, [sp, #7120]
        str     q0, [sp, #7104]
        str     q0, [sp, #7088]
        str     q0, [sp, #7072]
        str     q0, [sp, #7056]
        str     q0, [sp, #7040]
        str     q0, [sp, #7024]
        str     q0, [sp, #7008]
        str     q0, [sp, #6992]
        str     q0, [sp, #6976]
        str     q0, [sp, #6960]
        str     q0, [sp, #6944]
        strb    w8, [sp]
        bl      Lefc8
        add     x23, sp, #0xf20
        mov     w8, #0x6
        add     x1, x23, #0x200
        add     x2, x23, #0x400
        add     x0, sp, #0xf20
        add     x3, sp, #0x320
        mov     x4, x20
        mov     w5, #0x3
        mov     w6, #0x4
        mov     w7, #0x5
        add     x24, sp, #0x320
        strb    w8, [sp]
        bl      Lefc8
        add     x0, sp, #0x1, lsl #12
        add     x0, x0, #0xb20
        bl      Lecd4
        add     x1, sp, #0x1, lsl #12
        add     x0, sp, #0x20
        add     x1, x1, #0xb20
        add     x25, sp, #0x20
        bl      Lef20
        add     x1, sp, #0x2, lsl #12
        add     x2, sp, #0x1, lsl #12
        add     x0, sp, #0x920
        add     x1, x1, #0x120
        add     x2, x2, #0xb20
        add     x3, sp, #0x20
        add     x20, sp, #0x920
        bl      Led14
        add     x2, sp, #0x1, lsl #12
        add     x0, x20, #0x200
        add     x2, x2, #0xb20
        add     x3, sp, #0x20
        mov     x1, x21
        bl      Led14
        add     x2, sp, #0x1, lsl #12
        add     x0, x20, #0x400
        add     x2, x2, #0xb20
        add     x3, sp, #0x20
        mov     x1, x22
        bl      Led14
        add     x1, sp, #0x1, lsl #12
        add     x2, sp, #0x1, lsl #12
        add     x0, sp, #0x720
        add     x1, x1, #0x520
        add     x2, x2, #0xb20
        add     x3, sp, #0x20
        add     x21, sp, #0x720
        bl      Led14
        add     x0, sp, #0x920
        bl      Lecf4
        add     x0, sp, #0x720
        bl      La46c
        add     x0, sp, #0x920
        add     x1, sp, #0xf20
        bl      Lef74
        add     x0, sp, #0x720
        add     x1, sp, #0x320
        bl      L837c
        add     x0, sp, #0x720
        add     x1, sp, #0x520
        bl      L837c
        add     x0, sp, #0x920
        bl      Lef54
        add     x0, sp, #0x720
        bl      L832c
        add     x1, sp, #0x920
        mov     x0, x19
        bl      Lec04
        add     x0, x19, #0x3c0
        add     x1, sp, #0x720
        bl      L22b0
        add     x0, sp, #0x20
        mov     w1, wzr
        mov     w2, #0x300
        bl      L0840
        movi    v0.2d, #0x0
        add     x8, sp, #0x520
        add     x0, sp, #0x920
        mov     w1, wzr
        mov     w2, #0x600
        str     q0, [sp, #1296]
        str     q0, [sp, #1280]
        str     q0, [sp, #1264]
        str     q0, [sp, #1248]
        str     q0, [sp, #1232]
        str     q0, [sp, #1216]
        str     q0, [sp, #1200]
        str     q0, [sp, #1184]
        str     q0, [sp, #1168]
        str     q0, [sp, #1152]
        str     q0, [sp, #1136]
        str     q0, [sp, #1120]
        str     q0, [sp, #1104]
        str     q0, [sp, #1088]
        str     q0, [sp, #1072]
        str     q0, [sp, #1056]
        str     q0, [sp, #1040]
        stp     q0, q0, [sp, #816]
        stp     q0, q0, [sp, #848]
        stp     q0, q0, [sp, #880]
        stp     q0, q0, [sp, #912]
        stp     q0, q0, [sp, #944]
        stp     q0, q0, [sp, #976]
        stp     q0, q0, [sp, #1008]
        str     q0, [sp, #800]
        str     q0, [sp, #1808]
        str     q0, [sp, #1792]
        str     q0, [sp, #1776]
        str     q0, [sp, #1760]
        str     q0, [sp, #1744]
        str     q0, [sp, #1728]
        str     q0, [sp, #1712]
        str     q0, [sp, #1696]
        str     q0, [sp, #1680]
        str     q0, [sp, #1664]
        str     q0, [sp, #1648]
        str     q0, [sp, #1632]
        str     q0, [sp, #1616]
        str     q0, [sp, #1600]
        str     q0, [sp, #1584]
        str     q0, [sp, #1568]
        str     q0, [sp, #1552]
        str     q0, [sp, #1536]
        str     q0, [sp, #1520]
        str     q0, [sp, #1504]
        str     q0, [sp, #1488]
        str     q0, [sp, #1472]
        str     q0, [sp, #1456]
        str     q0, [sp, #1440]
        str     q0, [sp, #1424]
        str     q0, [sp, #1408]
        str     q0, [sp, #1392]
        str     q0, [sp, #1376]
        str     q0, [sp, #1360]
        str     q0, [sp, #1344]
        str     q0, [sp, #1328]
        str     q0, [sp, #1312]
        str     q0, [sp, #2320]
        str     q0, [sp, #2304]
        str     q0, [sp, #2288]
        str     q0, [sp, #2272]
        str     q0, [sp, #2256]
        str     q0, [sp, #2240]
        str     q0, [sp, #2224]
        str     q0, [sp, #2208]
        str     q0, [sp, #2192]
        str     q0, [sp, #2176]
        str     q0, [sp, #2160]
        str     q0, [sp, #2144]
        str     q0, [sp, #2128]
        str     q0, [sp, #2112]
        str     q0, [sp, #2096]
        str     q0, [sp, #2080]
        str     q0, [sp, #2064]
        str     q0, [sp, #2048]
        str     q0, [sp, #2032]
        str     q0, [sp, #2016]
        str     q0, [sp, #2000]
        str     q0, [sp, #1984]
        str     q0, [sp, #1968]
        str     q0, [sp, #1952]
        str     q0, [sp, #1936]
        str     q0, [sp, #1920]
        str     q0, [sp, #1904]
        str     q0, [sp, #1888]
        str     q0, [sp, #1872]
        str     q0, [sp, #1856]
        str     q0, [sp, #1840]
        str     q0, [sp, #1824]
        bl      L0840
        add     x0, sp, #0xf20
        mov     w1, wzr
        mov     w2, #0x600
        bl      L0840
        add     x0, sp, #0x1, lsl #12
        add     x0, x0, #0x520
        mov     w1, wzr
        mov     w2, #0x600
        bl      L0840
        add     x8, sp, #0x1, lsl #12
        add     x0, sp, #0x1, lsl #12
        add     x8, x8, #0x520
        add     x0, x0, #0xb20
        mov     w1, wzr
        mov     w2, #0x600
        bl      L0840
        add     x0, sp, #0x2, lsl #12
        add     x0, x0, #0x120
        mov     w1, wzr
        mov     w2, #0x1200
        bl      L0840
        movi    v0.2d, #0x0
        add     x8, sp, #0x3, lsl #12
        add     x8, x8, #0x320
        str     q0, [sp, #13104]
        str     q0, [sp, #13088]
        .inst   0xb0000108  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #13144]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    Le188
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
Le188:
        bl      L0830

// mlkem768_indcpa_dec (0x214 bytes)
Le18c:
        stp     x29, x30, [sp, #-80]!
        str     x28, [sp, #16]
        stp     x24, x23, [sp, #32]
        stp     x22, x21, [sp, #48]
        stp     x20, x19, [sp, #64]
        mov     x29, sp
        sub     x9, sp, #0x1, lsl #12
        sub     x9, x9, #0x310
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb0000108  // adrp x8, 0x2f000
        mov     x21, x0
        add     x0, sp, #0xd00
        mov     x19, x2
        mov     x20, x1
        add     x22, sp, #0xd00
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #4872]
        bl      Lec38
        add     x1, x20, #0x3c0
        add     x0, sp, #0x500
        add     x20, sp, #0x500
        bl      L2db0
        add     x0, sp, #0x700
        mov     x1, x19
        add     x19, sp, #0x700
        bl      Leca0
        add     x0, sp, #0xd00
        bl      Lecd4
        mov     x0, sp
        add     x1, sp, #0xd00
        mov     x24, sp
        bl      Lef20
        add     x0, sp, #0x300
        add     x1, sp, #0x700
        add     x2, sp, #0xd00
        mov     x3, sp
        add     x23, sp, #0x300
        bl      Led14
        add     x0, sp, #0x300
        bl      La46c
        add     x0, sp, #0x500
        add     x1, sp, #0x300
        bl      L84fc
        add     x0, sp, #0x500
        bl      L832c
        add     x1, sp, #0x500
        mov     x0, x21
        bl      L46a0
        mov     x0, sp
        mov     w1, wzr
        mov     w2, #0x300
        bl      L0840
        movi    v0.2d, #0x0
        add     x0, sp, #0x700
        mov     w1, wzr
        mov     w2, #0x600
        str     q0, [sp, #1264]
        str     q0, [sp, #1248]
        str     q0, [sp, #1232]
        str     q0, [sp, #1216]
        str     q0, [sp, #1200]
        str     q0, [sp, #1184]
        str     q0, [sp, #1168]
        str     q0, [sp, #1152]
        str     q0, [sp, #1136]
        str     q0, [sp, #1120]
        str     q0, [sp, #1104]
        str     q0, [sp, #1088]
        str     q0, [sp, #1072]
        str     q0, [sp, #1056]
        str     q0, [sp, #1040]
        stp     q0, q0, [sp, #784]
        stp     q0, q0, [sp, #816]
        stp     q0, q0, [sp, #848]
        stp     q0, q0, [sp, #880]
        stp     q0, q0, [sp, #912]
        stp     q0, q0, [sp, #944]
        stp     q0, q0, [sp, #976]
        stp     q0, q0, [sp, #1008]
        str     q0, [sp, #768]
        str     q0, [sp, #1776]
        str     q0, [sp, #1760]
        str     q0, [sp, #1744]
        str     q0, [sp, #1728]
        str     q0, [sp, #1712]
        str     q0, [sp, #1696]
        str     q0, [sp, #1680]
        str     q0, [sp, #1664]
        str     q0, [sp, #1648]
        str     q0, [sp, #1632]
        str     q0, [sp, #1616]
        str     q0, [sp, #1600]
        str     q0, [sp, #1584]
        str     q0, [sp, #1568]
        str     q0, [sp, #1552]
        str     q0, [sp, #1536]
        str     q0, [sp, #1520]
        str     q0, [sp, #1504]
        str     q0, [sp, #1488]
        str     q0, [sp, #1472]
        str     q0, [sp, #1456]
        str     q0, [sp, #1440]
        str     q0, [sp, #1424]
        str     q0, [sp, #1408]
        str     q0, [sp, #1392]
        str     q0, [sp, #1376]
        str     q0, [sp, #1360]
        str     q0, [sp, #1344]
        str     q0, [sp, #1328]
        str     q0, [sp, #1312]
        str     q0, [sp, #1296]
        str     q0, [sp, #1280]
        bl      L0840
        add     x0, sp, #0xd00
        mov     w1, wzr
        mov     w2, #0x600
        bl      L0840
        .inst   0xb0000108  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #4872]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    Le39c
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #64]
        ldp     x22, x21, [sp, #48]
        ldp     x24, x23, [sp, #32]
        ldr     x28, [sp, #16]
        ldp     x29, x30, [sp], #80
        ret
Le39c:
        bl      L0830

// mlkem768_check_pk (0x150 bytes)
Le3a0:
        stp     x29, x30, [sp, #-48]!
        stp     x28, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0xa90
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb0000108  // adrp x8, 0x2f000
        mov     x19, x0
        add     x0, sp, #0x480
        mov     x1, x19
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #2696]
        bl      Leca0
        add     x0, sp, #0x480
        bl      Lef54
        mov     x0, sp
        add     x1, sp, #0x480
        mov     x20, sp
        bl      Lec6c
        movi    v0.2d, #0x0
        mov     x8, xzr
        movi    v1.2d, #0x0
        movi    v2.2d, #0x0
        movi    v3.2d, #0x0
Le404:
        add     x9, x19, x8
        add     x10, x20, x8
        add     x8, x8, #0x20
        cmp     x8, #0x480
        ldp     q4, q5, [x9]
        ldp     q6, q7, [x10]
        eor     v4.16b, v6.16b, v4.16b
        orr     v2.16b, v4.16b, v2.16b
        eor     v5.16b, v7.16b, v5.16b
        orr     v3.16b, v5.16b, v3.16b
        eor     v0.16b, v4.16b, v0.16b
        eor     v1.16b, v5.16b, v1.16b
        b.ne    Le404
        orr     v2.16b, v3.16b, v2.16b
        mov     w20, wzr
        ext     v3.16b, v2.16b, v2.16b, #8
        mov     x0, sp
        eor     v0.16b, v1.16b, v0.16b
        mov     w1, w20
        mov     w2, #0x480
        mov     w8, #0xfffffffc
        mov     x21, sp
        orr     v1.8b, v2.8b, v3.8b
        ext     v2.16b, v0.16b, v0.16b, #8
        fmov    x9, d1
        orr     x9, x9, x9, lsr #32
        lsr     x10, x9, #16
        eor     v0.8b, v0.8b, v2.8b
        orr     w9, w9, w10
        fmov    x10, d0
        orr     w9, w9, w9, lsr #8
        eor     x10, x10, x10, lsr #32
        sub     w9, w20, w9, uxtb
        eor     x10, x10, x10, lsr #16
        lsr     x11, x10, #8
        eor     w10, w10, w11
        eor     w9, w10, w9, lsr #16
        and     w9, w9, #0xff
        cmp     w9, w10, uxtb
        csel    w19, w20, w8, eq
        bl      L0840
        add     x0, sp, #0x480
        mov     w1, w20
        mov     w2, #0x600
        add     x20, sp, #0x480
        bl      L0840
        .inst   0xb0000108  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #2696]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    Le4ec
        mov     w0, w19
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldp     x28, x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
Le4ec:
        bl      L0830

// mlkem768_check_sk (0xe0 bytes)
Le4f0:
        stp     x29, x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x29, sp
        sub     x9, sp, #0x40
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb0000108  // adrp x8, 0x2f000
        mov     x19, x0
        add     x1, x0, #0x480
        mov     x0, sp
        mov     w2, #0x4a0
        mov     x20, sp
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #56]
        bl      L53c4
        ldp     q1, q2, [sp]
        mov     w8, wzr
        ldr     q0, [x19, #2352]
        ldr     q3, [x19, #2336]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v1.16b, v3.16b
        orr     v2.16b, v1.16b, v0.16b
        ext     v3.16b, v2.16b, v2.16b, #8
        eor     v0.16b, v1.16b, v0.16b
        ext     v1.16b, v0.16b, v0.16b, #8
        orr     v2.8b, v2.8b, v3.8b
        fmov    x9, d2
        eor     v0.8b, v0.8b, v1.8b
        fmov    x11, d0
        orr     x9, x9, x9, lsr #32
        lsr     x10, x9, #16
        orr     w9, w9, w10
        eor     x10, x11, x11, lsr #32
        movi    v0.2d, #0x0
        orr     w9, w9, w9, lsr #8
        eor     x10, x10, x10, lsr #16
        sub     w9, w8, w9, uxtb
        lsr     x11, x10, #8
        eor     w10, w10, w11
        eor     w9, w10, w9, lsr #16
        .inst   0xb000010b  // adrp x11, 0x2f000
        stp     q0, q0, [sp]
        and     w9, w9, #0xff
        ldr     x11, [x11, #4088]
        cmp     w9, w10, uxtb
        ldr     x12, [sp, #56]
        mov     w9, #0xfffffffb
        csel    w0, w8, w9, eq
        ldr     x11, [x11]
        cmp     x11, x12
        b.ne    Le5cc
        mov     sp, x29
        ldp     x20, x19, [sp, #16]
        ldp     x29, x30, [sp], #32
        ret
Le5cc:
        bl      L0830

// mlkem768_keypair_derand (0x98 bytes)
Le5d0:
        str     x30, [sp, #-48]!
        stp     x22, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x22, x2
        mov     x19, x1
        mov     x21, x0
        bl      Ld908
        mov     w20, w0
        cbz     w0, Le628
        mov     x0, x21
        mov     w1, wzr
        mov     w2, #0x4a0
        bl      L0840
        mov     x0, x19
        mov     w1, wzr
        mov     w2, #0x960
        bl      L0840
        mov     w0, w20
        ldp     x20, x19, [sp, #32]
        ldp     x22, x21, [sp, #16]
        ldr     x30, [sp], #48
        ret
Le628:
        add     x0, x19, #0x480
        mov     x1, x21
        mov     w2, #0x4a0
        bl      L0810
        add     x0, x19, #0x920
        mov     x1, x21
        mov     w2, #0x4a0
        bl      L53c4
        ldp     q1, q0, [x22, #32]
        str     q1, [x19, #2368]
        str     q0, [x19, #2384]
        mov     w0, w20
        ldp     x20, x19, [sp, #32]
        ldp     x22, x21, [sp, #16]
        ldr     x30, [sp], #48
        ret

// mlkem768_keypair (0xf4 bytes)
Le668:
        stp     x29, x30, [sp, #-48]!
        str     x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0x50
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb0000108  // adrp x8, 0x2f000
        mov     x19, x1
        mov     x21, x0
        mov     x0, sp
        mov     w1, #0x40
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #72]
        bl      L0820
        cbz     w0, Le6b0
        mov     w20, #0xfffffffd
        b       Le718
Le6b0:
        mov     x2, sp
        mov     x0, x21
        mov     x1, x19
        bl      Ld908
        mov     w20, w0
        cbz     w0, Le6ec
        mov     x0, x21
        mov     w1, wzr
        mov     w2, #0x4a0
        bl      L0840
        mov     x0, x19
        mov     w1, wzr
        mov     w2, #0x960
        bl      L0840
        b       Le718
Le6ec:
        add     x0, x19, #0x480
        mov     x1, x21
        mov     w2, #0x4a0
        bl      L0810
        add     x0, x19, #0x920
        mov     x1, x21
        mov     w2, #0x4a0
        bl      L53c4
        ldp     q0, q1, [sp, #32]
        str     q0, [x19, #2368]
        str     q1, [x19, #2384]
Le718:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        .inst   0xb0000108  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #72]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    Le758
        mov     w0, w20
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldr     x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
Le758:
        bl      L0830

// mlkem768_enc_derand (0x1e4 bytes)
Le75c:
        stp     x29, x30, [sp, #-96]!
        str     x28, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0xaa0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb0000108  // adrp x8, 0x2f000
        mov     x19, x1
        mov     x21, x0
        add     x0, sp, #0x480
        mov     x1, x2
        mov     x22, x3
        ldr     x8, [x8, #4088]
        mov     x20, x2
        ldr     x8, [x8]
        str     x8, [sp, #2712]
        bl      Leca0
        add     x0, sp, #0x480
        bl      Lef54
        mov     x0, sp
        add     x1, sp, #0x480
        mov     x23, sp
        bl      Lec6c
        movi    v0.2d, #0x0
        mov     x8, xzr
        movi    v1.2d, #0x0
        movi    v2.2d, #0x0
        movi    v3.2d, #0x0
Le7d8:
        add     x9, x20, x8
        add     x10, x23, x8
        add     x8, x8, #0x20
        cmp     x8, #0x480
        ldp     q4, q5, [x9]
        ldp     q6, q7, [x10]
        eor     v4.16b, v6.16b, v4.16b
        orr     v2.16b, v4.16b, v2.16b
        eor     v5.16b, v7.16b, v5.16b
        orr     v3.16b, v5.16b, v3.16b
        eor     v0.16b, v4.16b, v0.16b
        eor     v1.16b, v5.16b, v1.16b
        b.ne    Le7d8
        orr     v2.16b, v3.16b, v2.16b
        mov     w23, wzr
        ext     v3.16b, v2.16b, v2.16b, #8
        mov     x0, sp
        eor     v0.16b, v1.16b, v0.16b
        mov     w1, wzr
        mov     w2, #0x480
        mov     x24, sp
        orr     v1.8b, v2.8b, v3.8b
        ext     v2.16b, v0.16b, v0.16b, #8
        fmov    x8, d1
        orr     x8, x8, x8, lsr #32
        lsr     x9, x8, #16
        eor     v0.8b, v0.8b, v2.8b
        orr     w8, w8, w9
        fmov    x9, d0
        orr     w8, w8, w8, lsr #8
        eor     x9, x9, x9, lsr #32
        sub     w8, w23, w8, uxtb
        eor     x9, x9, x9, lsr #16
        lsr     x10, x9, #8
        eor     w25, w9, w10
        eor     w8, w25, w8, lsr #16
        and     w26, w8, #0xff
        bl      L0840
        add     x0, sp, #0x480
        mov     w1, wzr
        mov     w2, #0x600
        add     x23, sp, #0x480
        bl      L0840
        cmp     w26, w25, uxtb
        b.ne    Le8dc
        ldp     q0, q1, [x22]
        add     x0, x23, #0x20
        mov     x1, x20
        mov     w2, #0x4a0
        str     q0, [sp, #1152]
        str     q1, [sp, #1168]
        bl      L53c4
        mov     x0, sp
        add     x1, sp, #0x480
        mov     w2, #0x40
        bl      L5468
        add     x3, x24, #0x20
        add     x1, sp, #0x480
        mov     x0, x21
        mov     x2, x20
        bl      Ldc70
        cbnz    w0, Le8e0
        ldp     q0, q1, [sp]
        stp     q0, q1, [x19]
        b       Le8e0
Le8dc:
        mov     w0, #0xfffffffc
Le8e0:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        str     q0, [sp, #1200]
        add     x8, sp, #0x480
        str     q0, [sp, #1184]
        str     q0, [sp, #1168]
        str     q0, [sp, #1152]
        .inst   0xb0000108  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #2712]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    Le93c
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldr     x28, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
Le93c:
        bl      L0830

// mlkem768_enc (0x9c bytes)
Le940:
        stp     x29, x30, [sp, #-48]!
        str     x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0x30
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb0000108  // adrp x8, 0x2f000
        mov     x20, x1
        mov     x21, x0
        mov     x0, sp
        mov     w1, #0x20
        mov     x19, x2
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #40]
        bl      L0820
        cbz     w0, Le98c
        mov     w0, #0xfffffffd
        b       Le9a0
Le98c:
        mov     x3, sp
        mov     x0, x21
        mov     x1, x20
        mov     x2, x19
        bl      Le75c
Le9a0:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        .inst   0xb0000108  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #40]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    Le9d8
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldr     x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
Le9d8:
        bl      L0830

// mlkem768_dec (0x228 bytes)
Le9dc:
        stp     x29, x30, [sp, #-64]!
        stp     x28, x23, [sp, #16]
        stp     x22, x21, [sp, #32]
        stp     x20, x19, [sp, #48]
        mov     x29, sp
        sub     x9, sp, #0x500
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb0000108  // adrp x8, 0x2f000
        mov     x19, x0
        mov     x0, x2
        mov     x21, x2
        mov     x20, x1
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #1272]
        bl      Le4f0
        mov     w22, w0
        cbnz    w0, Leb8c
        add     x0, sp, #0x4a0
        mov     x1, x20
        mov     x2, x21
        bl      Le18c
        mov     w22, w0
        cbnz    w0, Leb8c
        ldr     q0, [x21, #2336]
        add     x0, sp, #0x460
        ldr     q1, [x21, #2352]
        add     x1, sp, #0x4a0
        mov     w2, #0x40
        add     x22, x21, #0x480
        str     q0, [sp, #1216]
        add     x23, sp, #0x460
        str     q1, [sp, #1232]
        bl      L5468
        add     x3, x23, #0x20
        mov     x0, sp
        add     x1, sp, #0x4a0
        mov     x2, x22
        mov     x23, sp
        bl      Ldc70
        mov     w22, w0
        cbnz    w0, Leb8c
        movi    v0.2d, #0x0
        mov     x8, xzr
        movi    v1.2d, #0x0
        movi    v2.2d, #0x0
        movi    v3.2d, #0x0
Lea98:
        add     x9, x20, x8
        add     x10, x23, x8
        add     x8, x8, #0x20
        cmp     x8, #0x440
        ldp     q4, q5, [x9]
        ldp     q6, q7, [x10]
        eor     v4.16b, v6.16b, v4.16b
        orr     v2.16b, v4.16b, v2.16b
        eor     v5.16b, v7.16b, v5.16b
        orr     v3.16b, v5.16b, v3.16b
        eor     v0.16b, v4.16b, v0.16b
        eor     v1.16b, v5.16b, v1.16b
        b.ne    Lea98
        orr     v2.16b, v3.16b, v2.16b
        mov     w22, wzr
        ext     v3.16b, v2.16b, v2.16b, #8
        mov     x8, sp
        eor     v0.16b, v1.16b, v0.16b
        add     x0, x8, #0x20
        ext     v1.16b, v0.16b, v0.16b, #8
        mov     x1, x20
        mov     w2, #0x440
        orr     v2.8b, v2.8b, v3.8b
        fmov    x9, d2
        eor     v0.8b, v0.8b, v1.8b
        fmov    x11, d0
        orr     x9, x9, x9, lsr #32
        lsr     x10, x9, #16
        orr     w9, w9, w10
        eor     x10, x11, x11, lsr #32
        orr     w9, w9, w9, lsr #8
        eor     x10, x10, x10, lsr #16
        sub     w9, w22, w9, uxtb
        lsr     x11, x10, #8
        eor     w10, w10, w11
        eor     w9, w10, w9, lsr #16
        ldr     q0, [x21, #2368]
        ldr     q1, [x21, #2384]
        eor     w21, w9, w10
        stp     q0, q1, [sp]
        bl      L0810
        mov     x2, sp
        mov     x0, x19
        mov     w1, #0x20
        mov     w3, #0x460
        bl      L52f0
        mov     x8, xzr
        sub     w9, w22, w21, uxtb
        add     x10, sp, #0x460
Leb5c:
        ldrb    w11, [x19, x8]
        mov     w12, w9
        ldrb    w13, [x10, x8]
        lsr     w12, w12, #16
        and     w11, w11, w12
        bic     w13, w13, w12
        orr     w11, w11, w13
        strb    w11, [x19, x8]
        add     x8, x8, #0x1
        cmp     x8, #0x20
        b.ne    Leb5c
        mov     w22, wzr
Leb8c:
        mov     x0, sp
        mov     w1, wzr
        mov     w2, #0x460
        mov     x19, sp
        bl      L0840
        movi    v0.2d, #0x0
        add     x8, sp, #0x460
        str     q0, [sp, #1168]
        str     q0, [sp, #1152]
        str     q0, [sp, #1136]
        str     q0, [sp, #1120]
        str     q0, [sp, #1232]
        add     x8, sp, #0x4a0
        str     q0, [sp, #1216]
        str     q0, [sp, #1200]
        str     q0, [sp, #1184]
        .inst   0xb0000108  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #1272]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    Lec00
        mov     w0, w22
        mov     sp, x29
        ldp     x20, x19, [sp, #48]
        ldp     x22, x21, [sp, #32]
        ldp     x28, x23, [sp, #16]
        ldp     x29, x30, [sp], #64
        ret
Lec00:
        bl      L0830

// mlkem768_polyvec_compress_du (0x34 bytes)
Lec04:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L2d14
        add     x0, x20, #0x140
        add     x1, x19, #0x200
        bl      L2d14
        add     x0, x20, #0x280
        add     x1, x19, #0x400
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L2d14

// mlkem768_polyvec_decompress_du (0x34 bytes)
Lec38:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L317c
        add     x0, x20, #0x200
        add     x1, x19, #0x140
        bl      L317c
        add     x0, x20, #0x400
        add     x1, x19, #0x280
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L317c

// mlkem768_polyvec_tobytes (0x34 bytes)
Lec6c:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L4080
        add     x0, x20, #0x180
        add     x1, x19, #0x200
        bl      L4080
        add     x0, x20, #0x300
        add     x1, x19, #0x400
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L4080

// mlkem768_polyvec_frombytes (0x34 bytes)
Leca0:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L42d0
        add     x0, x20, #0x200
        add     x1, x19, #0x180
        bl      L42d0
        add     x0, x20, #0x400
        add     x1, x19, #0x300
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L42d0

// mlkem768_polyvec_ntt (0x20 bytes)
Lecd4:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L8c28
        add     x0, x19, #0x200
        bl      L8c28
        add     x0, x19, #0x400
        ldp     x30, x19, [sp], #16
        b       L8c28

// mlkem768_polyvec_invntt_tomont (0x20 bytes)
Lecf4:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      La46c
        add     x0, x19, #0x200
        bl      La46c
        add     x0, x19, #0x400
        ldp     x30, x19, [sp], #16
        b       La46c

// mlkem768_polyvec_basemul_acc_montgomery_cached (0x20c bytes)
Led14:
        add     x8, x3, #0x300
        add     x10, x0, #0x200
        cmp     x8, x0
        add     x9, x2, #0x600
        ccmp    x10, x3, #0x0, hi
        add     x11, x1, #0x600
        cset    w8, hi
        cmp     x9, x0
        ccmp    x10, x2, #0x0, hi
        cset    w9, hi
        cmp     x10, x1
        ccmp    x11, x0, #0x0, hi
        b.hi    Lee5c
        tbnz    w8, #0, Lee5c
        cbnz    w9, Lee5c
        mov     w10, #0xf3010000
        mov     x8, xzr
        add     x9, x3, #0x100
        mvni    v1.4s, #0xd, lsl #8
        dup     v0.4s, w10
Led64:
        add     x10, x1, x8
        add     x11, x2, x8
        add     x12, x10, #0x200
        ldur    q17, [x9, #-256]
        ldr     q22, [x9]
        ld2     {v2.8h-v3.8h}, [x10]
        add     x10, x10, #0x400
        ld2     {v4.8h-v5.8h}, [x11]
        ld2     {v6.8h-v7.8h}, [x12]
        add     x12, x11, #0x200
        smull   v16.4s, v4.4h, v2.4h
        smull2  v20.4s, v4.8h, v2.8h
        ld2     {v18.8h-v19.8h}, [x12]
        smull   v21.4s, v5.4h, v2.4h
        smull2  v23.4s, v5.8h, v2.8h
        smlal   v16.4s, v17.4h, v3.4h
        smlal2  v20.4s, v17.8h, v3.8h
        ld2     {v24.8h-v25.8h}, [x10]
        smlal   v21.4s, v4.4h, v3.4h
        add     x10, x11, #0x400
        smlal2  v23.4s, v4.8h, v3.8h
        smlal   v16.4s, v22.4h, v7.4h
        smlal2  v20.4s, v22.8h, v7.8h
        ldr     q2, [x9, #256]
        smlal   v21.4s, v18.4h, v7.4h
        ld2     {v3.8h-v4.8h}, [x10]
        smlal2  v23.4s, v18.8h, v7.8h
        add     x10, x0, x8
        smlal   v16.4s, v18.4h, v6.4h
        add     x8, x8, #0x20
        smlal2  v20.4s, v18.8h, v6.8h
        add     x9, x9, #0x10
        smlal   v21.4s, v19.4h, v6.4h
        cmp     x8, #0x200
        smlal2  v23.4s, v19.8h, v6.8h
        smlal   v16.4s, v2.4h, v25.4h
        smlal2  v20.4s, v2.8h, v25.8h
        smlal   v21.4s, v3.4h, v25.4h
        smlal2  v23.4s, v3.8h, v25.8h
        smlal   v16.4s, v3.4h, v24.4h
        smlal2  v20.4s, v3.8h, v24.8h
        smlal   v21.4s, v4.4h, v24.4h
        smlal2  v23.4s, v4.8h, v24.8h
        mul     v2.4s, v16.4s, v0.4s
        mul     v3.4s, v20.4s, v0.4s
        mul     v4.4s, v21.4s, v0.4s
        mul     v5.4s, v23.4s, v0.4s
        sshr    v2.4s, v2.4s, #16
        sshr    v3.4s, v3.4s, #16
        mul     v2.4s, v2.4s, v1.4s
        sshr    v4.4s, v4.4s, #16
        mul     v3.4s, v3.4s, v1.4s
        addhn   v6.4h, v2.4s, v16.4s
        mul     v2.4s, v4.4s, v1.4s
        sshr    v4.4s, v5.4s, #16
        addhn2  v6.8h, v3.4s, v20.4s
        mul     v3.4s, v4.4s, v1.4s
        addhn   v7.4h, v2.4s, v21.4s
        addhn2  v7.8h, v3.4s, v23.4s
        st2     {v6.8h-v7.8h}, [x10]
        b.ne    Led64
        b       Lef1c
Lee5c:
        mov     x8, xzr
        mov     w9, #0xf3010000
        add     x10, x3, #0x100
        mov     w11, #0xfffff2ff
Lee6c:
        add     x12, x1, x8
        add     x14, x2, x8
        ldursh  w13, [x10, #-256]
        ldrsh   w15, [x10]
        ldrsh   w17, [x12, #2]
        ldrsh   w18, [x14]
        ldrsh   w3, [x12]
        ldrsh   w4, [x14, #2]
        mul     w13, w13, w17
        ldrsh   w5, [x12, #514]
        mul     w17, w18, w17
        madd    w13, w18, w3, w13
        ldrsh   w18, [x14, #512]
        madd    w17, w4, w3, w17
        ldrsh   w3, [x12, #512]
        madd    w13, w15, w5, w13
        ldrsh   w15, [x14, #514]
        madd    w17, w18, w5, w17
        ldrsh   w16, [x10, #256]
        ldrsh   w4, [x12, #1026]
        madd    w13, w18, w3, w13
        ldrsh   w18, [x14, #1024]
        madd    w15, w15, w3, w17
        ldrsh   w12, [x12, #1024]
        add     x10, x10, #0x2
        ldrsh   w14, [x14, #1026]
        madd    w13, w16, w4, w13
        madd    w15, w18, w4, w15
        madd    w13, w18, w12, w13
        madd    w12, w14, w12, w15
        mul     w14, w13, w9
        mul     w15, w12, w9
        asr     w14, w14, #16
        asr     w15, w15, #16
        madd    w13, w14, w11, w13
        add     x14, x0, x8
        madd    w12, w15, w11, w12
        add     x8, x8, #0x4
        lsr     w13, w13, #16
        cmp     x8, #0x200
        lsr     w12, w12, #16
        strh    w13, [x14]
        strh    w12, [x14, #2]
        b.ne    Lee6c
Lef1c:
        ret

// mlkem768_polyvec_mulcache_compute (0x34 bytes)
Lef20:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L867c
        add     x0, x20, #0x100
        add     x1, x19, #0x200
        bl      L867c
        add     x0, x20, #0x200
        add     x1, x19, #0x400
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L867c

// mlkem768_polyvec_reduce (0x20 bytes)
Lef54:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L832c
        add     x0, x19, #0x200
        bl      L832c
        add     x0, x19, #0x400
        ldp     x30, x19, [sp], #16
        b       L832c

// mlkem768_polyvec_add (0x34 bytes)
Lef74:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L837c
        add     x0, x20, #0x200
        add     x1, x19, #0x200
        bl      L837c
        add     x0, x20, #0x400
        add     x1, x19, #0x400
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L837c

// mlkem768_polyvec_tomont (0x20 bytes)
Lefa8:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L8298
        add     x0, x19, #0x200
        bl      L8298
        add     x0, x19, #0x400
        ldp     x30, x19, [sp], #16
        b       L8298

// mlkem768_poly_getnoise_eta1_4x (0x18c bytes)
Lefc8:
        stp     x29, x30, [sp, #-80]!
        stp     x28, x25, [sp, #16]
        stp     x24, x23, [sp, #32]
        stp     x22, x21, [sp, #48]
        stp     x20, x19, [sp, #64]
        mov     x29, sp
        sub     x9, sp, #0x330
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb0000108  // adrp x8, 0x2f000
        ldrb    w10, [x29, #80]
        add     x11, sp, #0x20
        add     x12, sp, #0x120
        add     x9, x11, #0x80
        add     x24, x12, #0x80
        ldr     x8, [x8, #4088]
        add     x25, x12, #0x100
        add     x20, x12, #0x180
        mov     x19, x3
        mov     x21, x2
        mov     x22, x1
        ldr     x8, [x8]
        mov     x23, x0
        add     x0, sp, #0x120
        mov     x1, x24
        mov     x2, x25
        mov     x3, x20
        str     x8, [sp, #808]
        add     x8, x11, #0x40
        ldp     q0, q1, [x4]
        strb    w5, [sp, #64]
        add     x11, x11, #0xc0
        strb    w6, [sp, #128]
        add     x5, sp, #0x20
        strb    w7, [sp, #192]
        mov     w4, #0x80
        strb    w10, [sp, #256]
        mov     w10, #0x21
        mov     x6, x8
        mov     x7, x9
        stp     q0, q1, [sp, #32]
        stp     q0, q1, [sp, #96]
        stp     q0, q1, [sp, #160]
        stp     q0, q1, [sp, #224]
        stp     x11, x10, [sp]
        bl      L5770
        add     x1, sp, #0x120
        mov     x0, x23
        bl      Lcc10
        mov     x0, x22
        mov     x1, x24
        bl      Lcc10
        mov     x0, x21
        mov     x1, x25
        bl      Lcc10
        cbz     x19, Lf0b0
        mov     x0, x19
        mov     x1, x20
        bl      Lcc10
Lf0b0:
        movi    v0.2d, #0x0
        add     x8, sp, #0x120
        stp     q0, q0, [sp, #288]
        stp     q0, q0, [sp, #320]
        stp     q0, q0, [sp, #352]
        stp     q0, q0, [sp, #384]
        stp     q0, q0, [sp, #416]
        stp     q0, q0, [sp, #448]
        stp     q0, q0, [sp, #480]
        stp     q0, q0, [sp, #512]
        stp     q0, q0, [sp, #544]
        stp     q0, q0, [sp, #576]
        stp     q0, q0, [sp, #608]
        stp     q0, q0, [sp, #640]
        stp     q0, q0, [sp, #672]
        stp     q0, q0, [sp, #704]
        stp     q0, q0, [sp, #736]
        stp     q0, q0, [sp, #768]
        stp     q0, q0, [sp, #64]
        stp     q0, q0, [sp, #96]
        add     x8, sp, #0x20
        stp     q0, q0, [sp, #32]
        stp     q0, q0, [sp, #128]
        stp     q0, q0, [sp, #160]
        stp     q0, q0, [sp, #192]
        stp     q0, q0, [sp, #224]
        stp     q0, q0, [sp, #256]
        .inst   0x90000108  // adrp x8, 0x2f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #808]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    Lf150
        mov     sp, x29
        ldp     x20, x19, [sp, #64]
        ldp     x22, x21, [sp, #48]
        ldp     x24, x23, [sp, #32]
        ldp     x28, x25, [sp, #16]
        ldp     x29, x30, [sp], #80
        ret
Lf150:
        bl      L0830

// Padding (0xf154 to 0xf160)

        .long   0x00000000
        .long   0x00000000
        .long   0x00000000

// The read-only data (0xf160 to 0xf940)

        .quad   0x19180908fffefffe
        .quad   0xfffefffefffefffe
        .quad   0xfffefffe1b1a0b0a
        .quad   0xfffefffefffefffe
        .quad   0x1d1c0d0cfffefffe
        .quad   0xfffefffefffefffe
        .quad   0xfffefffe1d1c0d0c
        .quad   0xfffefffefffefffe
        .quad   0x1f1e0f0efffefffe
        .quad   0xfffefffefffefffe
        .quad   0xfffefffe1f1e0f0e
        .quad   0xfffefffefffefffe
        .quad   0xffffff05ffffff00
        .quad   0xffffff0fffffff0a
        .quad   0xffffffff100b0601
        .quad   0xffffffffffffffff
        .quad   0xffffff01ffffff00
        .quad   0xffffff03ffffff02
        .quad   0xffffffff110c0702
        .quad   0xffffffffffffffff
        .quad   0xffffffff120d0803
        .quad   0xffffffffffffffff
        .quad   0xffffffff130e0904
        .quad   0xffffffffffffffff
        .quad   0x03ffffffffffffff
        .quad   0xffffff1c17120d08
        .quad   0xff1e19140f0a0500
        .quad   0xffffffffffffffff
        .quad   0x1706050403020100
        .quad   0xffffff1c1b1a1918
        .quad   0x0706050403020100
        .quad   0x1b16110c0b0a0908
        .quad   0x04ffffffffffffff
        .quad   0xffffff1d18130e09
        .quad   0xff1f1a15100b0601
        .quad   0xffffffffffffffff
        .quad   0x0706050403020100
        .quad   0x1c17120c0b0a0908
        .quad   0x0500ffffffffffff
        .quad   0xffffff1e19140f0a
        .quad   0xffff1b16110c0702
        .quad   0xffffffffffffffff
        .quad   0x1716050403020100
        .quad   0xfffe1d1c1b1a1918
        .quad   0x0706050403020100
        .quad   0x1d18130c0b0a0908
        .quad   0x0601ffffffffffff
        .quad   0xffffff1f1a15100b
        .quad   0xffff1c17120d0803
        .quad   0xffffffffffffffff
        .quad   0x0706050403020100
        .quad   0x1e19140c0b0a0908
        .quad   0x0702ffffffffffff
        .quad   0xffffffff1b16110c
        .quad   0xffff1d18130e0904
        .quad   0xffffffffffffffff
        .quad   0x1716050403020100
        .quad   0xfffefffe1b1a1918
        .quad   0x0706050403020100
        .quad   0x1f1a15100b0a0908
        .quad   0x1918111009080100
        .quad   0xfffefffefffefffe
        .quad   0xfffefffefffefffe
        .quad   0xfffe111009080100
        .quad   0x1b1a13120b0a0302
        .quad   0xfffefffefffefffe
        .quad   0xfffefffefffefffe
        .quad   0xfffe13120b0a0302
        .quad   0x1d1c15140d0c0504
        .quad   0xfffefffefffefffe
        .quad   0xfffefffefffefffe
        .quad   0xfffe15140d0c0504
        .quad   0x1f1e17160f0e0706
        .quad   0xfffefffefffefffe
        .quad   0xfffefffefffefffe
        .quad   0xfffe17160f0e0706
        .quad   0xfffefffefffefffe
        .quad   0xfffe191809080100
        .quad   0xfffefffefffefffe
        .quad   0xfffe1b1a0b0a0302
        .quad   0xfffefffefffefffe
        .quad   0xfffe1d1c0d0c0504
        .quad   0xfffefffefffefffe
        .quad   0xfffe1f1e0f0e0706
        .quad   0x0000000500000008
        .quad   0x000000070000000a
        .quad   0x000007e000000700
        .quad   0x0000078000000400
        .quad   0xc8670000821d0000
        .quad   0xab690000500e0000
        .quad   0x2bae0000feb10000
        .quad   0x344b0000d32b0000
        .quad   0x379900007de30000
        .quad   0x54970000aff20000
        .quad   0xd4520000014f0000
        .quad   0xcbb500002cd50000
        .quad   0x5a340000c5dd0000
        .quad   0x1575000018260000
        .quad   0x334b000093a60000
        .quad   0xee15000003b10000
        .quad   0xa5cc00003a230000
        .quad   0xea8b0000e7da0000
        .quad   0xccb500006c5a0000
        .quad   0x11eb0000fc4f0000
        .quad   0xb6cb000071f70000
        .quad   0x315f00008fa60000
        .quad   0x810a00007d0a0000
        .quad   0x766d000029870000
        .quad   0x493500008e090000
        .quad   0xcea10000705a0000
        .quad   0x7ef6000082f60000
        .quad   0x89930000d6790000
        .quad   0x4c490000c7a20000
        .quad   0xceb50000eb640000
        .quad   0x4e840000b7ca0000
        .quad   0x485d000044980000
        .quad   0xb3b70000385e0000
        .quad   0x314b0000149c0000
        .quad   0xb17c000048360000
        .quad   0xb7a30000bb680000
        .quad   0x3bfb0000e32a0000
        .quad   0x818000005f470000
        .quad   0x4f49000086310000
        .quad   0x08620000635b0000
        .quad   0xc40500001cd60000
        .quad   0x7e800000a0b90000
        .quad   0xb0b7000079cf0000
        .quad   0xf79e00009ca50000
        .quad   0xd4dc00005e960000
        .quad   0x38850000425d0000
        .quad   0xe7780000ae410000
        .quad   0xc5c900002ac20000
        .quad   0x2b240000a16a0000
        .quad   0xc77b0000bda30000
        .quad   0x1888000051bf0000
        .quad   0x3a370000d53e0000
        .quad   0x5aaa0000a81a0000
        .quad   0xbbde00002a9a0000
        .quad   0xac060000285f0000
        .quad   0xb11a0000e1020000
        .quad   0xa556000057e60000
        .quad   0x44220000d5660000
        .quad   0x53fa0000d7a10000
        .quad   0x4ee600001efe0000
        .quad   0x1e4c00005dbe0000
        .quad   0x5a5c0000bbf20000
        .quad   0xa2cc00007b940000
        .quad   0xb0df00006fe40000
        .quad   0xfffefffefffefffe
        .quad   0x1918111009080100
        .quad   0xfffefffefffefffe
        .quad   0x1b1a13120b0a0302
        .quad   0xfffefffefffefffe
        .quad   0x1d1c15140d0c0504
        .quad   0xfffefffefffefffe
        .quad   0x1f1e17160f0e0706
        .quad   0xfffffffafffffffe
        .quad   0xfffffff2fffffff6
        .quad   0xffffffecfffffff0
        .quad   0xffffffe4ffffffe8
        .quad   0xfffffff9fffffffe
        .quad   0xfffffffffffffffc
        .quad   0x0069060e0367fb1d
        .quad   0x034b022b01aefbb1
        .quad   0xff97f9f2fc9904e3
        .quad   0xfcb5fdd5fe52044f
        .quad   0x06750626fe34fedd
        .quad   0xff1500b1024b01a6
        .quad   0xf98bf9da01cc0123
        .quad   0x00ebff4ffdb5fe5a
        .quad   0x045ffda605cbfcf7
        .quad   0xff6d0487030aff0a
        .quad   0xfba1025afa350309
        .quad   0x0093fb79fcf600f6
        .quad   0xffb5ff64014901a2
        .quad   0x015dfc980284f9ca
        .quad   0x004b009cfeb7fe5e
        .quad   0xfea30368fd7c0636
        .quad   0x0180fa47fafb052a
        .quad   0x0262025b04490331
        .quad   0xfe8005b90505fad6
        .quad   0xfd9efda5fbb7fccf
        .quad   0xf985fb5d00dcfc96
        .quad   0xfac904c2ff78fb41
        .quad   0x067b04a3ff24036a
        .quad   0x0537fb3e008804bf
        .quad   0x01defc9afcaafa1a
        .quad   0x031afb02fa06fb5f
        .quad   0xfe220366035605e6
        .quad   0xfce604fe05fa04a1
        .quad   0x065c05f2fa4c03be
        .quad   0x03df03e4feccff94
        .quad   0xfffffff4fffffff8
        .quad   0xffffffeaffffffee
        .quad   0xfffffff4fffffffa
        .quad   0xfffffff1fffffff7
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
