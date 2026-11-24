// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// The code and read-only data of mlkem-native's libmlkem.so (clang 17, -O2)
//
// This is a transcription of the binary
// binaries/multilevel/clang17/O2/libmlkem.so from the binary branch of
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

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_libmlkem_clang17_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_libmlkem_clang17_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_libmlkem_clang17_O2):

// ELF header and dynamic linking information (0x0 to 0x7f0)

        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x0000000100b70003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x0000000000025b58
        .quad   0x0038004000000000
        .quad   0x0018001900400005
        .quad   0x0000000500000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000000000c7f0
        .quad   0x000000000000c7f0
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
        .quad   0x0000000000007000
        .quad   0x00000000000002a0
        .quad   0x000800120000003e
        .quad   0x00000000000017e0
        .quad   0x00000000000000e0
        .quad   0x000800120000010d
        .quad   0x0000000000006d8c
        .quad   0x00000000000001d8
        .quad   0x00080012000001a9
        .quad   0x000000000000a474
        .quad   0x00000000000002b8
        .quad   0x000800120000014d
        .quad   0x0000000000009f98
        .quad   0x00000000000000e0
        .quad   0x0008001200000071
        .quad   0x0000000000001948
        .quad   0x00000000000000f4
        .quad   0x000800120000002b
        .quad   0x0000000000001690
        .quad   0x0000000000000150
        .quad   0x00080012000000a4
        .quad   0x0000000000001c20
        .quad   0x000000000000009c
        .quad   0x00080012000000e4
        .quad   0x0000000000006c10
        .quad   0x0000000000000088
        .quad   0x000800120000013b
        .quad   0x0000000000009e48
        .quad   0x0000000000000150
        .quad   0x0008001200000177
        .quad   0x000000000000a100
        .quad   0x00000000000000f4
        .quad   0x000800120000008f
        .quad   0x0000000000001a3c
        .quad   0x00000000000001e4
        .quad   0x000800120000015f
        .quad   0x000000000000a078
        .quad   0x0000000000000088
        .quad   0x0008001200000121
        .quad   0x0000000000006f64
        .quad   0x000000000000009c
        .quad   0x00080012000000d2
        .quad   0x0000000000006b30
        .quad   0x00000000000000e0
        .quad   0x0008001200000188
        .quad   0x000000000000a1f4
        .quad   0x00000000000001e4
        .quad   0x000800120000019c
        .quad   0x000000000000a3d8
        .quad   0x000000000000009c
        .quad   0x00080012000000c0
        .quad   0x00000000000069e0
        .quad   0x0000000000000150
        .quad   0x00080012000000b2
        .quad   0x0000000000001cbc
        .quad   0x00000000000002b8
        .quad   0x00080012000000fc
        .quad   0x0000000000006c98
        .quad   0x00000000000000f4
        .quad   0x0008001200000051
        .quad   0x00000000000018c0
        .quad   0x0000000000000088
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
        .quad   0x6d2f706d742f006f
        .quad   0x69616d2d6d656b6c
        .quad   0x6972616e69622d6e
        .quad   0x52353174382e7365
        .quad   0x72756f732f584167
        .quad   0x757074756f2f6563
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

// The procedure linkage table and the code (0x7f0 to 0xac80)
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

// mlkem1024_gen_matrix (0x21c bytes)
L0850:
        stp     x29, x30, [sp, #-48]!
        str     x28, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0x110
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xf00000e8  // adrp x8, 0x1f000
        mov     w20, w2
        mov     x19, x0
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #264]
        ldp     q0, q1, [x1]
        stp     q0, q1, [sp]
        stp     q0, q1, [sp, #64]
        stp     q0, q1, [sp, #128]
        stp     q0, q1, [sp, #192]
        cbz     w2, L08b0
        mov     w9, wzr
        mov     w10, #0x100
        mov     w11, #0x200
        strh    wzr, [sp, #32]
        mov     w8, #0x3
        b       L08c4
L08b0:
        mov     w8, wzr
        mov     w10, #0x1
        mov     w11, #0x2
        mov     w9, #0x3
        strh    wzr, [sp, #32]
L08c4:
        add     x1, x19, #0x200
        add     x2, x19, #0x400
        add     x3, x19, #0x600
        mov     x4, sp
        mov     x0, x19
        strh    w10, [sp, #96]
        strh    w11, [sp, #160]
        strb    w9, [sp, #224]
        strb    w8, [sp, #225]
        bl      L8750
        cbz     w20, L0910
        mov     w8, #0x1
        mov     w10, #0x101
        mov     w11, #0x201
        mov     w9, #0x3
        strh    w8, [sp, #32]
        strh    w10, [sp, #96]
        strh    w11, [sp, #160]
        b       L0930
L0910:
        mov     w10, #0x100
        mov     w11, #0x101
        mov     w12, #0x102
        mov     w9, #0x1
        mov     w8, #0x3
        strh    w10, [sp, #32]
        strh    w11, [sp, #96]
        strh    w12, [sp, #160]
L0930:
        add     x0, x19, #0x800
        add     x1, x19, #0xa00
        add     x2, x19, #0xc00
        add     x3, x19, #0xe00
        mov     x4, sp
        strb    w8, [sp, #224]
        strb    w9, [sp, #225]
        bl      L8750
        cbz     w20, L096c
        mov     w8, #0x2
        mov     w10, #0x102
        mov     w9, #0x3
        strh    w8, [sp, #32]
        strh    w10, [sp, #96]
        b       L0984
L096c:
        mov     w10, #0x200
        mov     w11, #0x201
        mov     w9, #0x2
        mov     w8, #0x3
        strh    w10, [sp, #32]
        strh    w11, [sp, #96]
L0984:
        mov     w11, #0x1200
        mov     w10, #0x202
        add     x1, x19, x11
        mov     w11, #0x1400
        add     x2, x19, x11
        mov     w11, #0x1600
        add     x0, x19, #0x1, lsl #12
        add     x3, x19, x11
        mov     x4, sp
        strh    w10, [sp, #160]
        strb    w8, [sp, #224]
        strb    w9, [sp, #225]
        bl      L8750
        cbz     w20, L09cc
        mov     w8, #0x3
        mov     w9, #0x103
        mov     w10, #0x203
        b       L09d8
L09cc:
        mov     w8, #0x300
        mov     w9, #0x301
        mov     w10, #0x302
L09d8:
        strh    w9, [sp, #96]
        mov     w9, #0x1800
        strh    w10, [sp, #160]
        mov     w10, #0x1a00
        add     x0, x19, x9
        add     x1, x19, x10
        mov     w9, #0x1c00
        mov     w10, #0x1e00
        strh    w8, [sp, #32]
        mov     w8, #0x303
        add     x2, x19, x9
        add     x3, x19, x10
        mov     x4, sp
        mov     x19, sp
        strh    w8, [sp, #224]
        bl      L8750
        movi    v0.2d, #0x0
        .inst   0xf00000e8  // adrp x8, 0x1f000
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        stp     q0, q0, [sp, #64]
        stp     q0, q0, [sp, #96]
        stp     q0, q0, [sp, #128]
        stp     q0, q0, [sp, #160]
        stp     q0, q0, [sp, #192]
        stp     q0, q0, [sp, #224]
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #264]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L0a68
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldr     x28, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L0a68:
        bl      L0830

// mlkem1024_indcpa_keypair_derand (0x40c bytes)
L0a6c:
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
        .inst   0xf00000e8  // adrp x8, 0x1f000
        mov     x20, x1
        mov     x19, x0
        add     x9, sp, #0x3, lsl #12
        add     x0, sp, #0x3, lsl #12
        add     x1, sp, #0x3, lsl #12
        ldr     x8, [x8, #4088]
        add     x9, x9, #0xc20
        add     x0, x0, #0xc60
        add     x1, x1, #0xc20
        add     x24, sp, #0x3, lsl #12
        ldr     x8, [x8]
        add     x24, x24, #0xc60
        str     x8, [sp, #15544]
        mov     w8, #0x4
        ldp     q0, q1, [x2]
        mov     w2, #0x21
        strb    w8, [x9, #32]
        str     q0, [sp, #15392]
        str     q1, [sp, #15408]
        bl      L4c48
        add     x28, sp, #0x1, lsl #12
        add     x0, sp, #0x1, lsl #12
        add     x28, x28, #0xc20
        add     x4, sp, #0x1, lsl #12
        ldr     q0, [sp, #15456]
        mov     w8, #0x1
        ldr     q1, [sp, #15472]
        mov     w9, #0x2
        mov     w26, #0x3
        add     x1, x28, #0x200
        add     x2, x28, #0x400
        add     x3, x28, #0x600
        add     x0, x0, #0xc20
        add     x4, x4, #0x420
        add     x27, sp, #0x1, lsl #12
        str     q0, [sp, #5152]
        str     q1, [sp, #5168]
        add     x27, x27, #0x420
        str     q0, [sp, #5216]
        str     q1, [sp, #5232]
        str     q0, [sp, #5280]
        str     q1, [sp, #5296]
        str     q1, [sp, #5360]
        str     q0, [sp, #5344]
        strh    w8, [sp, #5248]
        strh    w9, [sp, #5312]
        strh    wzr, [sp, #5184]
        strh    w26, [sp, #5376]
        bl      L8750
        add     x21, x28, #0x800
        add     x4, sp, #0x1, lsl #12
        mov     w8, #0x100
        mov     w9, #0x101
        mov     w10, #0x102
        mov     w11, #0x103
        add     x1, x28, #0xa00
        add     x2, x28, #0xc00
        add     x3, x28, #0xe00
        add     x4, x4, #0x420
        mov     x0, x21
        strh    w8, [sp, #5184]
        strh    w9, [sp, #5248]
        strh    w10, [sp, #5312]
        strh    w11, [sp, #5376]
        bl      L8750
        mov     w8, #0x200
        mov     w9, #0x201
        add     x22, x28, #0x1, lsl #12
        mov     w12, #0x1200
        add     x4, sp, #0x1, lsl #12
        mov     w10, #0x202
        strh    w8, [sp, #5184]
        mov     w8, #0x1400
        strh    w9, [sp, #5248]
        mov     w9, #0x1600
        mov     w11, #0x203
        add     x1, x28, x12
        add     x2, x28, x8
        add     x3, x28, x9
        add     x4, x4, #0x420
        mov     x0, x22
        strh    w10, [sp, #5312]
        strh    w11, [sp, #5376]
        bl      L8750
        mov     w8, #0x300
        mov     w9, #0x301
        mov     w12, #0x1800
        add     x4, sp, #0x1, lsl #12
        add     x23, x28, x12
        mov     w10, #0x302
        strh    w8, [sp, #5184]
        mov     w8, #0x1a00
        strh    w9, [sp, #5248]
        add     x1, x28, x8
        mov     w8, #0x1c00
        mov     w9, #0x1e00
        mov     w11, #0x303
        add     x2, x28, x8
        add     x3, x28, x9
        add     x4, x4, #0x420
        mov     x0, x23
        strh    w10, [sp, #5312]
        strh    w11, [sp, #5376]
        bl      L8750
        movi    v0.2d, #0x0
        add     x24, x24, #0x20
        add     x25, sp, #0x420
        add     x0, sp, #0x420
        add     x1, x25, #0x200
        add     x2, x25, #0x400
        add     x3, x25, #0x600
        mov     x4, x24
        str     q0, [sp, #5392]
        mov     w5, wzr
        str     q0, [sp, #5376]
        mov     w6, #0x1
        str     q0, [sp, #5360]
        mov     w7, #0x2
        str     q0, [sp, #5344]
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
        strb    w26, [sp]
        bl      L23f0
        add     x0, sp, #0x1, lsl #12
        add     x1, x27, #0x200
        add     x2, x27, #0x400
        add     x3, x27, #0x600
        mov     w8, #0x7
        add     x0, x0, #0x420
        mov     x4, x24
        mov     w5, #0x4
        mov     w6, #0x5
        mov     w7, #0x6
        strb    w8, [sp]
        bl      L23f0
        add     x0, sp, #0x420
        bl      L2074
        add     x0, sp, #0x1, lsl #12
        add     x0, x0, #0x420
        bl      L2074
        add     x0, sp, #0x20
        add     x1, sp, #0x420
        add     x26, sp, #0x20
        bl      L2320
        add     x1, sp, #0x1, lsl #12
        add     x0, sp, #0xc20
        add     x1, x1, #0xc20
        add     x2, sp, #0x420
        add     x3, sp, #0x20
        add     x24, sp, #0xc20
        bl      L20c4
        add     x0, x24, #0x200
        add     x2, sp, #0x420
        add     x3, sp, #0x20
        mov     x1, x21
        bl      L20c4
        add     x0, x24, #0x400
        add     x2, sp, #0x420
        add     x3, sp, #0x20
        mov     x1, x22
        bl      L20c4
        add     x0, x24, #0x600
        add     x2, sp, #0x420
        add     x3, sp, #0x20
        mov     x1, x23
        bl      L20c4
        add     x0, sp, #0xc20
        bl      L23c8
        add     x1, sp, #0x1, lsl #12
        add     x0, sp, #0xc20
        add     x1, x1, #0x420
        bl      L2388
        add     x0, sp, #0xc20
        bl      L2360
        add     x0, sp, #0x420
        bl      L2360
        add     x1, sp, #0x420
        mov     x0, x20
        bl      L1ff4
        add     x1, sp, #0xc20
        mov     x0, x19
        bl      L1ff4
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
        add     x8, sp, #0x3, lsl #12
        add     x8, x8, #0xc20
        movi    v0.2d, #0x0
        strb    wzr, [x8, #32]
        add     x8, sp, #0x3, lsl #12
        add     x8, x8, #0xc20
        str     q0, [sp, #15408]
        str     q0, [sp, #15392]
        add     x8, sp, #0x3, lsl #12
        str     q0, [sp, #15504]
        add     x8, x8, #0xc60
        str     q0, [sp, #15488]
        str     q0, [sp, #15472]
        str     q0, [sp, #15456]
        .inst   0xf00000e8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #15544]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L0e74
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L0e74:
        bl      L0830

// mlkem1024_indcpa_enc (0x5e4 bytes)
L0e78:
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
        .inst   0xf00000e8  // adrp x8, 0x1f000
        mov     x19, x0
        add     x0, sp, #0x1, lsl #12
        mov     x22, x1
        add     x0, x0, #0xa20
        mov     x1, x2
        ldr     x8, [x8, #4088]
        add     x24, sp, #0x2, lsl #12
        mov     x20, x3
        mov     x21, x2
        add     x24, x24, #0x220
        ldr     x8, [x8]
        str     x8, [sp, #19032]
        bl      L2034
        ldr     q0, [x21, #1536]
        add     x0, sp, #0x620
        ldr     q1, [x21, #1552]
        mov     x1, x22
        str     q0, [sp, #18976]
        str     q1, [sp, #18992]
        bl      L413c
        add     x25, sp, #0x2, lsl #12
        add     x0, sp, #0x2, lsl #12
        add     x25, x25, #0xa20
        add     x4, sp, #0x2, lsl #12
        ldr     q0, [sp, #18976]
        mov     w8, #0x100
        ldr     q1, [sp, #18992]
        mov     w9, #0x200
        mov     w10, #0x300
        add     x1, x25, #0x200
        add     x2, x25, #0x400
        add     x3, x25, #0x600
        add     x0, x0, #0xa20
        add     x4, x4, #0x220
        add     x26, sp, #0x2, lsl #12
        str     q0, [sp, #8736]
        str     q1, [sp, #8752]
        add     x26, x26, #0x220
        str     q0, [sp, #8800]
        str     q1, [sp, #8816]
        str     q0, [sp, #8864]
        str     q1, [sp, #8880]
        strh    w8, [x24, #96]
        strh    w9, [x24, #160]
        strh    w10, [x24, #224]
        str     q1, [sp, #8944]
        str     q0, [sp, #8928]
        strh    wzr, [x24, #32]
        bl      L8750
        add     x21, x25, #0x800
        add     x4, sp, #0x2, lsl #12
        mov     w8, #0x1
        mov     w9, #0x101
        mov     w10, #0x201
        mov     w11, #0x301
        add     x1, x25, #0xa00
        add     x2, x25, #0xc00
        add     x3, x25, #0xe00
        add     x4, x4, #0x220
        mov     x0, x21
        strh    w8, [x24, #32]
        strh    w9, [x24, #96]
        strh    w10, [x24, #160]
        strh    w11, [x24, #224]
        bl      L8750
        mov     w8, #0x2
        mov     w9, #0x102
        add     x22, x25, #0x1, lsl #12
        mov     w12, #0x1200
        add     x4, sp, #0x2, lsl #12
        mov     w10, #0x202
        strh    w8, [x24, #32]
        mov     w8, #0x1400
        strh    w9, [x24, #96]
        mov     w9, #0x1600
        mov     w11, #0x302
        add     x1, x25, x12
        add     x2, x25, x8
        add     x3, x25, x9
        add     x4, x4, #0x220
        mov     x0, x22
        strh    w10, [x24, #160]
        strh    w11, [x24, #224]
        bl      L8750
        mov     w8, #0x103
        mov     w9, #0x203
        mov     w11, #0x1800
        add     x4, sp, #0x2, lsl #12
        add     x23, x25, x11
        mov     w27, #0x3
        strh    w8, [x24, #96]
        mov     w8, #0x1a00
        strh    w9, [x24, #160]
        add     x1, x25, x8
        mov     w8, #0x1c00
        mov     w9, #0x1e00
        mov     w10, #0x303
        add     x2, x25, x8
        add     x3, x25, x9
        add     x4, x4, #0x220
        mov     x0, x23
        strh    w27, [x24, #32]
        strh    w10, [x24, #224]
        bl      L8750
        movi    v0.2d, #0x0
        add     x0, sp, #0x2, lsl #12
        add     x1, x26, #0x200
        add     x2, x26, #0x400
        add     x3, x26, #0x600
        add     x0, x0, #0x220
        mov     x4, x20
        mov     w5, wzr
        str     q0, [sp, #8976]
        mov     w6, #0x1
        str     q0, [sp, #8960]
        mov     w7, #0x2
        str     q0, [sp, #8944]
        str     q0, [sp, #8928]
        str     q0, [sp, #8912]
        str     q0, [sp, #8896]
        str     q0, [sp, #8880]
        str     q0, [sp, #8864]
        str     q0, [sp, #8848]
        str     q0, [sp, #8832]
        str     q0, [sp, #8816]
        str     q0, [sp, #8800]
        str     q0, [sp, #8784]
        str     q0, [sp, #8768]
        str     q0, [sp, #8752]
        str     q0, [sp, #8736]
        strb    w27, [sp]
        bl      L23f0
        add     x28, sp, #0x1, lsl #12
        add     x0, sp, #0x1, lsl #12
        add     x28, x28, #0x220
        mov     w8, #0x7
        add     x1, x28, #0x200
        add     x2, x28, #0x400
        add     x3, x28, #0x600
        add     x0, x0, #0x220
        mov     x4, x20
        mov     w5, #0x4
        mov     w6, #0x5
        mov     w7, #0x6
        strb    w8, [sp]
        bl      L23f0
        add     x0, sp, #0x420
        mov     x1, x20
        mov     w2, #0x8
        add     x24, sp, #0x420
        bl      L2580
        add     x0, sp, #0x2, lsl #12
        add     x0, x0, #0x220
        bl      L2074
        add     x1, sp, #0x2, lsl #12
        add     x0, sp, #0x20
        add     x1, x1, #0x220
        add     x27, sp, #0x20
        bl      L2320
        add     x1, sp, #0x2, lsl #12
        add     x2, sp, #0x2, lsl #12
        add     x0, sp, #0xa20
        add     x1, x1, #0xa20
        add     x2, x2, #0x220
        add     x3, sp, #0x20
        add     x20, sp, #0xa20
        bl      L20c4
        add     x2, sp, #0x2, lsl #12
        add     x0, x20, #0x200
        add     x2, x2, #0x220
        add     x3, sp, #0x20
        mov     x1, x21
        bl      L20c4
        add     x2, sp, #0x2, lsl #12
        add     x0, x20, #0x400
        add     x2, x2, #0x220
        add     x3, sp, #0x20
        mov     x1, x22
        bl      L20c4
        add     x2, sp, #0x2, lsl #12
        add     x0, x20, #0x600
        add     x2, x2, #0x220
        add     x3, sp, #0x20
        mov     x1, x23
        bl      L20c4
        add     x1, sp, #0x1, lsl #12
        add     x2, sp, #0x2, lsl #12
        add     x0, sp, #0x820
        add     x1, x1, #0xa20
        add     x2, x2, #0x220
        add     x3, sp, #0x20
        add     x21, sp, #0x820
        bl      L20c4
        add     x0, sp, #0xa20
        bl      L209c
        add     x0, sp, #0x820
        bl      L7e1c
        add     x1, sp, #0x1, lsl #12
        add     x0, sp, #0xa20
        add     x1, x1, #0x220
        bl      L2388
        add     x0, sp, #0x820
        add     x1, sp, #0x420
        bl      L7384
        add     x0, sp, #0x820
        add     x1, sp, #0x620
        bl      L7384
        add     x0, sp, #0xa20
        bl      L2360
        add     x0, sp, #0x820
        bl      L7334
        add     x1, sp, #0xa20
        mov     x0, x19
        bl      L1f74
        add     x0, x19, #0x580
        add     x1, sp, #0x820
        bl      L3258
        add     x0, sp, #0x20
        mov     w1, wzr
        mov     w2, #0x400
        bl      L0840
        movi    v0.2d, #0x0
        add     x8, sp, #0x620
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
        add     x8, sp, #0x1, lsl #12
        add     x0, sp, #0x2, lsl #12
        add     x8, x8, #0xa20
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
        .inst   0xd00000e8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #19032]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L1458
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L1458:
        bl      L0830

// mlkem1024_indcpa_dec (0x234 bytes)
L145c:
        stp     x29, x30, [sp, #-80]!
        str     x28, [sp, #16]
        stp     x24, x23, [sp, #32]
        stp     x22, x21, [sp, #48]
        stp     x20, x19, [sp, #64]
        mov     x29, sp
        sub     x9, sp, #0x1, lsl #12
        sub     x9, x9, #0x810
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd00000e8  // adrp x8, 0x1f000
        mov     x21, x0
        add     x0, sp, #0x1, lsl #12
        mov     x19, x2
        mov     x20, x1
        add     x22, sp, #0x1, lsl #12
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #6152]
        bl      L1fb4
        add     x1, x20, #0x580
        add     x0, sp, #0x600
        add     x20, sp, #0x600
        bl      L342c
        add     x0, sp, #0x800
        mov     x1, x19
        add     x19, sp, #0x800
        bl      L2034
        add     x0, sp, #0x1, lsl #12
        bl      L2074
        mov     x0, sp
        add     x1, sp, #0x1, lsl #12
        mov     x24, sp
        bl      L2320
        add     x0, sp, #0x400
        add     x1, sp, #0x800
        add     x2, sp, #0x1, lsl #12
        mov     x3, sp
        add     x23, sp, #0x400
        bl      L20c4
        add     x0, sp, #0x400
        bl      L7e1c
        add     x0, sp, #0x600
        add     x1, sp, #0x400
        bl      L7504
        add     x0, sp, #0x600
        bl      L7334
        add     x1, sp, #0x600
        mov     x0, x21
        bl      L421c
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
        .inst   0xd00000e8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #6152]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L168c
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #64]
        ldp     x22, x21, [sp, #48]
        ldp     x24, x23, [sp, #32]
        ldr     x28, [sp, #16]
        ldp     x29, x30, [sp], #80
        ret
L168c:
        bl      L0830

// mlkem1024_check_pk (0x150 bytes)
L1690:
        stp     x29, x30, [sp, #-48]!
        stp     x28, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0xe10
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd00000e8  // adrp x8, 0x1f000
        mov     x19, x0
        add     x0, sp, #0x600
        mov     x1, x19
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #3592]
        bl      L2034
        add     x0, sp, #0x600
        bl      L2360
        mov     x0, sp
        add     x1, sp, #0x600
        mov     x20, sp
        bl      L1ff4
        movi    v0.2d, #0x0
        mov     x8, xzr
        movi    v1.2d, #0x0
        movi    v2.2d, #0x0
        movi    v3.2d, #0x0
L16f4:
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
        b.ne    L16f4
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
        .inst   0xd00000e8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #3592]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L17dc
        mov     w0, w19
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldp     x28, x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L17dc:
        bl      L0830

// mlkem1024_check_sk (0xe0 bytes)
L17e0:
        stp     x29, x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x29, sp
        sub     x9, sp, #0x40
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd00000e8  // adrp x8, 0x1f000
        mov     x19, x0
        add     x1, x0, #0x600
        mov     x0, sp
        mov     w2, #0x620
        mov     x20, sp
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #56]
        bl      L4ba4
        ldp     q2, q3, [sp]
        mov     w8, wzr
        ldr     q0, [x19, #3104]
        ldr     q1, [x19, #3120]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v3.16b, v1.16b
        orr     v2.16b, v1.16b, v0.16b
        ext     v3.16b, v2.16b, v2.16b, #8
        eor     v0.16b, v1.16b, v0.16b
        orr     v1.8b, v2.8b, v3.8b
        ext     v2.16b, v0.16b, v0.16b, #8
        fmov    x9, d1
        orr     x9, x9, x9, lsr #32
        eor     v0.8b, v0.8b, v2.8b
        lsr     x10, x9, #16
        fmov    x11, d0
        orr     w9, w9, w10
        movi    v0.2d, #0x0
        orr     w9, w9, w9, lsr #8
        eor     x10, x11, x11, lsr #32
        sub     w9, w8, w9, uxtb
        eor     x10, x10, x10, lsr #16
        lsr     x11, x10, #8
        eor     w10, w10, w11
        .inst   0xd00000eb  // adrp x11, 0x1f000
        eor     w9, w10, w9, lsr #16
        stp     q0, q0, [sp]
        and     w9, w9, #0xff
        ldr     x11, [x11, #4088]
        cmp     w9, w10, uxtb
        ldr     x12, [sp, #56]
        mov     w9, #0xfffffffb
        csel    w0, w8, w9, eq
        ldr     x11, [x11]
        cmp     x11, x12
        b.ne    L18bc
        mov     sp, x29
        ldp     x20, x19, [sp, #16]
        ldp     x29, x30, [sp], #32
        ret
L18bc:
        bl      L0830

// mlkem1024_keypair_derand (0x88 bytes)
L18c0:
        str     x30, [sp, #-48]!
        stp     x22, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x22, x2
        mov     x19, x1
        mov     x21, x0
        bl      L0a6c
        mov     w20, w0
        cbz     w0, L1908
        mov     x0, x21
        mov     w1, wzr
        mov     w2, #0x620
        bl      L0840
        mov     x0, x19
        mov     w1, wzr
        mov     w2, #0xc60
        bl      L0840
        b       L1934
L1908:
        add     x0, x19, #0x600
        mov     x1, x21
        mov     w2, #0x620
        bl      L0810
        add     x0, x19, #0xc20
        mov     x1, x21
        mov     w2, #0x620
        bl      L4ba4
        ldp     q1, q0, [x22, #32]
        str     q1, [x19, #3136]
        str     q0, [x19, #3152]
L1934:
        mov     w0, w20
        ldp     x20, x19, [sp, #32]
        ldp     x22, x21, [sp, #16]
        ldr     x30, [sp], #48
        ret

// mlkem1024_keypair (0xf4 bytes)
L1948:
        stp     x29, x30, [sp, #-48]!
        str     x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0x50
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd00000e8  // adrp x8, 0x1f000
        mov     x19, x1
        mov     x21, x0
        mov     x0, sp
        mov     w1, #0x40
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #72]
        bl      L0820
        cbz     w0, L1990
        mov     w20, #0xfffffffd
        b       L19f8
L1990:
        mov     x2, sp
        mov     x0, x21
        mov     x1, x19
        bl      L0a6c
        mov     w20, w0
        cbz     w0, L19cc
        mov     x0, x21
        mov     w1, wzr
        mov     w2, #0x620
        bl      L0840
        mov     x0, x19
        mov     w1, wzr
        mov     w2, #0xc60
        bl      L0840
        b       L19f8
L19cc:
        add     x0, x19, #0x600
        mov     x1, x21
        mov     w2, #0x620
        bl      L0810
        add     x0, x19, #0xc20
        mov     x1, x21
        mov     w2, #0x620
        bl      L4ba4
        ldp     q0, q1, [sp, #32]
        str     q0, [x19, #3136]
        str     q1, [x19, #3152]
L19f8:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        .inst   0xd00000e8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #72]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L1a38
        mov     w0, w20
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldr     x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L1a38:
        bl      L0830

// mlkem1024_enc_derand (0x1e4 bytes)
L1a3c:
        stp     x29, x30, [sp, #-96]!
        str     x28, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0xe20
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd00000e8  // adrp x8, 0x1f000
        mov     x19, x1
        mov     x21, x0
        add     x0, sp, #0x600
        mov     x1, x2
        mov     x22, x3
        ldr     x8, [x8, #4088]
        mov     x20, x2
        ldr     x8, [x8]
        str     x8, [sp, #3608]
        bl      L2034
        add     x0, sp, #0x600
        bl      L2360
        mov     x0, sp
        add     x1, sp, #0x600
        mov     x23, sp
        bl      L1ff4
        movi    v0.2d, #0x0
        mov     x8, xzr
        movi    v1.2d, #0x0
        movi    v2.2d, #0x0
        movi    v3.2d, #0x0
L1ab8:
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
        b.ne    L1ab8
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
        b.ne    L1bbc
        ldp     q0, q1, [x22]
        add     x0, x23, #0x20
        mov     x1, x20
        mov     w2, #0x620
        str     q0, [sp, #1536]
        str     q1, [sp, #1552]
        bl      L4ba4
        mov     x0, sp
        add     x1, sp, #0x600
        mov     w2, #0x40
        bl      L4c48
        add     x3, x24, #0x20
        add     x1, sp, #0x600
        mov     x0, x21
        mov     x2, x20
        bl      L0e78
        cbnz    w0, L1bc0
        ldp     q0, q1, [sp]
        stp     q0, q1, [x19]
        b       L1bc0
L1bbc:
        mov     w0, #0xfffffffc
L1bc0:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        str     q0, [sp, #1584]
        add     x8, sp, #0x600
        str     q0, [sp, #1568]
        str     q0, [sp, #1552]
        str     q0, [sp, #1536]
        .inst   0xd00000e8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #3608]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L1c1c
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldr     x28, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L1c1c:
        bl      L0830

// mlkem1024_enc (0x9c bytes)
L1c20:
        stp     x29, x30, [sp, #-48]!
        str     x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0x30
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd00000e8  // adrp x8, 0x1f000
        mov     x20, x1
        mov     x21, x0
        mov     x0, sp
        mov     w1, #0x20
        mov     x19, x2
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #40]
        bl      L0820
        cbz     w0, L1c6c
        mov     w0, #0xfffffffd
        b       L1c80
L1c6c:
        mov     x3, sp
        mov     x0, x21
        mov     x1, x20
        mov     x2, x19
        bl      L1a3c
L1c80:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        .inst   0xd00000e8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #40]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L1cb8
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldr     x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L1cb8:
        bl      L0830

// mlkem1024_dec (0x2b8 bytes)
L1cbc:
        stp     x29, x30, [sp, #-64]!
        stp     x28, x23, [sp, #16]
        stp     x22, x21, [sp, #32]
        stp     x20, x19, [sp, #48]
        mov     x29, sp
        sub     x9, sp, #0x6e0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd00000e8  // adrp x8, 0x1f000
        add     x22, x2, #0x600
        mov     x21, x2
        mov     x20, x1
        mov     x19, x0
        mov     x0, sp
        ldr     x8, [x8, #4088]
        mov     x1, x22
        mov     w2, #0x620
        mov     x23, sp
        ldr     x8, [x8]
        str     x8, [sp, #1752]
        bl      L4ba4
        ldp     q2, q3, [sp]
        mov     w8, wzr
        ldr     q0, [x21, #3104]
        ldr     q1, [x21, #3120]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v3.16b, v1.16b
        orr     v2.16b, v1.16b, v0.16b
        ext     v3.16b, v2.16b, v2.16b, #8
        eor     v0.16b, v1.16b, v0.16b
        orr     v1.8b, v2.8b, v3.8b
        ext     v2.16b, v0.16b, v0.16b, #8
        fmov    x9, d1
        orr     x9, x9, x9, lsr #32
        eor     v0.8b, v0.8b, v2.8b
        lsr     x10, x9, #16
        orr     w9, w9, w10
        fmov    x10, d0
        movi    v0.2d, #0x0
        orr     w9, w9, w9, lsr #8
        eor     x10, x10, x10, lsr #32
        sub     w8, w8, w9, uxtb
        eor     x9, x10, x10, lsr #16
        lsr     x10, x9, #8
        eor     w9, w9, w10
        eor     w8, w9, w8, lsr #16
        stp     q0, q0, [sp]
        and     w8, w8, #0xff
        cmp     w8, w9, uxtb
        b.ne    L1ef8
        add     x0, sp, #0x680
        mov     x1, x20
        mov     x2, x21
        bl      L145c
        mov     w23, w0
        cbnz    w0, L1efc
        add     x8, x21, #0xc20
        add     x0, sp, #0x640
        add     x1, sp, #0x680
        mov     w2, #0x40
        add     x23, sp, #0x640
        ldp     q0, q1, [x8]
        str     q0, [sp, #1696]
        str     q1, [sp, #1712]
        bl      L4c48
        add     x3, x23, #0x20
        mov     x0, sp
        add     x1, sp, #0x680
        mov     x2, x22
        mov     x22, sp
        bl      L0e78
        mov     w23, w0
        cbnz    w0, L1efc
        movi    v0.2d, #0x0
        mov     x8, xzr
        movi    v1.2d, #0x0
        movi    v2.2d, #0x0
        movi    v3.2d, #0x0
L1df0:
        add     x9, x20, x8
        add     x10, x22, x8
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
        b.ne    L1df0
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
        add     x0, sp, #0x680
        mov     x2, sp
        mov     w1, #0x20
        mov     w3, #0x640
        add     x20, sp, #0x680
        bl      L4ad0
        mov     x8, xzr
        sub     w9, w22, w21, uxtb
        add     x10, sp, #0x640
L1eb8:
        ldrb    w11, [x20, x8]
        mov     w12, w9
        ldrb    w13, [x10, x8]
        lsr     w12, w12, #16
        and     w11, w11, w12
        bic     w13, w13, w12
        orr     w11, w11, w13
        strb    w11, [x20, x8]
        add     x8, x8, #0x1
        cmp     x8, #0x20
        b.ne    L1eb8
        mov     w23, wzr
        ldr     q0, [sp, #1664]
        ldr     q1, [sp, #1680]
        stp     q0, q1, [x19]
        b       L1efc
L1ef8:
        mov     w23, #0xfffffffb
L1efc:
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
        .inst   0xd00000e8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #1752]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L1f70
        mov     w0, w23
        mov     sp, x29
        ldp     x20, x19, [sp, #48]
        ldp     x22, x21, [sp, #32]
        ldp     x28, x23, [sp, #16]
        ldp     x29, x30, [sp], #64
        ret
L1f70:
        bl      L0830

// mlkem1024_polyvec_compress_du (0x40 bytes)
L1f74:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L3324
        add     x0, x20, #0x160
        add     x1, x19, #0x200
        bl      L3324
        add     x0, x20, #0x2c0
        add     x1, x19, #0x400
        bl      L3324
        add     x0, x20, #0x420
        add     x1, x19, #0x600
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L3324

// mlkem1024_polyvec_decompress_du (0x40 bytes)
L1fb4:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L3af0
        add     x0, x20, #0x200
        add     x1, x19, #0x160
        bl      L3af0
        add     x0, x20, #0x400
        add     x1, x19, #0x2c0
        bl      L3af0
        add     x0, x20, #0x600
        add     x1, x19, #0x420
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L3af0

// mlkem1024_polyvec_tobytes (0x40 bytes)
L1ff4:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L3bfc
        add     x0, x20, #0x180
        add     x1, x19, #0x200
        bl      L3bfc
        add     x0, x20, #0x300
        add     x1, x19, #0x400
        bl      L3bfc
        add     x0, x20, #0x480
        add     x1, x19, #0x600
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L3bfc

// mlkem1024_polyvec_frombytes (0x40 bytes)
L2034:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L3e4c
        add     x0, x20, #0x200
        add     x1, x19, #0x180
        bl      L3e4c
        add     x0, x20, #0x400
        add     x1, x19, #0x300
        bl      L3e4c
        add     x0, x20, #0x600
        add     x1, x19, #0x480
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L3e4c

// mlkem1024_polyvec_ntt (0x28 bytes)
L2074:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L7c30
        add     x0, x19, #0x200
        bl      L7c30
        add     x0, x19, #0x400
        bl      L7c30
        add     x0, x19, #0x600
        ldp     x30, x19, [sp], #16
        b       L7c30

// mlkem1024_polyvec_invntt_tomont (0x28 bytes)
L209c:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L7e1c
        add     x0, x19, #0x200
        bl      L7e1c
        add     x0, x19, #0x400
        bl      L7e1c
        add     x0, x19, #0x600
        ldp     x30, x19, [sp], #16
        b       L7e1c

// mlkem1024_polyvec_basemul_acc_montgomery_cached (0x25c bytes)
L20c4:
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
        b.hi    L223c
        tbnz    w8, #0, L223c
        cbnz    w9, L223c
        mov     w9, #0xf3010000
        mov     x8, xzr
        mvni    v1.4s, #0xd, lsl #8
        dup     v0.4s, w9
L2110:
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
        b.ne    L2110
        b       L231c
L223c:
        mov     x8, xzr
        mov     w9, #0xf3010000
        mov     w10, #0xfffff2ff
L2248:
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
        b.ne    L2248
L231c:
        ret

// mlkem1024_polyvec_mulcache_compute (0x40 bytes)
L2320:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L7684
        add     x0, x20, #0x100
        add     x1, x19, #0x200
        bl      L7684
        add     x0, x20, #0x200
        add     x1, x19, #0x400
        bl      L7684
        add     x0, x20, #0x300
        add     x1, x19, #0x600
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L7684

// mlkem1024_polyvec_reduce (0x28 bytes)
L2360:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L7334
        add     x0, x19, #0x200
        bl      L7334
        add     x0, x19, #0x400
        bl      L7334
        add     x0, x19, #0x600
        ldp     x30, x19, [sp], #16
        b       L7334

// mlkem1024_polyvec_add (0x40 bytes)
L2388:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L7384
        add     x0, x20, #0x200
        add     x1, x19, #0x200
        bl      L7384
        add     x0, x20, #0x400
        add     x1, x19, #0x400
        bl      L7384
        add     x0, x20, #0x600
        add     x1, x19, #0x600
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L7384

// mlkem1024_polyvec_tomont (0x28 bytes)
L23c8:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L72a0
        add     x0, x19, #0x200
        bl      L72a0
        add     x0, x19, #0x400
        bl      L72a0
        add     x0, x19, #0x600
        ldp     x30, x19, [sp], #16
        b       L72a0

// mlkem1024_poly_getnoise_eta1_4x (0x190 bytes)
L23f0:
        stp     x29, x30, [sp, #-80]!
        stp     x28, x25, [sp, #16]
        stp     x24, x23, [sp, #32]
        stp     x22, x21, [sp, #48]
        stp     x20, x19, [sp, #64]
        mov     x29, sp
        sub     x9, sp, #0x330
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb00000e8  // adrp x8, 0x1f000
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
        str     q0, [sp, #96]
        str     q1, [sp, #112]
        stp     q0, q1, [sp, #160]
        stp     q0, q1, [sp, #224]
        stp     x11, x10, [sp]
        bl      L4f50
        add     x1, sp, #0x120
        mov     x0, x23
        bl      L8e64
        mov     x0, x22
        mov     x1, x24
        bl      L8e64
        mov     x0, x21
        mov     x1, x25
        bl      L8e64
        cbz     x19, L24dc
        mov     x0, x19
        mov     x1, x20
        bl      L8e64
L24dc:
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
        .inst   0xb00000e8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #808]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L257c
        mov     sp, x29
        ldp     x20, x19, [sp, #64]
        ldp     x22, x21, [sp, #48]
        ldp     x24, x23, [sp, #32]
        ldp     x28, x25, [sp, #16]
        ldp     x29, x30, [sp], #80
        ret
L257c:
        bl      L0830

// mlkem1024_poly_getnoise_eta2 (0xac bytes)
L2580:
        stp     x29, x30, [sp, #-48]!
        stp     x28, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0xd0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb00000e8  // adrp x8, 0x1f000
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
        bl      L4ad0
        add     x1, sp, #0x40
        mov     x0, x19
        bl      L8e64
        movi    v0.2d, #0x0
        .inst   0xb00000e8  // adrp x8, 0x1f000
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
        b.ne    L2628
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldp     x28, x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L2628:
        bl      L0830

// mlkem_poly_compress_d4 (0x5b0 bytes)
L262c:
        sub     sp, sp, #0x140
        stp     d15, d14, [sp, #240]
        stp     d13, d12, [sp, #256]
        stp     d11, d10, [sp, #272]
        stp     d9, d8, [sp, #288]
        str     x29, [sp, #304]
        add     x8, x1, #0x200
        cmp     x8, x0
        b.ls    L26f8
        add     x8, x0, #0x80
        cmp     x8, x1
        b.ls    L26f8
        mov     w10, #0xafb0
        mov     x8, xzr
        movk    w10, #0x13, lsl #16
        add     x9, x1, #0x8
        dup     v0.4s, w10
L2670:
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
        b.ne    L2670
        b       L2bc0
L26f8:
        .inst   0x90000049  // adrp x9, 0xa000
        .inst   0x9000004a  // adrp x10, 0xa000
        .inst   0x9000004b  // adrp x11, 0xa000
        mov     x8, xzr
        ldr     q0, [x9, #3200]
        .inst   0x90000049  // adrp x9, 0xa000
        str     q0, [sp, #96]
        ldr     q0, [x10, #3216]
        .inst   0x9000004a  // adrp x10, 0xa000
        str     q0, [sp, #80]
        ldr     q0, [x11, #3232]
        .inst   0x9000004b  // adrp x11, 0xa000
        str     q0, [sp, #64]
        ldr     q0, [x9, #3248]
        .inst   0x90000049  // adrp x9, 0xa000
        str     q0, [sp, #48]
        ldr     q0, [x10, #3264]
        mov     w10, #0xafb0
        movk    w10, #0x13, lsl #16
        str     q0, [sp, #32]
        ldr     q0, [x11, #3280]
        dup     v16.4s, w10
        str     q0, [sp, #16]
        ldr     q0, [x9, #3296]
        str     q0, [sp]
L275c:
        ldp     q21, q22, [x1, #32]
        add     x9, sp, #0x70
        movi    v7.4s, #0x8, lsl #24
        movi    v15.4s, #0x8, lsl #24
        ldp     q23, q24, [x1]
        zip1    v18.4h, v21.4h, v22.4h
        ext     v31.8b, v21.8b, v18.8b, #4
        ldp     q19, q20, [x1, #96]
        zip1    v6.4h, v23.4h, v24.4h
        trn2    v4.4h, v23.4h, v24.4h
        mov     v6.s[1], v31.s[1]
        ldp     q25, q26, [x1, #224]
        zip1    v3.4h, v19.4h, v20.4h
        mov     v4.s[1], v18.s[1]
        sxtl    v6.4s, v6.4h
        ext     v10.8b, v19.8b, v3.8b, #4
        ldp     q0, q1, [x1, #64]
        zip1    v31.4h, v25.4h, v26.4h
        mla     v15.4s, v6.4s, v16.4s
        sxtl    v4.4s, v4.4h
        ext     v13.8b, v25.8b, v31.8b, #4
        ldp     q29, q30, [x1, #160]
        zip1    v11.4h, v0.4h, v1.4h
        trn2    v5.4h, v0.4h, v1.4h
        st1     {v0.2d-v1.2d}, [x9]
        mov     v11.s[1], v10.s[1]
        ldp     q27, q28, [x1, #192]
        zip1    v17.4h, v29.4h, v30.4h
        mov     v5.s[1], v3.s[1]
        sxtl    v11.4s, v11.4h
        ext     v10.8b, v29.8b, v17.8b, #4
        ldp     q8, q9, [x1, #128]
        zip1    v14.4h, v27.4h, v28.4h
        add     x1, x1, #0x100
        mov     v14.s[1], v13.s[1]
        zip1    v12.4h, v8.4h, v9.4h
        movi    v13.4s, #0x8, lsl #24
        trn2    v18.4h, v8.4h, v9.4h
        sxtl    v1.4s, v14.4h
        mov     v12.s[1], v10.s[1]
        movi    v10.4s, #0x8, lsl #24
        mla     v7.4s, v1.4s, v16.4s
        mov     v18.s[1], v17.s[1]
        sxtl    v3.4s, v12.4h
        mla     v10.4s, v11.4s, v16.4s
        mla     v13.4s, v3.4s, v16.4s
        ushr    v3.4s, v7.4s, #28
        trn2    v12.4h, v27.4h, v28.4h
        movi    v7.4s, #0x8, lsl #24
        ushr    v2.4s, v13.4s, #28
        ushr    v1.4s, v10.4s, #28
        ushr    v0.4s, v15.4s, #28
        ldr     q15, [sp, #96]
        mov     v12.s[1], v31.s[1]
        zip2    v31.8h, v23.8h, v24.8h
        tbl     v6.16b, {v0.16b-v3.16b}, v15.16b
        movi    v3.4s, #0x8, lsl #24
        sxtl    v1.4s, v18.4h
        ld1     {v17.2d-v18.2d}, [x9]
        sxtl    v0.4s, v5.4h
        add     x9, x0, x8
        movi    v5.4s, #0x8, lsl #24
        add     x8, x8, #0x40
        mla     v3.4s, v4.4s, v16.4s
        cmp     x8, #0x80
        sxtl    v2.4s, v12.4h
        mla     v7.4s, v0.4s, v16.4s
        mov     v0.16b, v19.16b
        stp     q3, q6, [sp, #208]
        zip2    v4.4h, v23.4h, v24.4h
        movi    v6.4s, #0x8, lsl #24
        mov     v3.16b, v21.16b
        mov     v3.h[3], v22.h[2]
        mla     v5.4s, v1.4s, v16.4s
        mla     v6.4s, v2.4s, v16.4s
        mov     v0.h[3], v20.h[2]
        zip2    v2.4h, v17.4h, v18.4h
        mov     v1.16b, v29.16b
        stp     q6, q5, [sp, #176]
        zip2    v5.4h, v8.4h, v9.4h
        mov     v4.s[1], v3.s[1]
        zip2    v6.4h, v27.4h, v28.4h
        mov     v3.16b, v25.16b
        mov     v1.h[3], v30.h[2]
        mov     v2.s[1], v0.s[1]
        mov     v3.h[3], v26.h[2]
        sxtl    v0.4s, v4.4h
        mov     v5.s[1], v1.s[1]
        sxtl    v1.4s, v2.4h
        movi    v2.4s, #0x8, lsl #24
        mov     v6.s[1], v3.s[1]
        sxtl    v3.4s, v5.4h
        movi    v5.4s, #0x8, lsl #24
        mla     v2.4s, v0.4s, v16.4s
        movi    v0.4s, #0x8, lsl #24
        sxtl    v4.4s, v6.4h
        movi    v6.4s, #0x8, lsl #24
        mla     v5.4s, v1.4s, v16.4s
        mla     v0.4s, v4.4s, v16.4s
        uzp2    v1.4h, v23.4h, v24.4h
        mla     v6.4s, v3.4s, v16.4s
        zip2    v3.4h, v21.4h, v22.4h
        zip2    v4.4h, v29.4h, v30.4h
        ushr    v13.4s, v0.4s, #28
        uzp2    v0.4h, v17.4h, v18.4h
        uzp2    v1.4h, v1.4h, v23.4h
        ushr    v12.4s, v6.4s, #28
        ushr    v11.4s, v5.4s, #28
        ushr    v10.4s, v2.4s, #28
        uzp2    v6.4h, v0.4h, v17.4h
        mov     v1.s[1], v3.s[1]
        zip2    v2.4h, v19.4h, v20.4h
        tbl     v0.16b, {v10.16b-v13.16b}, v15.16b
        ldr     q10, [sp, #80]
        movi    v11.4s, #0x8, lsl #24
        sxtl    v3.4s, v1.4h
        uzp2    v1.4h, v27.4h, v28.4h
        str     q0, [sp, #160]
        uzp2    v0.4h, v8.4h, v9.4h
        mov     v6.s[1], v2.s[1]
        mla     v11.4s, v3.4s, v16.4s
        uzp2    v1.4h, v1.4h, v27.4h
        uzp2    v2.4h, v0.4h, v8.4h
        zip2    v0.4h, v25.4h, v26.4h
        tbl     v5.16b, {v21.16b-v22.16b}, v10.16b
        str     q11, [sp, #144]
        tbl     v3.16b, {v29.16b-v30.16b}, v10.16b
        mov     v1.s[1], v0.s[1]
        tbl     v0.16b, {v19.16b-v20.16b}, v10.16b
        tbl     v10.16b, {v25.16b-v26.16b}, v10.16b
        zip2    v11.8h, v27.8h, v28.8h
        mov     v2.s[1], v4.s[1]
        zip2    v4.8h, v8.8h, v9.8h
        mov     v31.s[1], v5.s[1]
        zip2    v5.8h, v17.8h, v18.8h
        mov     v11.s[1], v10.s[1]
        mov     v4.s[1], v3.s[1]
        sxtl    v3.4s, v31.4h
        movi    v31.4s, #0x8, lsl #24
        mov     v5.s[1], v0.s[1]
        movi    v0.4s, #0x8, lsl #24
        sxtl    v10.4s, v11.4h
        sxtl    v4.4s, v4.4h
        mla     v31.4s, v10.4s, v16.4s
        movi    v10.4s, #0x8, lsl #24
        mla     v0.4s, v4.4s, v16.4s
        movi    v4.4s, #0x8, lsl #24
        sxtl    v5.4s, v5.4h
        ushr    v14.4s, v31.4s, #28
        mla     v10.4s, v5.4s, v16.4s
        ushr    v13.4s, v0.4s, #28
        mla     v4.4s, v3.4s, v16.4s
        sxtl    v3.4s, v6.4h
        movi    v31.4s, #0x8, lsl #24
        ushr    v12.4s, v10.4s, #28
        ushr    v11.4s, v4.4s, #28
        movi    v0.4s, #0x8, lsl #24
        tbl     v6.16b, {v11.16b-v14.16b}, v15.16b
        ldp     q13, q12, [sp, #32]
        sxtl    v2.4s, v2.4h
        mla     v31.4s, v3.4s, v16.4s
        mla     v0.4s, v2.4s, v16.4s
        tbl     v3.16b, {v23.16b-v24.16b}, v13.16b
        tbl     v5.16b, {v17.16b-v18.16b}, v13.16b
        tbl     v2.16b, {v21.16b-v22.16b}, v12.16b
        tbl     v4.16b, {v19.16b-v20.16b}, v12.16b
        tbl     v10.16b, {v29.16b-v30.16b}, v12.16b
        tbl     v11.16b, {v8.16b-v9.16b}, v13.16b
        tbl     v12.16b, {v25.16b-v26.16b}, v12.16b
        tbl     v13.16b, {v27.16b-v28.16b}, v13.16b
        mov     v3.s[1], v2.s[1]
        mov     v5.s[1], v4.s[1]
        movi    v2.4s, #0x8, lsl #24
        movi    v4.4s, #0x8, lsl #24
        mov     v13.s[1], v12.s[1]
        sxtl    v3.4s, v3.4h
        mov     v11.s[1], v10.s[1]
        sxtl    v5.4s, v5.4h
        mla     v2.4s, v3.4s, v16.4s
        movi    v3.4s, #0x8, lsl #24
        mla     v4.4s, v5.4s, v16.4s
        movi    v5.4s, #0x8, lsl #24
        sxtl    v10.4s, v13.4h
        sxtl    v11.4s, v11.4h
        mla     v3.4s, v10.4s, v16.4s
        mla     v5.4s, v11.4s, v16.4s
        movi    v10.4s, #0x8, lsl #24
        sxtl    v1.4s, v1.4h
        ushr    v14.4s, v3.4s, #28
        ushr    v13.4s, v5.4s, #28
        ushr    v12.4s, v4.4s, #28
        ushr    v11.4s, v2.4s, #28
        mla     v10.4s, v1.4s, v16.4s
        tbl     v1.16b, {v11.16b-v14.16b}, v15.16b
        ldr     q14, [sp, #64]
        zip2    v2.8h, v21.8h, v22.8h
        zip2    v11.8h, v29.8h, v30.8h
        tbl     v4.16b, {v23.16b-v24.16b}, v14.16b
        tbl     v5.16b, {v17.16b-v18.16b}, v14.16b
        tbl     v12.16b, {v8.16b-v9.16b}, v14.16b
        zip2    v13.8h, v25.8h, v26.8h
        tbl     v14.16b, {v27.16b-v28.16b}, v14.16b
        mov     v4.s[1], v2.s[1]
        mov     v12.s[1], v11.s[1]
        movi    v2.4s, #0x8, lsl #24
        mov     v14.s[1], v13.s[1]
        ldp     q13, q11, [sp]
        zip2    v3.8h, v19.8h, v20.8h
        sxtl    v4.4s, v4.4h
        mla     v2.4s, v4.4s, v16.4s
        mov     v5.s[1], v3.s[1]
        tbl     v4.16b, {v21.16b-v22.16b}, v11.16b
        tbl     v21.16b, {v23.16b-v24.16b}, v13.16b
        movi    v3.4s, #0x8, lsl #24
        movi    v22.4s, #0x8, lsl #24
        sxtl    v5.4s, v5.4h
        mov     v21.s[1], v4.s[1]
        tbl     v4.16b, {v19.16b-v20.16b}, v11.16b
        tbl     v19.16b, {v17.16b-v18.16b}, v13.16b
        ldr     q17, [sp, #176]
        sxtl    v24.4s, v14.4h
        mla     v3.4s, v5.4s, v16.4s
        movi    v5.4s, #0x8, lsl #24
        mla     v22.4s, v24.4s, v16.4s
        tbl     v20.16b, {v29.16b-v30.16b}, v11.16b
        tbl     v24.16b, {v25.16b-v26.16b}, v11.16b
        tbl     v25.16b, {v27.16b-v28.16b}, v13.16b
        ushr    v29.4s, v17.4s, #24
        ldr     q17, [sp, #192]
        sxtl    v23.4s, v12.4h
        mov     v19.s[1], v4.s[1]
        ushr    v28.4s, v17.4s, #24
        mla     v5.4s, v23.4s, v16.4s
        ushr    v27.4s, v7.4s, #24
        tbl     v23.16b, {v8.16b-v9.16b}, v13.16b
        ldr     q7, [sp, #208]
        movi    v18.4s, #0x8, lsl #24
        mov     v25.s[1], v24.s[1]
        ushr    v26.4s, v7.4s, #24
        sxtl    v7.4s, v19.4h
        mov     v23.s[1], v20.s[1]
        movi    v19.4s, #0x8, lsl #24
        mla     v18.4s, v7.4s, v16.4s
        tbl     v7.16b, {v26.16b-v29.16b}, v15.16b
        ushr    v29.4s, v10.4s, #24
        ushr    v28.4s, v0.4s, #24
        movi    v0.4s, #0x8, lsl #24
        ushr    v27.4s, v31.4s, #24
        sxtl    v20.4s, v25.4h
        movi    v4.4s, #0x8, lsl #24
        sxtl    v17.4s, v23.4h
        mla     v19.4s, v20.4s, v16.4s
        ldr     q20, [sp, #144]
        sxtl    v21.4s, v21.4h
        mla     v0.4s, v17.4s, v16.4s
        ushr    v26.4s, v20.4s, #24
        mla     v4.4s, v21.4s, v16.4s
        ushr    v23.4s, v22.4s, #24
        tbl     v17.16b, {v26.16b-v29.16b}, v15.16b
        ushr    v27.4s, v19.4s, #24
        ushr    v26.4s, v0.4s, #24
        ushr    v22.4s, v5.4s, #24
        ushr    v25.4s, v18.4s, #24
        ushr    v21.4s, v3.4s, #24
        ushr    v24.4s, v4.4s, #24
        ushr    v20.4s, v2.4s, #24
        movi    v4.16b, #0xf0
        ldr     q5, [sp, #224]
        tbl     v0.16b, {v20.16b-v23.16b}, v15.16b
        tbl     v2.16b, {v24.16b-v27.16b}, v15.16b
        and     v3.16b, v7.16b, v4.16b
        orr     v18.16b, v3.16b, v5.16b
        ldr     q5, [sp, #160]
        and     v3.16b, v17.16b, v4.16b
        and     v0.16b, v0.16b, v4.16b
        orr     v19.16b, v3.16b, v5.16b
        orr     v20.16b, v0.16b, v6.16b
        and     v0.16b, v2.16b, v4.16b
        orr     v21.16b, v0.16b, v1.16b
        st4     {v18.16b-v21.16b}, [x9]
        b.ne    L275c
L2bc0:
        ldp     d9, d8, [sp, #288]
        ldp     d11, d10, [sp, #272]
        ldp     d13, d12, [sp, #256]
        ldp     d15, d14, [sp, #240]
        ldr     x29, [sp, #304]
        add     sp, sp, #0x140
        ret

// mlkem_poly_compress_d10 (0x9c bytes)
L2bdc:
        mov     w9, #0xbc00
        mov     x8, xzr
        movk    w9, #0x9d7d, lsl #16
        add     x10, x1, #0x6
        add     x11, x0, #0x2
        mov     x12, #0x100000000
L2bf4:
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
        b.ne    L2bf4
        ret

// mlkem_poly_decompress_d4 (0x3cc bytes)
L2c78:
        add     x8, x1, #0x80
        cmp     x8, x0
        b.ls    L2cd8
        add     x8, x0, #0x200
        cmp     x8, x1
        b.ls    L2cd8
        mov     x8, xzr
        add     x9, x0, #0x2
        mov     w10, #0xd01
        mov     w11, #0x8
L2ca0:
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
        b.ne    L2ca0
        ret
L2cd8:
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
L3044:
        add     x8, x1, #0x140
        cmp     x8, x0
        b.ls    L30e4
        add     x8, x0, #0x200
        cmp     x8, x1
        b.ls    L30e4
        mov     x8, xzr
        add     x9, x1, #0x2
        mov     w10, #0xd01
        mov     w11, #0x200
L306c:
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
        b.ne    L306c
        b       L3254
L30e4:
        .inst   0xf0000029  // adrp x9, 0xa000
        .inst   0xf000002a  // adrp x10, 0xa000
        .inst   0xf000002c  // adrp x12, 0xa000
        .inst   0xf000002b  // adrp x11, 0xa000
        movi    v5.4s, #0x3, lsl #8
        mov     x8, xzr
        ldr     q0, [x9, #3312]
        .inst   0xf0000029  // adrp x9, 0xa000
        ldr     q1, [x10, #3328]
        mov     w10, #0xd01
        ldr     q3, [x12, #3360]
        .inst   0xf000002c  // adrp x12, 0xa000
        ldr     q2, [x11, #3344]
        mov     w11, #0x3c0
        ldr     q4, [x9, #3376]
        mov     w9, #0x3f0
        dup     v6.4h, w10
        ldr     q16, [x12, #3392]
        dup     v7.4s, w11
        dup     v18.4s, w10
        dup     v17.4s, w9
L3138:
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
        b.ne    L3138
L3254:
        ret

// mlkem_poly_compress_d5 (0xcc bytes)
L3258:
        mov     w9, #0xafc0
        mov     x8, xzr
        movk    w9, #0x13, lsl #16
        add     x10, x1, #0x8
        add     x11, x0, #0x2
        mov     w12, #0x4000000
L3270:
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
        b.ne    L3270
        ret

// mlkem_poly_compress_d11 (0x108 bytes)
L3324:
        mov     x9, #0x7800
        mov     x8, xzr
        movk    x9, #0x3afb, lsl #16
        add     x10, x1, #0xe
        movk    x9, #0x1, lsl #32
        add     x11, x0, #0x5
        mov     x12, #0x100000000
L3340:
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
        b.ne    L3340
        ret

// mlkem_poly_decompress_d5 (0x6c4 bytes)
L342c:
        stp     d15, d14, [sp, #-80]!
        stp     d13, d12, [sp, #16]
        stp     d11, d10, [sp, #32]
        stp     d9, d8, [sp, #48]
        str     x29, [sp, #64]
        sub     sp, sp, #0x2c0
        add     x8, x1, #0xa0
        cmp     x8, x0
        b.ls    L355c
        add     x8, x0, #0x200
        cmp     x8, x1
        b.ls    L355c
        .inst   0x90000049  // adrp x9, 0xb000
        .inst   0x9000004a  // adrp x10, 0xb000
        mov     w11, #0xd01
        movi    d0, #0xff000000ff
        mov     x8, xzr
        ldr     d1, [x9, #416]
        add     x9, x1, #0x2
        ldr     d2, [x10, #424]
        dup     v3.8h, w11
L3480:
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
        b.ne    L3480
        b       L3ad4
L355c:
        .inst   0xf0000029  // adrp x9, 0xa000
        .inst   0xf000002a  // adrp x10, 0xa000
        .inst   0xf000002b  // adrp x11, 0xa000
        mov     x8, xzr
        ldr     q0, [x9, #3408]
        .inst   0xf0000029  // adrp x9, 0xa000
        str     q0, [sp, #400]
        ldr     q0, [x10, #3424]
        .inst   0xf000002a  // adrp x10, 0xa000
        str     q0, [sp, #384]
        ldr     q0, [x11, #3440]
        .inst   0xf000002b  // adrp x11, 0xa000
        str     q0, [sp, #368]
        ldr     q0, [x9, #3456]
        .inst   0xf0000029  // adrp x9, 0xa000
        str     q0, [sp, #352]
        ldr     q0, [x10, #3472]
        .inst   0xf000002a  // adrp x10, 0xa000
        str     q0, [sp, #336]
        ldr     q0, [x11, #3488]
        .inst   0xf000002b  // adrp x11, 0xa000
        str     q0, [sp, #320]
        ldr     q0, [x9, #3504]
        .inst   0xf0000029  // adrp x9, 0xa000
        str     q0, [sp, #304]
        ldr     q0, [x10, #3520]
        .inst   0xf000002a  // adrp x10, 0xa000
        str     q0, [sp, #288]
        ldr     q0, [x11, #3536]
        .inst   0xf000002b  // adrp x11, 0xa000
        str     q0, [sp, #272]
        ldr     q0, [x9, #3552]
        .inst   0xf0000029  // adrp x9, 0xa000
        str     q0, [sp, #256]
        ldr     q0, [x10, #3568]
        .inst   0xf000002a  // adrp x10, 0xa000
        str     q0, [sp, #240]
        ldr     q0, [x11, #3584]
        .inst   0xf000002b  // adrp x11, 0xa000
        str     q0, [sp, #224]
        ldr     q0, [x9, #3600]
        .inst   0xf0000029  // adrp x9, 0xa000
        str     q0, [sp, #208]
        ldr     q0, [x10, #3616]
        .inst   0xf000002a  // adrp x10, 0xa000
        str     q0, [sp, #192]
        ldr     q0, [x11, #3632]
        .inst   0xf000002b  // adrp x11, 0xa000
        str     q0, [sp, #176]
        ldr     q0, [x9, #3648]
        .inst   0xf0000029  // adrp x9, 0xa000
        str     q0, [sp, #160]
        ldr     q0, [x10, #3664]
        .inst   0xf000002a  // adrp x10, 0xa000
        str     q0, [sp, #144]
        ldr     q0, [x11, #3680]
        .inst   0xf000002b  // adrp x11, 0xa000
        str     q0, [sp, #128]
        ldr     q0, [x9, #3696]
        .inst   0xf0000029  // adrp x9, 0xa000
        str     q0, [sp, #112]
        ldr     q0, [x10, #3712]
        .inst   0xf000002a  // adrp x10, 0xa000
        str     q0, [sp, #96]
        ldr     q0, [x11, #3728]
        str     q0, [sp, #80]
        ldr     q0, [x9, #3744]
        .inst   0xf0000029  // adrp x9, 0xa000
        str     q0, [sp, #64]
        ldr     q0, [x10, #3760]
        .inst   0xf000002a  // adrp x10, 0xa000
        str     q0, [sp, #48]
        ldr     q0, [x9, #3776]
        .inst   0xf0000029  // adrp x9, 0xa000
        str     q0, [sp, #32]
        ldr     q0, [x10, #3792]
        .inst   0xf000002a  // adrp x10, 0xa000
        str     q0, [sp, #16]
        ldr     q0, [x9, #3808]
        .inst   0xf0000029  // adrp x9, 0xa000
        str     q0, [sp]
        ldr     q0, [x10, #3824]
        .inst   0xf000002a  // adrp x10, 0xa000
        str     q0, [sp, #688]
        ldr     q0, [x9, #3840]
        mov     w9, #0xd01
        str     q0, [sp, #672]
        ldr     q0, [x10, #3856]
        .inst   0xf000002a  // adrp x10, 0xa000
        dup     v13.8h, w9
        str     q0, [sp, #656]
        ldr     q0, [x10, #3872]
        str     q0, [sp, #640]
L36d0:
        add     x9, x1, x8
        ldr     q22, [sp, #368]
        ldp     q16, q6, [sp, #384]
        movi    v23.16b, #0x1f
        add     x8, x8, #0x50
        cmp     x8, #0xa0
        ldp     q5, q2, [x9, #16]
        ldp     q3, q1, [x9, #48]
        tbl     v7.16b, {v2.16b-v3.16b}, v6.16b
        ldr     q4, [x9]
        ldr     q18, [sp, #288]
        ldr     q20, [sp, #176]
        tbl     v6.16b, {v4.16b-v5.16b}, v16.16b
        ldr     q16, [sp, #336]
        tbl     v19.16b, {v2.16b-v3.16b}, v18.16b
        tbl     v21.16b, {v2.16b-v3.16b}, v20.16b
        tbl     v17.16b, {v2.16b-v3.16b}, v16.16b
        tbl     v0.16b, {v6.16b-v7.16b}, v22.16b
        ldr     q6, [sp, #320]
        tbl     v16.16b, {v4.16b-v5.16b}, v6.16b
        ldr     q6, [sp, #224]
        tbl     v7.16b, {v2.16b-v3.16b}, v6.16b
        ldr     q2, [sp, #352]
        tbl     v2.16b, {v0.16b-v1.16b}, v2.16b
        tbl     v0.16b, {v16.16b-v17.16b}, v22.16b
        ldp     q22, q3, [sp, #256]
        tbl     v18.16b, {v4.16b-v5.16b}, v3.16b
        ldr     q3, [sp, #208]
        tbl     v6.16b, {v4.16b-v5.16b}, v3.16b
        ldr     q3, [sp, #160]
        tbl     v20.16b, {v4.16b-v5.16b}, v3.16b
        ldr     q3, [sp, #304]
        tbl     v4.16b, {v0.16b-v1.16b}, v3.16b
        and     v3.16b, v2.16b, v23.16b
        uxtl    v5.8h, v3.8b
        tbl     v0.16b, {v18.16b-v19.16b}, v22.16b
        ldr     q19, [sp, #144]
        uxtl2   v16.8h, v3.16b
        umull   v3.4s, v5.4h, v13.4h
        umull2  v17.4s, v5.8h, v13.8h
        ldr     q5, [sp, #240]
        movi    v18.16b, #0x18
        tbl     v5.16b, {v0.16b-v1.16b}, v5.16b
        tbl     v0.16b, {v6.16b-v7.16b}, v22.16b
        shl     v6.16b, v4.16b, #3
        ushr    v7.16b, v4.16b, #2
        and     v6.16b, v6.16b, v18.16b
        and     v18.16b, v7.16b, v23.16b
        ldr     q7, [sp, #192]
        usra    v6.16b, v2.16b, #5
        movi    v2.16b, #0x1e
        tbl     v7.16b, {v0.16b-v1.16b}, v7.16b
        tbl     v0.16b, {v20.16b-v21.16b}, v19.16b
        add     v19.16b, v5.16b, v5.16b
        umull   v22.4s, v16.4h, v13.4h
        and     v2.16b, v19.16b, v2.16b
        ldr     q19, [sp, #128]
        usra    v2.16b, v4.16b, #7
        movi    v4.16b, #0x10
        tbl     v19.16b, {v0.16b-v1.16b}, v19.16b
        ushr    v1.16b, v7.16b, #1
        shl     v0.16b, v7.16b, #4
        and     v20.16b, v1.16b, v23.16b
        movi    v1.16b, #0x1c
        and     v4.16b, v0.16b, v4.16b
        shl     v0.16b, v19.16b, #2
        usra    v4.16b, v5.16b, #4
        ushr    v15.16b, v19.16b, #3
        and     v5.16b, v0.16b, v1.16b
        uxtl2   v1.8h, v6.16b
        usra    v5.16b, v7.16b, #6
        umull2  v7.4s, v1.8h, v13.8h
        umull   v1.4s, v1.4h, v13.4h
        uxtl    v6.8h, v6.8b
        umull2  v0.4s, v16.8h, v13.8h
        umull2  v25.4s, v6.8h, v13.8h
        str     q1, [sp, #560]
        umull   v1.4s, v6.4h, v13.4h
        uxtl    v6.8h, v18.8b
        uxtl2   v16.8h, v18.16b
        umull   v21.4s, v6.4h, v13.4h
        umull2  v23.4s, v6.8h, v13.8h
        uxtl2   v6.8h, v2.16b
        uxtl    v18.8h, v2.8b
        umull2  v2.4s, v6.8h, v13.8h
        umull   v24.4s, v16.4h, v13.4h
        umull2  v26.4s, v16.8h, v13.8h
        umull2  v16.4s, v18.8h, v13.8h
        stp     q2, q7, [sp, #608]
        umull   v2.4s, v6.4h, v13.4h
        uxtl    v6.8h, v4.8b
        uxtl2   v4.8h, v4.16b
        umull   v28.4s, v18.4h, v13.4h
        umull   v18.4s, v4.4h, v13.4h
        str     q2, [sp, #544]
        umull2  v8.4s, v4.8h, v13.8h
        uxtl2   v4.8h, v20.16b
        umull   v30.4s, v6.4h, v13.4h
        umull2  v2.4s, v4.8h, v13.8h
        uxtl    v20.8h, v20.8b
        rshrn   v18.4h, v18.4s, #5
        umull2  v27.4s, v20.8h, v13.8h
        rshrn   v9.4h, v30.4s, #5
        str     q2, [sp, #576]
        umull   v2.4s, v4.4h, v13.4h
        uxtl    v4.8h, v5.8b
        uxtl2   v5.8h, v5.16b
        umull   v12.4s, v4.4h, v13.4h
        umull   v14.4s, v5.4h, v13.4h
        str     q2, [sp, #512]
        umull2  v11.4s, v4.8h, v13.8h
        umull2  v31.4s, v6.8h, v13.8h
        rshrn   v6.4h, v3.4s, #5
        rshrn   v19.4h, v14.4s, #5
        rshrn   v10.4h, v12.4s, #5
        umull   v14.4s, v20.4h, v13.4h
        rshrn   v7.4h, v21.4s, #5
        uxtl2   v20.8h, v15.16b
        uxtl    v2.8h, v15.8b
        umull2  v4.4s, v20.8h, v13.8h
        str     q2, [sp, #592]
        umull2  v30.4s, v2.8h, v13.8h
        rshrn   v2.4h, v17.4s, #5
        umull   v15.4s, v20.4h, v13.4h
        rshrn2  v6.8h, v1.4s, #5
        rshrn   v20.4h, v0.4s, #5
        umull2  v5.4s, v5.8h, v13.8h
        rshrn   v21.4h, v26.4s, #5
        rshrn2  v10.8h, v11.4s, #5
        rshrn   v3.4h, v23.4s, #5
        rshrn2  v7.8h, v28.4s, #5
        rshrn   v4.4h, v4.4s, #5
        ldp     q26, q28, [sp, #96]
        rshrn2  v9.8h, v14.4s, #5
        rshrn   v0.4h, v31.4s, #5
        rshrn2  v2.8h, v25.4s, #5
        str     q4, [sp, #528]
        rshrn2  v19.8h, v5.4s, #5
        tbl     v5.16b, {v9.16b-v10.16b}, v26.16b
        rshrn2  v0.8h, v27.4s, #5
        ldr     q25, [sp, #64]
        rshrn   v30.4h, v30.4s, #5
        ldr     q31, [sp, #32]
        rshrn   v17.4h, v15.4s, #5
        mov     v1.16b, v10.16b
        ldr     q14, [sp]
        tbl     v4.16b, {v9.16b-v10.16b}, v25.16b
        rshrn2  v3.8h, v16.4s, #5
        rshrn   v11.4h, v22.4s, #5
        ldr     q22, [sp, #80]
        rshrn   v12.4h, v24.4s, #5
        rshrn   v23.4h, v8.4s, #5
        stp     q4, q5, [sp, #480]
        ldr     q4, [sp, #688]
        tbl     v8.16b, {v2.16b-v3.16b}, v22.16b
        tbl     v5.16b, {v0.16b-v1.16b}, v4.16b
        tbl     v4.16b, {v9.16b-v10.16b}, v31.16b
        mov     v5.h[7], v30.h[0]
        str     q4, [sp, #464]
        tbl     v4.16b, {v9.16b-v10.16b}, v14.16b
        str     q4, [sp, #448]
        tbl     v4.16b, {v2.16b-v3.16b}, v28.16b
        stp     q5, q4, [sp, #416]
        ldr     q4, [sp, #672]
        ldr     q5, [sp, #48]
        tbl     v15.16b, {v0.16b-v1.16b}, v4.16b
        ldr     q4, [sp, #656]
        tbl     v9.16b, {v2.16b-v3.16b}, v5.16b
        tbl     v10.16b, {v0.16b-v1.16b}, v4.16b
        ldr     q4, [sp, #640]
        mov     v15.h[7], v30.h[1]
        tbl     v29.16b, {v0.16b-v1.16b}, v4.16b
        ldr     q0, [sp, #560]
        ldr     q4, [sp, #16]
        mov     v10.h[7], v30.h[2]
        rshrn2  v11.8h, v0.4s, #5
        ldr     q0, [sp, #512]
        tbl     v27.16b, {v2.16b-v3.16b}, v4.16b
        mov     v29.h[7], v30.h[3]
        rshrn2  v18.8h, v0.4s, #5
        ldr     q0, [sp, #544]
        mov     v8.d[1], v15.d[1]
        mov     v9.d[1], v10.d[1]
        rshrn2  v12.8h, v0.4s, #5
        ldr     q0, [sp, #624]
        tbl     v16.16b, {v18.16b-v19.16b}, v26.16b
        tbl     v2.16b, {v18.16b-v19.16b}, v25.16b
        rshrn2  v20.8h, v0.4s, #5
        ldr     q0, [sp, #608]
        tbl     v25.16b, {v18.16b-v19.16b}, v31.16b
        tbl     v30.16b, {v18.16b-v19.16b}, v14.16b
        rshrn2  v21.8h, v0.4s, #5
        ldr     q0, [sp, #576]
        tbl     v26.16b, {v11.16b-v12.16b}, v28.16b
        tbl     v3.16b, {v11.16b-v12.16b}, v22.16b
        rshrn2  v23.8h, v0.4s, #5
        ldr     q0, [sp, #688]
        mov     v24.16b, v19.16b
        tbl     v1.16b, {v11.16b-v12.16b}, v5.16b
        tbl     v18.16b, {v23.16b-v24.16b}, v0.16b
        ldr     q0, [sp, #672]
        tbl     v11.16b, {v11.16b-v12.16b}, v4.16b
        mov     v25.h[7], v17.h[2]
        tbl     v19.16b, {v23.16b-v24.16b}, v0.16b
        ldr     q0, [sp, #656]
        mov     v30.h[7], v17.h[3]
        mov     v16.h[7], v17.h[0]
        tbl     v12.16b, {v23.16b-v24.16b}, v0.16b
        ldr     q0, [sp, #640]
        mov     v2.h[7], v17.h[1]
        tbl     v17.16b, {v20.16b-v21.16b}, v28.16b
        tbl     v23.16b, {v23.16b-v24.16b}, v0.16b
        tbl     v24.16b, {v20.16b-v21.16b}, v22.16b
        tbl     v0.16b, {v20.16b-v21.16b}, v5.16b
        tbl     v20.16b, {v20.16b-v21.16b}, v4.16b
        ldr     q21, [sp, #528]
        mov     v11.d[1], v30.d[1]
        mov     v1.d[1], v25.d[1]
        mov     v23.h[7], v21.h[3]
        mov     v12.h[7], v21.h[2]
        mov     v26.d[1], v16.d[1]
        stp     q1, q11, [x0, #160]
        ldp     q1, q16, [sp, #416]
        mov     v20.d[1], v23.d[1]
        mov     v0.d[1], v12.d[1]
        mov     v3.d[1], v2.d[1]
        tbl     v2.16b, {v6.16b-v7.16b}, v22.16b
        tbl     v4.16b, {v6.16b-v7.16b}, v4.16b
        stp     q0, q20, [x0, #224]
        ldr     q0, [sp, #592]
        mov     v16.d[1], v1.d[1]
        stp     q26, q3, [x0, #128]
        tbl     v1.16b, {v6.16b-v7.16b}, v28.16b
        umull   v0.4s, v0.4h, v13.4h
        tbl     v3.16b, {v6.16b-v7.16b}, v5.16b
        stp     q16, q8, [x0, #64]
        ldp     q16, q7, [sp, #448]
        rshrn   v0.4h, v0.4s, #5
        mov     v19.h[7], v21.h[1]
        mov     v18.h[7], v21.h[0]
        mov     v16.h[7], v0.h[3]
        mov     v27.d[1], v29.d[1]
        ldp     q6, q5, [sp, #480]
        mov     v7.h[7], v0.h[2]
        mov     v24.d[1], v19.d[1]
        mov     v17.d[1], v18.d[1]
        stp     q9, q27, [x0, #96]
        mov     v6.h[7], v0.h[1]
        mov     v4.d[1], v16.d[1]
        mov     v5.h[7], v0.h[0]
        mov     v3.d[1], v7.d[1]
        stp     q17, q24, [x0, #192]
        mov     v2.d[1], v6.d[1]
        mov     v1.d[1], v5.d[1]
        stp     q3, q4, [x0, #32]
        stp     q1, q2, [x0], #256
        b.ne    L36d0
L3ad4:
        add     sp, sp, #0x2c0
        ldp     d9, d8, [sp, #48]
        ldp     d11, d10, [sp, #32]
        ldp     d13, d12, [sp, #16]
        ldr     x29, [sp, #64]
        ldp     d15, d14, [sp], #80
        ret

// mlkem_poly_decompress_d11 (0x10c bytes)
L3af0:
        mov     w9, #0xd01
        .inst   0xf000002b  // adrp x11, 0xa000
        .inst   0xf000002c  // adrp x12, 0xa000
        mov     x8, xzr
        add     x10, x1, #0x5
        dup     v1.4h, w9
        ldr     q0, [x11, #3888]
        ldr     q2, [x12, #3904]
        mov     w11, #0x400
L3b14:
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
        b.ne    L3b14
        ret

// mlkem_poly_tobytes (0x250 bytes)
L3bfc:
        add     x8, x1, #0x200
        cmp     x8, x0
        b.ls    L3c50
        add     x8, x0, #0x180
        cmp     x8, x1
        b.ls    L3c50
        mov     x8, xzr
        add     x9, x0, #0x2
L3c1c:
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
        b.ne    L3c1c
        ret
L3c50:
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
L3e4c:
        add     x8, x1, #0x180
        cmp     x8, x0
        b.ls    L3ea0
        add     x8, x0, #0x200
        cmp     x8, x1
        b.ls    L3ea0
        mov     x8, xzr
        add     x9, x1, #0x2
L3e6c:
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
        b.ne    L3e6c
        ret
L3ea0:
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
L413c:
        mov     x8, xzr
        add     x9, x0, #0x8
        mov     w10, #0x681
L4148:
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
        b.ne    L4148
        ret

// mlkem_poly_tomsg (0x700 bytes)
L421c:
        sub     sp, sp, #0x1e0
        stp     d15, d14, [sp, #400]
        stp     d13, d12, [sp, #416]
        stp     d11, d10, [sp, #432]
        stp     d9, d8, [sp, #448]
        str     x29, [sp, #464]
        add     x8, x1, #0x200
        cmp     x8, x0
        b.ls    L4318
        add     x8, x0, #0x20
        cmp     x8, x1
        b.ls    L4318
        mov     w9, #0xafb8
        mov     x8, xzr
        movk    w9, #0x13, lsl #16
        add     x10, x1, #0x8
        mov     w11, #0x40000000
L4260:
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
        b.ne    L4260
        b       L4900
L4318:
        .inst   0xd0000029  // adrp x9, 0xa000
        .inst   0xd000002a  // adrp x10, 0xa000
        mov     x8, xzr
        ldr     q0, [x9, #3200]
        .inst   0xd0000029  // adrp x9, 0xa000
        str     q0, [sp, #256]
        ldr     q0, [x10, #3216]
        .inst   0xd000002a  // adrp x10, 0xa000
        str     q0, [sp, #80]
        ldr     q0, [x9, #3232]
        mov     w9, #0xafb8
        movk    w9, #0x13, lsl #16
        str     q0, [sp, #64]
        ldr     q0, [x10, #3248]
        .inst   0xd000002a  // adrp x10, 0xa000
        dup     v12.4s, w9
        str     q0, [sp, #48]
        ldr     q0, [x10, #3264]
        .inst   0xd000002a  // adrp x10, 0xa000
        str     q0, [sp, #32]
        ldr     q0, [x10, #3280]
        .inst   0xd000002a  // adrp x10, 0xa000
        str     q0, [sp, #16]
        ldr     q0, [x10, #3296]
        str     q0, [sp]
L437c:
        movi    v0.2d, #0x0
        add     x9, sp, #0x130
        str     q0, [x0, x8]
        ldp     q0, q1, [x1, #128]
        mov     v5.16b, v0.16b
        mov     v31.16b, v5.16b
        ldp     q16, q17, [x1, #32]
        mov     v6.16b, v1.16b
        zip1    v20.4h, v5.4h, v6.4h
        mov     v27.16b, v16.16b
        ldp     q25, q26, [x1]
        zip1    v4.4h, v16.4h, v17.4h
        mov     v28.16b, v17.16b
        ext     v2.8b, v16.8b, v4.8b, #4
        ldp     q23, q24, [x1, #224]
        st1     {v25.2d-v26.2d}, [x9]
        add     x9, sp, #0xa0
        zip1    v3.4h, v25.4h, v26.4h
        movi    v16.4s, #0x40, lsl #24
        ldp     q8, q9, [x1, #96]
        zip1    v17.4h, v23.4h, v24.4h
        mov     v3.s[1], v2.s[1]
        ext     v21.8b, v23.8b, v17.8b, #4
        ldp     q29, q30, [x1, #160]
        zip1    v15.4h, v8.4h, v9.4h
        sxtl    v3.4s, v3.4h
        mla     v16.4s, v3.4s, v12.4s
        ext     v2.8b, v8.8b, v15.8b, #4
        ldp     q0, q1, [x1, #64]
        zip1    v7.4h, v29.4h, v30.4h
        mov     v13.16b, v0.16b
        ext     v19.8b, v29.8b, v7.8b, #4
        ldp     q10, q11, [x1, #192]
        st1     {v0.2d-v1.2d}, [x9]
        add     x9, sp, #0x150
        zip1    v18.4h, v0.4h, v1.4h
        add     x1, x1, #0x100
        mov     v20.s[1], v19.s[1]
        st1     {v5.2d-v6.2d}, [x9]
        add     x9, sp, #0x170
        movi    v19.4s, #0x40, lsl #24
        zip1    v5.4h, v10.4h, v11.4h
        mov     v18.s[1], v2.s[1]
        st1     {v29.2d-v30.2d}, [x9]
        mov     v0.16b, v6.16b
        add     x9, sp, #0x130
        movi    v6.4s, #0x40, lsl #24
        mov     v5.s[1], v21.s[1]
        movi    v21.4s, #0x40, lsl #24
        mov     v14.16b, v1.16b
        sxtl    v1.4s, v18.4h
        sxtl    v5.4s, v5.4h
        trn2    v18.4h, v25.4h, v26.4h
        ld1     {v25.2d-v26.2d}, [x9]
        sxtl    v2.4s, v20.4h
        trn2    v20.4h, v31.4h, v0.4h
        mla     v21.4s, v5.4s, v12.4s
        add     x9, sp, #0xa0
        mla     v19.4s, v2.4s, v12.4s
        mla     v6.4s, v1.4s, v12.4s
        mov     v18.s[1], v4.s[1]
        trn2    v4.4h, v10.4h, v11.4h
        ushr    v3.4s, v21.4s, #31
        ldr     q21, [sp, #256]
        ushr    v2.4s, v19.4s, #31
        trn2    v22.4h, v13.4h, v14.4h
        ushr    v1.4s, v6.4s, #31
        mov     v4.s[1], v17.s[1]
        ushr    v0.4s, v16.4s, #31
        mov     v20.s[1], v7.s[1]
        tbl     v0.16b, {v0.16b-v3.16b}, v21.16b
        movi    v3.4s, #0x40, lsl #24
        sxtl    v1.4s, v4.4h
        mov     v22.s[1], v15.s[1]
        mov     v13.16b, v27.16b
        str     q0, [sp, #240]
        mla     v3.4s, v1.4s, v12.4s
        mov     v14.16b, v28.16b
        ld1     {v27.2d-v28.2d}, [x9]
        add     x9, sp, #0x150
        movi    v7.4s, #0x40, lsl #24
        sxtl    v5.4s, v18.4h
        movi    v4.4s, #0x40, lsl #24
        ushr    v19.4s, v3.4s, #30
        mov     v3.16b, v29.16b
        sxtl    v0.4s, v20.4h
        mov     v3.h[3], v30.h[2]
        ld1     {v29.2d-v30.2d}, [x9]
        sxtl    v6.4s, v22.4h
        add     x9, sp, #0x110
        mla     v7.4s, v0.4s, v12.4s
        mla     v4.4s, v6.4s, v12.4s
        movi    v2.4s, #0x40, lsl #24
        st1     {v8.2d-v9.2d}, [x9]
        mov     v0.16b, v8.16b
        add     x9, sp, #0x170
        mov     v0.h[3], v9.h[2]
        mov     v6.16b, v23.16b
        ushr    v18.4s, v7.4s, #30
        zip2    v7.4h, v27.4h, v28.4h
        ushr    v17.4s, v4.4s, #30
        mov     v1.16b, v13.16b
        zip2    v4.4h, v29.4h, v30.4h
        mov     v6.h[3], v24.h[2]
        zip2    v20.4h, v10.4h, v11.4h
        mla     v2.4s, v5.4s, v12.4s
        zip2    v5.4h, v25.4h, v26.4h
        mov     v1.h[3], v14.h[2]
        mov     v7.s[1], v0.s[1]
        mov     v4.s[1], v3.s[1]
        mov     v20.s[1], v6.s[1]
        mov     v5.s[1], v1.s[1]
        movi    v6.4s, #0x40, lsl #24
        sxtl    v1.4s, v7.4h
        movi    v7.4s, #0x40, lsl #24
        sxtl    v3.4s, v4.4h
        sxtl    v4.4s, v20.4h
        movi    v20.4s, #0x40, lsl #24
        sxtl    v0.4s, v5.4h
        movi    v5.4s, #0x40, lsl #24
        mla     v6.4s, v4.4s, v12.4s
        mla     v7.4s, v3.4s, v12.4s
        mla     v20.4s, v1.4s, v12.4s
        mla     v5.4s, v0.4s, v12.4s
        ushr    v16.4s, v2.4s, #30
        ushr    v3.4s, v6.4s, #29
        uzp2    v6.4h, v25.4h, v26.4h
        ushr    v2.4s, v7.4s, #29
        ushr    v1.4s, v20.4s, #29
        ushr    v0.4s, v5.4s, #29
        zip2    v5.4h, v13.4h, v14.4h
        tbl     v4.16b, {v16.16b-v19.16b}, v21.16b
        uzp2    v7.4h, v6.4h, v25.4h
        tbl     v0.16b, {v0.16b-v3.16b}, v21.16b
        mov     v18.16b, v27.16b
        mov     v19.16b, v28.16b
        mov     v16.16b, v29.16b
        stp     q0, q4, [sp, #208]
        uzp2    v0.4h, v18.4h, v19.4h
        mov     v17.16b, v30.16b
        ld1     {v29.2d-v30.2d}, [x9]
        mov     v27.16b, v10.16b
        add     x9, sp, #0x80
        mov     v28.16b, v11.16b
        uzp2    v1.4h, v16.4h, v17.4h
        uzp2    v2.4h, v27.4h, v28.4h
        zip2    v3.4h, v8.4h, v9.4h
        mov     v7.s[1], v5.s[1]
        uzp2    v0.4h, v0.4h, v18.4h
        movi    v4.4s, #0x40, lsl #24
        st1     {v27.2d-v28.2d}, [x9]
        uzp2    v1.4h, v1.4h, v16.4h
        add     x9, sp, #0x150
        zip2    v16.4h, v23.4h, v24.4h
        uzp2    v2.4h, v2.4h, v27.4h
        mov     v0.s[1], v3.s[1]
        zip2    v5.4h, v29.4h, v30.4h
        sxtl    v3.4s, v7.4h
        movi    v17.4s, #0x40, lsl #24
        mla     v4.4s, v3.4s, v12.4s
        mov     v2.s[1], v16.s[1]
        mov     v1.s[1], v5.s[1]
        movi    v5.4s, #0x40, lsl #24
        str     q4, [sp, #192]
        ldr     q4, [sp, #80]
        sxtl    v2.4s, v2.4h
        movi    v3.4s, #0x40, lsl #24
        sxtl    v0.4s, v0.4h
        sxtl    v1.4s, v1.4h
        mla     v5.4s, v2.4s, v12.4s
        tbl     v2.16b, {v13.16b-v14.16b}, v4.16b
        zip2    v16.8h, v25.8h, v26.8h
        mov     v10.16b, v18.16b
        mov     v11.16b, v19.16b
        mla     v17.4s, v0.4s, v12.4s
        mla     v3.4s, v1.4s, v12.4s
        tbl     v0.16b, {v8.16b-v9.16b}, v4.16b
        zip2    v1.8h, v10.8h, v11.8h
        mov     v16.s[1], v2.s[1]
        tbl     v2.16b, {v29.16b-v30.16b}, v4.16b
        ld1     {v29.2d-v30.2d}, [x9]
        add     x9, sp, #0x60
        ushr    v21.4s, v5.4s, #28
        mov     v1.s[1], v0.s[1]
        ushr    v20.4s, v3.4s, #28
        sxtl    v3.4s, v16.4h
        tbl     v0.16b, {v23.16b-v24.16b}, v4.16b
        st1     {v23.2d-v24.2d}, [x9]
        zip2    v16.8h, v27.8h, v28.8h
        add     x9, sp, #0x110
        movi    v27.4s, #0x40, lsl #24
        sxtl    v1.4s, v1.4h
        mov     v8.16b, v23.16b
        mov     v16.s[1], v0.s[1]
        mla     v27.4s, v1.4s, v12.4s
        ld1     {v0.2d-v1.2d}, [x9]
        add     x9, sp, #0x170
        ushr    v19.4s, v17.4s, #28
        mov     v9.16b, v24.16b
        movi    v7.4s, #0x40, lsl #24
        ld1     {v23.2d-v24.2d}, [x9]
        add     x9, sp, #0x80
        zip2    v5.8h, v29.8h, v30.8h
        movi    v22.4s, #0x40, lsl #24
        mla     v7.4s, v3.4s, v12.4s
        ldr     q3, [sp, #64]
        mov     v5.s[1], v2.s[1]
        sxtl    v16.4s, v16.4h
        movi    v2.4s, #0x40, lsl #24
        mla     v22.4s, v16.4s, v12.4s
        zip2    v16.8h, v0.8h, v1.8h
        zip2    v1.8h, v23.8h, v24.8h
        tbl     v23.16b, {v29.16b-v30.16b}, v3.16b
        ld1     {v30.2d-v31.2d}, [x9]
        sxtl    v5.4s, v5.4h
        add     x9, sp, #0x130
        tbl     v0.16b, {v10.16b-v11.16b}, v3.16b
        mla     v2.4s, v5.4s, v12.4s
        zip2    v6.8h, v13.8h, v14.8h
        tbl     v5.16b, {v25.16b-v26.16b}, v3.16b
        ldr     q26, [sp, #256]
        zip2    v25.8h, v8.8h, v9.8h
        tbl     v24.16b, {v30.16b-v31.16b}, v3.16b
        mov     v0.s[1], v16.s[1]
        mov     v5.s[1], v6.s[1]
        movi    v6.4s, #0x40, lsl #24
        movi    v4.4s, #0x40, lsl #24
        mov     v24.s[1], v25.s[1]
        sxtl    v0.4s, v0.4h
        mov     v23.s[1], v1.s[1]
        ldr     q1, [sp, #192]
        sxtl    v5.4s, v5.4h
        mla     v6.4s, v0.4s, v12.4s
        movi    v0.4s, #0x40, lsl #24
        mla     v4.4s, v5.4s, v12.4s
        movi    v5.4s, #0x40, lsl #24
        sxtl    v16.4s, v24.4h
        sxtl    v23.4s, v23.4h
        mla     v0.4s, v16.4s, v12.4s
        mla     v5.4s, v23.4s, v12.4s
        ushr    v18.4s, v1.4s, #28
        ushr    v25.4s, v22.4s, #27
        tbl     v9.16b, {v18.16b-v21.16b}, v26.16b
        ld1     {v17.2d-v18.2d}, [x9]
        add     x9, sp, #0x110
        ushr    v24.4s, v2.4s, #27
        ushr    v3.4s, v0.4s, #26
        ushr    v23.4s, v27.4s, #27
        ushr    v2.4s, v5.4s, #26
        ushr    v22.4s, v7.4s, #27
        ushr    v1.4s, v6.4s, #26
        ld1     {v7.2d-v8.2d}, [x9]
        add     x9, sp, #0x170
        ushr    v0.4s, v4.4s, #26
        tbl     v4.16b, {v22.16b-v25.16b}, v26.16b
        tbl     v15.16b, {v0.16b-v3.16b}, v26.16b
        ldp     q16, q6, [sp, #32]
        mov     v22.16b, v13.16b
        mov     v23.16b, v14.16b
        str     q4, [sp, #192]
        tbl     v1.16b, {v17.16b-v18.16b}, v16.16b
        tbl     v3.16b, {v10.16b-v11.16b}, v16.16b
        ld1     {v19.2d-v20.2d}, [x9]
        add     x9, sp, #0x150
        tbl     v0.16b, {v13.16b-v14.16b}, v6.16b
        tbl     v2.16b, {v7.16b-v8.16b}, v6.16b
        ld1     {v13.2d-v14.2d}, [x9]
        add     x9, sp, #0x60
        mov     v1.s[1], v0.s[1]
        movi    v0.4s, #0x40, lsl #24
        tbl     v4.16b, {v19.16b-v20.16b}, v6.16b
        ld1     {v24.2d-v25.2d}, [x9]
        mov     v3.s[1], v2.s[1]
        sxtl    v1.4s, v1.4h
        tbl     v5.16b, {v13.16b-v14.16b}, v16.16b
        tbl     v16.16b, {v30.16b-v31.16b}, v16.16b
        ldr     q21, [sp, #16]
        movi    v2.4s, #0x40, lsl #24
        mla     v0.4s, v1.4s, v12.4s
        tbl     v6.16b, {v24.16b-v25.16b}, v6.16b
        mov     v5.s[1], v4.s[1]
        movi    v1.4s, #0x40, lsl #24
        sxtl    v3.4s, v3.4h
        mov     v16.s[1], v6.s[1]
        sxtl    v4.4s, v5.4h
        mla     v2.4s, v3.4s, v12.4s
        movi    v3.4s, #0x40, lsl #24
        mla     v1.4s, v4.4s, v12.4s
        tbl     v4.16b, {v22.16b-v23.16b}, v21.16b
        ldr     q22, [sp]
        sxtl    v5.4s, v16.4h
        tbl     v6.16b, {v7.16b-v8.16b}, v21.16b
        mla     v3.4s, v5.4s, v12.4s
        tbl     v5.16b, {v17.16b-v18.16b}, v22.16b
        tbl     v16.16b, {v10.16b-v11.16b}, v22.16b
        tbl     v19.16b, {v19.16b-v20.16b}, v21.16b
        tbl     v20.16b, {v13.16b-v14.16b}, v22.16b
        tbl     v21.16b, {v24.16b-v25.16b}, v21.16b
        tbl     v22.16b, {v30.16b-v31.16b}, v22.16b
        mov     v5.s[1], v4.s[1]
        mov     v16.s[1], v6.s[1]
        mov     v20.s[1], v19.s[1]
        mov     v22.s[1], v21.s[1]
        sxtl    v4.4s, v5.4h
        sxtl    v5.4s, v16.4h
        movi    v19.4s, #0x40, lsl #24
        sxtl    v16.4s, v22.4h
        movi    v21.4s, #0x40, lsl #24
        movi    v22.4s, #0x40, lsl #24
        sxtl    v6.4s, v20.4h
        mla     v19.4s, v4.4s, v12.4s
        mla     v21.4s, v6.4s, v12.4s
        mla     v22.4s, v5.4s, v12.4s
        ushr    v6.4s, v3.4s, #25
        ushr    v5.4s, v1.4s, #25
        ushr    v4.4s, v2.4s, #25
        ushr    v3.4s, v0.4s, #25
        movi    v2.16b, #0x2
        tbl     v0.16b, {v3.16b-v6.16b}, v26.16b
        ldp     q4, q3, [sp, #208]
        movi    v20.4s, #0x40, lsl #24
        mla     v20.4s, v16.4s, v12.4s
        and     v2.16b, v3.16b, v2.16b
        movi    v3.16b, #0x4
        ushr    v30.4s, v20.4s, #24
        ushr    v29.4s, v21.4s, #24
        and     v3.16b, v4.16b, v3.16b
        ldr     q4, [sp, #192]
        orr     v2.16b, v2.16b, v3.16b
        ldr     q3, [sp, #240]
        ushr    v28.4s, v22.4s, #24
        ushr    v27.4s, v19.4s, #24
        orr     v2.16b, v2.16b, v3.16b
        movi    v3.16b, #0x8
        tbl     v1.16b, {v27.16b-v30.16b}, v26.16b
        and     v3.16b, v9.16b, v3.16b
        orr     v2.16b, v2.16b, v3.16b
        movi    v3.16b, #0x10
        and     v3.16b, v4.16b, v3.16b
        movi    v4.16b, #0x20
        and     v4.16b, v15.16b, v4.16b
        orr     v3.16b, v3.16b, v4.16b
        movi    v4.16b, #0x40
        and     v0.16b, v0.16b, v4.16b
        orr     v0.16b, v3.16b, v0.16b
        orr     v0.16b, v2.16b, v0.16b
        movi    v2.16b, #0x80
        and     v1.16b, v1.16b, v2.16b
        orr     v0.16b, v0.16b, v1.16b
        str     q0, [x0, x8]
        add     x8, x8, #0x10
        cmp     x8, #0x20
        b.ne    L437c
L4900:
        ldp     d9, d8, [sp, #448]
        ldp     d11, d10, [sp, #432]
        ldp     d13, d12, [sp, #416]
        ldp     d15, d14, [sp, #400]
        ldr     x29, [sp, #464]
        add     sp, sp, #0x1e0
        ret

// mlkem_shake128_absorb_once (0x18 bytes)
L491c:
        mov     x8, x1
        mov     x3, x2
        mov     w1, #0xa8
        mov     x2, x8
        mov     w4, #0x1f
        b       L4934

// mlk_keccak_absorb_once (0x128 bytes)
L4934:
        sub     sp, sp, #0x50
        str     x30, [sp, #16]
        stp     x24, x23, [sp, #32]
        stp     x22, x21, [sp, #48]
        stp     x20, x19, [sp, #64]
        .inst   0xf00000c8  // adrp x8, 0x1f000
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
        b.hi    L49c8
L499c:
        mov     x0, x19
        mov     x1, x23
        mov     w2, wzr
        mov     w3, w22
        bl      L524c
        mov     x0, x19
        bl      L5a5c
        sub     x20, x20, x24
        add     x23, x23, x24
        cmp     x20, x24
        b.cs    L499c
L49c8:
        cbz     x20, L49e0
        mov     x0, x19
        mov     x1, x23
        mov     w2, wzr
        mov     w3, w20
        bl      L524c
L49e0:
        sub     w22, w22, #0x1
        cmp     x20, x22
        b.ne    L49f4
        orr     w8, w21, #0x80
        b       L4a10
L49f4:
        add     x1, sp, #0x4
        mov     x0, x19
        mov     w2, w20
        mov     w3, #0x1
        bl      L524c
        mov     w8, #0x80
        mov     w20, w22
L4a10:
        add     x1, sp, #0x4
        mov     x0, x19
        mov     w2, w20
        mov     w3, #0x1
        strb    w8, [sp, #4]
        bl      L524c
        .inst   0xf00000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #8]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L4a58
        ldp     x20, x19, [sp, #64]
        ldp     x22, x21, [sp, #48]
        ldp     x24, x23, [sp, #32]
        ldr     x30, [sp, #16]
        add     sp, sp, #0x50
        ret
L4a58:
        bl      L0830

// mlkem_shake128_squeezeblocks (0x4c bytes)
L4a5c:
        cbz     x1, L4aa4
        stp     x30, x21, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x2
        mov     x20, x1
        mov     x21, x0
L4a74:
        mov     x0, x19
        bl      L5a5c
        mov     x0, x19
        mov     x1, x21
        mov     w2, wzr
        mov     w3, #0xa8
        bl      L5180
        add     x21, x21, #0xa8
        subs    x20, x20, #0x1
        b.ne    L4a74
        ldp     x20, x19, [sp, #16]
        ldp     x30, x21, [sp], #32
L4aa4:
        ret

// mlkem_shake128_init (0x4 bytes)
L4aa8:
        ret

// mlkem_shake128_release (0x24 bytes)
L4aac:
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
L4ad0:
        stp     x29, x30, [sp, #-64]!
        str     x28, [sp, #16]
        stp     x22, x21, [sp, #32]
        stp     x20, x19, [sp, #48]
        mov     x29, sp
        sub     x9, sp, #0x100
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xf00000c8  // adrp x8, 0x1f000
        mov     x19, x1
        mov     x20, x0
        mov     x0, sp
        mov     w1, #0x88
        mov     w4, #0x1f
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #248]
        bl      L4934
        cbz     x19, L4b4c
        mov     w22, #0x88
L4b1c:
        mov     x0, sp
        bl      L5a5c
        cmp     x19, #0x88
        mov     x0, sp
        csel    x21, x19, x22, cc
        mov     x1, x20
        mov     w2, wzr
        mov     w3, w21
        bl      L5180
        add     x20, x20, x21
        subs    x19, x19, x21
        b.ne    L4b1c
L4b4c:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        stp     q0, q0, [sp, #64]
        stp     q0, q0, [sp, #96]
        stp     q0, q0, [sp, #128]
        stp     q0, q0, [sp, #160]
        stp     q0, q0, [sp, #192]
        .inst   0xf00000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #248]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L4ba0
        mov     sp, x29
        ldp     x20, x19, [sp, #48]
        ldp     x22, x21, [sp, #32]
        ldr     x28, [sp, #16]
        ldp     x29, x30, [sp], #64
        ret
L4ba0:
        bl      L0830

// mlkem_sha3_256 (0xa4 bytes)
L4ba4:
        sub     sp, sp, #0xf0
        str     x30, [sp, #208]
        stp     x20, x19, [sp, #224]
        .inst   0xf00000c8  // adrp x8, 0x1f000
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
        bl      L4934
        mov     x0, sp
        bl      L5a5c
        mov     x0, sp
        mov     x1, x19
        mov     w2, wzr
        mov     w3, #0x20
        bl      L5180
        movi    v0.2d, #0x0
        .inst   0xf00000c8  // adrp x8, 0x1f000
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
        b.ne    L4c44
        ldp     x20, x19, [sp, #224]
        ldr     x30, [sp, #208]
        add     sp, sp, #0xf0
        ret
L4c44:
        bl      L0830

// mlkem_sha3_512 (0xa4 bytes)
L4c48:
        sub     sp, sp, #0xf0
        str     x30, [sp, #208]
        stp     x20, x19, [sp, #224]
        .inst   0xf00000c8  // adrp x8, 0x1f000
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
        bl      L4934
        mov     x0, sp
        bl      L5a5c
        mov     x0, sp
        mov     x1, x19
        mov     w2, wzr
        mov     w3, #0x40
        bl      L5180
        movi    v0.2d, #0x0
        .inst   0xf00000c8  // adrp x8, 0x1f000
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
        b.ne    L4ce8
        ldp     x20, x19, [sp, #224]
        ldr     x30, [sp, #208]
        add     sp, sp, #0xf0
        ret
L4ce8:
        bl      L0830

// mlkem_shake128x4_absorb_once (0x64 bytes)
L4cec:
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
        b       L4d50

// mlk_keccak_absorb_once_x4 (0x160 bytes)
L4d50:
        sub     sp, sp, #0x60
        stp     x30, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        .inst   0xf00000c8  // adrp x8, 0x1f000
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
        b.hi    L4df4
        mov     x26, xzr
L4dac:
        add     x4, x22, x26
        add     x3, x23, x26
        add     x2, x24, x26
        add     x1, x25, x26
        mov     x0, x20
        mov     w5, wzr
        mov     w6, w21
        bl      L5660
        mov     x0, x20
        bl      L5a34
        sub     x19, x19, x27
        add     x26, x26, x27
        cmp     x19, x27
        b.cs    L4dac
        add     x22, x22, x26
        add     x23, x23, x26
        add     x24, x24, x26
        add     x25, x25, x26
L4df4:
        cbz     x19, L4e18
        mov     x0, x20
        mov     x1, x25
        mov     x2, x24
        mov     x3, x23
        mov     x4, x22
        mov     w5, wzr
        mov     w6, w19
        bl      L5660
L4e18:
        sub     w21, w21, #0x1
        cmp     x19, x21
        b.ne    L4e2c
        mov     w8, #0x9f
        b       L4e54
L4e2c:
        add     x1, sp, #0x4
        add     x2, sp, #0x4
        add     x3, sp, #0x4
        add     x4, sp, #0x4
        mov     x0, x20
        mov     w5, w19
        mov     w6, #0x1
        bl      L5660
        mov     w8, #0x80
        mov     w19, w21
L4e54:
        add     x1, sp, #0x4
        add     x2, sp, #0x4
        add     x3, sp, #0x4
        add     x4, sp, #0x4
        mov     x0, x20
        mov     w5, w19
        mov     w6, #0x1
        strb    w8, [sp, #4]
        bl      L5660
        .inst   0xf00000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #8]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L4eac
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x30, x27, [sp, #16]
        add     sp, sp, #0x60
        ret
L4eac:
        bl      L0830

// mlkem_shake128x4_squeezeblocks (0x80 bytes)
L4eb0:
        cbz     x4, L4f2c
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
L4edc:
        mov     x0, x19
        bl      L5a34
        mov     x0, x19
        mov     x1, x24
        mov     x2, x23
        mov     x3, x22
        mov     x4, x21
        mov     w5, wzr
        mov     w6, #0xa8
        bl      L5344
        subs    x20, x20, #0x1
        add     x21, x21, #0xa8
        add     x22, x22, #0xa8
        add     x23, x23, #0xa8
        add     x24, x24, #0xa8
        b.ne    L4edc
        ldp     x20, x19, [sp, #48]
        ldp     x22, x21, [sp, #32]
        ldp     x24, x23, [sp, #16]
        ldr     x30, [sp], #64
L4f2c:
        ret

// mlkem_shake128x4_init (0x4 bytes)
L4f30:
        ret

// mlkem_shake128x4_release (0x1c bytes)
L4f34:
        stp     x30, x19, [sp, #-16]!
        mov     w1, wzr
        mov     w2, #0x320
        mov     x19, x0
        bl      L0840
        ldp     x30, x19, [sp], #16
        ret

// mlkem_shake256x4 (0x230 bytes)
L4f50:
        stp     x29, x30, [sp, #-96]!
        stp     x28, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0x5a0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xf00000c9  // adrp x9, 0x1f000
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
        bl      L4d50
        cmp     x23, #0x88
        b.cc    L5044
        mov     x24, x20
        mov     x25, x22
        ldr     x26, [sp, #24]
        mov     x27, x21
        mov     x28, x19
L5004:
        add     x0, sp, #0x260
        bl      L5a34
        add     x0, sp, #0x260
        mov     x1, x24
        mov     x2, x25
        mov     x3, x26
        mov     x4, x27
        mov     w5, wzr
        mov     w6, #0x88
        bl      L5344
        subs    x28, x28, #0x1
        add     x27, x27, #0x88
        add     x26, x26, #0x88
        add     x25, x25, #0x88
        add     x24, x24, #0x88
        b.ne    L5004
L5044:
        add     x8, x19, x19, lsl #4
        lsl     x24, x8, #3
        subs    x23, x23, x24
        b.eq    L50cc
        add     x0, sp, #0x260
        add     x21, x21, x24
        add     x22, x22, x24
        bl      L5a34
        add     x0, sp, #0x260
        add     x1, sp, #0x1d0
        add     x2, sp, #0x140
        add     x3, sp, #0xb0
        add     x4, sp, #0x20
        mov     w5, wzr
        mov     w6, #0x88
        bl      L5344
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
L50cc:
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
        .inst   0xd00000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #1432]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L517c
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L517c:
        bl      L0830

// mlkem_keccakf1600_extract_bytes (0xcc bytes)
L5180:
        cbz     w3, L51c8
        mov     w9, w2
        mov     w8, w3
        cmp     w3, #0x8
        b.cc    L51a4
        sub     x10, x1, x0
        sub     x10, x10, x9
        cmp     x10, #0x20
        b.cs    L51cc
L51a4:
        mov     x10, xzr
L51a8:
        add     x11, x0, x10
        sub     x8, x8, x10
        add     x9, x11, x9
        add     x11, x1, x10
L51b8:
        ldrb    w10, [x9], #1
        subs    x8, x8, #0x1
        strb    w10, [x11], #1
        b.ne    L51b8
L51c8:
        ret
L51cc:
        cmp     w3, #0x20
        b.cs    L51dc
        mov     x10, xzr
        b       L5218
L51dc:
        and     x10, x8, #0xffffffe0
        add     x11, x9, x0
        add     x11, x11, #0x10
        add     x12, x1, #0x10
        mov     x13, x10
L51f0:
        ldp     q0, q1, [x11, #-16]
        add     x11, x11, #0x20
        subs    x13, x13, #0x20
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L51f0
        cmp     x10, x8
        b.eq    L51c8
        tst     x8, #0x18
        b.eq    L51a8
L5218:
        mov     x13, x10
        and     x10, x8, #0xfffffff8
        add     x11, x0, x13
        add     x12, x1, x13
        add     x11, x11, x9
        sub     x13, x13, x10
L5230:
        ldr     d0, [x11], #8
        adds    x13, x13, #0x8
        str     d0, [x12], #8
        b.ne    L5230
        cmp     x10, x8
        b.eq    L51c8
        b       L51a8

// mlkem_keccakf1600_xor_bytes (0xf8 bytes)
L524c:
        cbz     w3, L52ac
        mov     w8, w2
        mov     w9, w3
        cmp     w3, #0x8
        b.cc    L5280
        add     x10, x0, x8
        add     x11, x1, x9
        cmp     x10, x11
        b.cs    L52b0
        add     x10, x9, x8
        add     x10, x0, x10
        cmp     x10, x1
        b.ls    L52b0
L5280:
        mov     x10, xzr
L5284:
        add     x12, x0, x10
        add     x11, x1, x10
        add     x8, x12, x8
        sub     x9, x9, x10
L5294:
        ldrb    w10, [x11], #1
        ldrb    w12, [x8]
        subs    x9, x9, #0x1
        eor     w10, w12, w10
        strb    w10, [x8], #1
        b.ne    L5294
L52ac:
        ret
L52b0:
        cmp     w3, #0x20
        b.cs    L52c0
        mov     x10, xzr
        b       L5308
L52c0:
        and     x10, x9, #0xffffffe0
        add     x12, x8, x0
        add     x11, x1, #0x10
        add     x12, x12, #0x10
        mov     x13, x10
L52d4:
        ldp     q0, q1, [x11, #-16]
        add     x11, x11, #0x20
        subs    x13, x13, #0x20
        ldp     q2, q3, [x12, #-16]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v3.16b, v1.16b
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L52d4
        cmp     x10, x9
        b.eq    L52ac
        tst     x9, #0x18
        b.eq    L5284
L5308:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x12, x0, x13
        add     x11, x1, x13
        add     x12, x12, x8
        sub     x13, x13, x10
L5320:
        ldr     d0, [x11], #8
        ldr     d1, [x12]
        adds    x13, x13, #0x8
        eor     v0.8b, v1.8b, v0.8b
        str     d0, [x12], #8
        b.ne    L5320
        cmp     x10, x9
        b.eq    L52ac
        b       L5284

// mlkem_keccakf1600x4_extract_bytes (0x31c bytes)
L5344:
        cbz     w6, L5458
        mov     w8, w5
        mov     w9, w6
        cmp     w6, #0x8
        b.cc    L5368
        sub     x10, x1, x0
        sub     x10, x10, x8
        cmp     x10, #0x20
        b.cs    L545c
L5368:
        mov     x10, xzr
L536c:
        add     x12, x0, x10
        sub     x11, x9, x10
        add     x10, x1, x10
        add     x12, x12, x8
L537c:
        ldrb    w13, [x12], #1
        subs    x11, x11, #0x1
        strb    w13, [x10], #1
        b.ne    L537c
L538c:
        cmp     w6, #0x8
        b.cc    L53a8
        add     x10, x0, x8
        sub     x10, x2, x10
        sub     x10, x10, #0xc8
        cmp     x10, #0x20
        b.cs    L546c
L53a8:
        mov     x10, xzr
L53ac:
        add     x12, x10, x8
        sub     x11, x9, x10
        add     x12, x12, x0
        add     x10, x2, x10
        add     x12, x12, #0xc8
L53c0:
        ldrb    w13, [x12], #1
        subs    x11, x11, #0x1
        strb    w13, [x10], #1
        b.ne    L53c0
L53d0:
        cmp     w6, #0x8
        b.cc    L53ec
        add     x10, x0, x8
        sub     x10, x3, x10
        sub     x10, x10, #0x190
        cmp     x10, #0x20
        b.cs    L547c
L53ec:
        mov     x10, xzr
L53f0:
        add     x12, x10, x8
        sub     x11, x9, x10
        add     x12, x12, x0
        add     x10, x3, x10
        add     x12, x12, #0x190
L5404:
        ldrb    w13, [x12], #1
        subs    x11, x11, #0x1
        strb    w13, [x10], #1
        b.ne    L5404
L5414:
        cmp     w6, #0x8
        b.cc    L5430
        add     x11, x0, x8
        sub     x10, x4, x11
        sub     x10, x10, #0x258
        cmp     x10, #0x20
        b.cs    L548c
L5430:
        mov     x10, xzr
L5434:
        add     x11, x10, x8
        sub     x8, x9, x10
        add     x11, x11, x0
        add     x9, x4, x10
        add     x10, x11, #0x258
L5448:
        ldrb    w11, [x10], #1
        subs    x8, x8, #0x1
        strb    w11, [x9], #1
        b.ne    L5448
L5458:
        ret
L545c:
        cmp     w6, #0x20
        b.cs    L549c
        mov     x10, xzr
        b       L54d8
L546c:
        cmp     w6, #0x20
        b.cs    L550c
        mov     x10, xzr
        b       L5548
L547c:
        cmp     w6, #0x20
        b.cs    L5580
        mov     x10, xzr
        b       L55bc
L548c:
        cmp     w6, #0x20
        b.cs    L55f4
        mov     x10, xzr
        b       L5628
L549c:
        and     x10, x9, #0xffffffe0
        add     x11, x8, x0
        add     x11, x11, #0x10
        add     x12, x1, #0x10
        mov     x13, x10
L54b0:
        ldp     q0, q1, [x11, #-16]
        add     x11, x11, #0x20
        subs    x13, x13, #0x20
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L54b0
        cmp     x10, x9
        b.eq    L538c
        tst     x9, #0x18
        b.eq    L536c
L54d8:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x11, x0, x13
        add     x12, x1, x13
        add     x11, x11, x8
        sub     x13, x13, x10
L54f0:
        ldr     d0, [x11], #8
        adds    x13, x13, #0x8
        str     d0, [x12], #8
        b.ne    L54f0
        cmp     x10, x9
        b.eq    L538c
        b       L536c
L550c:
        and     x10, x9, #0xffffffe0
        add     x11, x8, x0
        add     x11, x11, #0xd8
        add     x12, x2, #0x10
        mov     x13, x10
L5520:
        ldp     q0, q1, [x11, #-16]
        add     x11, x11, #0x20
        subs    x13, x13, #0x20
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L5520
        cmp     x10, x9
        b.eq    L53d0
        tst     x9, #0x18
        b.eq    L53ac
L5548:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x11, x13, x8
        add     x12, x2, x13
        add     x11, x11, x0
        sub     x13, x13, x10
        add     x11, x11, #0xc8
L5564:
        ldr     d0, [x11], #8
        adds    x13, x13, #0x8
        str     d0, [x12], #8
        b.ne    L5564
        cmp     x10, x9
        b.eq    L53d0
        b       L53ac
L5580:
        and     x10, x9, #0xffffffe0
        add     x11, x8, x0
        add     x11, x11, #0x1a0
        add     x12, x3, #0x10
        mov     x13, x10
L5594:
        ldp     q0, q1, [x11, #-16]
        add     x11, x11, #0x20
        subs    x13, x13, #0x20
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L5594
        cmp     x10, x9
        b.eq    L5414
        tst     x9, #0x18
        b.eq    L53f0
L55bc:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x11, x13, x8
        add     x12, x3, x13
        add     x11, x11, x0
        sub     x13, x13, x10
        add     x11, x11, #0x190
L55d8:
        ldr     d0, [x11], #8
        adds    x13, x13, #0x8
        str     d0, [x12], #8
        b.ne    L55d8
        cmp     x10, x9
        b.eq    L5414
        b       L53f0
L55f4:
        and     x10, x9, #0xffffffe0
        add     x11, x11, #0x258
        add     x12, x4, #0x10
        mov     x13, x10
L5604:
        ldp     q0, q1, [x11], #32
        subs    x13, x13, #0x20
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L5604
        cmp     x10, x9
        b.eq    L5458
        tst     x9, #0x18
        b.eq    L5434
L5628:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x11, x13, x8
        add     x12, x4, x13
        add     x11, x11, x0
        sub     x13, x13, x10
        add     x11, x11, #0x258
L5644:
        ldr     d0, [x11], #8
        adds    x13, x13, #0x8
        str     d0, [x12], #8
        b.ne    L5644
        cmp     x10, x9
        b.eq    L5458
        b       L5434

// mlkem_keccakf1600x4_xor_bytes (0x3d4 bytes)
L5660:
        cbz     w6, L57e0
        mov     w8, w5
        mov     w9, w6
        cmp     w6, #0x8
        b.cc    L5694
        add     x10, x0, x8
        add     x11, x1, x9
        cmp     x10, x11
        b.cs    L57e4
        add     x10, x9, x8
        add     x10, x0, x10
        cmp     x10, x1
        b.ls    L57e4
L5694:
        mov     x10, xzr
L5698:
        add     x12, x0, x10
        sub     x11, x9, x10
        add     x12, x12, x8
        add     x10, x1, x10
L56a8:
        ldrb    w13, [x10], #1
        ldrb    w14, [x12]
        subs    x11, x11, #0x1
        eor     w13, w14, w13
        strb    w13, [x12], #1
        b.ne    L56a8
L56c0:
        cmp     w6, #0x8
        b.cc    L56f0
        add     x10, x0, x8
        add     x11, x2, x9
        add     x10, x10, #0xc8
        cmp     x10, x11
        b.cs    L57f4
        add     x10, x9, x8
        add     x10, x10, x0
        add     x10, x10, #0xc8
        cmp     x10, x2
        b.ls    L57f4
L56f0:
        mov     x10, xzr
L56f4:
        add     x12, x10, x8
        sub     x11, x9, x10
        add     x12, x12, x0
        add     x10, x2, x10
        add     x12, x12, #0xc8
L5708:
        ldrb    w13, [x10], #1
        ldrb    w14, [x12]
        subs    x11, x11, #0x1
        eor     w13, w14, w13
        strb    w13, [x12], #1
        b.ne    L5708
L5720:
        cmp     w6, #0x8
        b.cc    L5750
        add     x10, x0, x8
        add     x11, x3, x9
        add     x10, x10, #0x190
        cmp     x10, x11
        b.cs    L5804
        add     x10, x9, x8
        add     x10, x10, x0
        add     x10, x10, #0x190
        cmp     x10, x3
        b.ls    L5804
L5750:
        mov     x10, xzr
L5754:
        add     x12, x10, x8
        sub     x11, x9, x10
        add     x12, x12, x0
        add     x10, x3, x10
        add     x12, x12, #0x190
L5768:
        ldrb    w13, [x10], #1
        ldrb    w14, [x12]
        subs    x11, x11, #0x1
        eor     w13, w14, w13
        strb    w13, [x12], #1
        b.ne    L5768
L5780:
        cmp     w6, #0x8
        b.cc    L57b0
        add     x10, x0, x8
        add     x11, x10, #0x258
        add     x10, x4, x9
        cmp     x11, x10
        b.cs    L5814
        add     x10, x9, x8
        add     x10, x10, x0
        add     x10, x10, #0x258
        cmp     x10, x4
        b.ls    L5814
L57b0:
        mov     x10, xzr
L57b4:
        add     x11, x10, x8
        sub     x8, x9, x10
        add     x9, x11, x0
        add     x10, x4, x10
        add     x9, x9, #0x258
L57c8:
        ldrb    w11, [x10], #1
        ldrb    w12, [x9]
        subs    x8, x8, #0x1
        eor     w11, w12, w11
        strb    w11, [x9], #1
        b.ne    L57c8
L57e0:
        ret
L57e4:
        cmp     w6, #0x20
        b.cs    L5824
        mov     x10, xzr
        b       L586c
L57f4:
        cmp     w6, #0x20
        b.cs    L58a8
        mov     x10, xzr
        b       L58f0
L5804:
        cmp     w6, #0x20
        b.cs    L5930
        mov     x10, xzr
        b       L5978
L5814:
        cmp     w6, #0x20
        b.cs    L59b8
        mov     x10, xzr
        b       L59f4
L5824:
        and     x10, x9, #0xffffffe0
        add     x12, x8, x0
        add     x11, x1, #0x10
        add     x12, x12, #0x10
        mov     x13, x10
L5838:
        ldp     q0, q1, [x11, #-16]
        add     x11, x11, #0x20
        subs    x13, x13, #0x20
        ldp     q2, q3, [x12, #-16]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v3.16b, v1.16b
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L5838
        cmp     x10, x9
        b.eq    L56c0
        tst     x9, #0x18
        b.eq    L5698
L586c:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x12, x0, x13
        add     x11, x1, x13
        add     x12, x12, x8
        sub     x13, x13, x10
L5884:
        ldr     d0, [x11], #8
        ldr     d1, [x12]
        adds    x13, x13, #0x8
        eor     v0.8b, v1.8b, v0.8b
        str     d0, [x12], #8
        b.ne    L5884
        cmp     x10, x9
        b.eq    L56c0
        b       L5698
L58a8:
        and     x10, x9, #0xffffffe0
        add     x12, x8, x0
        add     x11, x2, #0x10
        add     x12, x12, #0xd8
        mov     x13, x10
L58bc:
        ldp     q0, q1, [x11, #-16]
        add     x11, x11, #0x20
        subs    x13, x13, #0x20
        ldp     q2, q3, [x12, #-16]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v3.16b, v1.16b
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L58bc
        cmp     x10, x9
        b.eq    L5720
        tst     x9, #0x18
        b.eq    L56f4
L58f0:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x12, x13, x8
        add     x11, x2, x13
        add     x12, x12, x0
        sub     x13, x13, x10
        add     x12, x12, #0xc8
L590c:
        ldr     d0, [x11], #8
        ldr     d1, [x12]
        adds    x13, x13, #0x8
        eor     v0.8b, v1.8b, v0.8b
        str     d0, [x12], #8
        b.ne    L590c
        cmp     x10, x9
        b.eq    L5720
        b       L56f4
L5930:
        and     x10, x9, #0xffffffe0
        add     x12, x8, x0
        add     x11, x3, #0x10
        add     x12, x12, #0x1a0
        mov     x13, x10
L5944:
        ldp     q0, q1, [x11, #-16]
        add     x11, x11, #0x20
        subs    x13, x13, #0x20
        ldp     q2, q3, [x12, #-16]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v3.16b, v1.16b
        stp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        b.ne    L5944
        cmp     x10, x9
        b.eq    L5780
        tst     x9, #0x18
        b.eq    L5754
L5978:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x12, x13, x8
        add     x11, x3, x13
        add     x12, x12, x0
        sub     x13, x13, x10
        add     x12, x12, #0x190
L5994:
        ldr     d0, [x11], #8
        ldr     d1, [x12]
        adds    x13, x13, #0x8
        eor     v0.8b, v1.8b, v0.8b
        str     d0, [x12], #8
        b.ne    L5994
        cmp     x10, x9
        b.eq    L5780
        b       L5754
L59b8:
        and     x10, x9, #0xffffffe0
        add     x12, x4, #0x10
        mov     x13, x10
L59c4:
        ldp     q0, q1, [x12, #-16]
        add     x12, x12, #0x20
        subs    x13, x13, #0x20
        ldp     q2, q3, [x11]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v3.16b, v1.16b
        stp     q0, q1, [x11], #32
        b.ne    L59c4
        cmp     x10, x9
        b.eq    L57e0
        tst     x9, #0x18
        b.eq    L57b4
L59f4:
        mov     x13, x10
        and     x10, x9, #0xfffffff8
        add     x12, x13, x8
        add     x11, x4, x13
        add     x12, x12, x0
        sub     x13, x13, x10
        add     x12, x12, #0x258
L5a10:
        ldr     d0, [x11], #8
        ldr     d1, [x12]
        adds    x13, x13, #0x8
        eor     v0.8b, v1.8b, v0.8b
        str     d0, [x12], #8
        b.ne    L5a10
        cmp     x10, x9
        b.eq    L57e0
        b       L57b4

// mlkem_keccakf1600x4_permute (0x28 bytes)
L5a34:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L5a5c
        add     x0, x19, #0xc8
        bl      L5a5c
        add     x0, x19, #0x190
        bl      L5a5c
        add     x0, x19, #0x258
        ldp     x30, x19, [sp], #16
        b       L5a5c

// mlkem_keccakf1600_permute (0x534 bytes)
L5a5c:
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
L5ac0:
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
        .inst   0xd0000030  // adrp x16, 0xb000
        add     x16, x16, #0x2b0
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
        b.cc    L5ac0
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
L5f90:
        stp     x29, x30, [sp, #-32]!
        stp     x28, x19, [sp, #16]
        mov     x29, sp
        sub     x9, sp, #0x120
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd00000c8  // adrp x8, 0x1f000
        cmp     w2, #0x0
        cset    w9, eq
        mov     w10, #0x101
        add     x2, x0, #0x400
        add     x3, x0, #0x600
        ldr     x8, [x8, #4088]
        mov     x4, sp
        mov     x19, sp
        ldr     x8, [x8]
        str     x8, [sp, #280]
        cset    w8, ne
        ldp     q0, q1, [x1]
        add     x1, x0, #0x200
        strb    w9, [sp, #96]
        strb    w8, [sp, #97]
        strb    w8, [sp, #160]
        strb    w9, [sp, #161]
        strh    w10, [sp, #224]
        stp     q0, q1, [sp]
        stp     q0, q1, [sp, #64]
        stp     q0, q1, [sp, #128]
        stp     q0, q1, [sp, #192]
        strh    wzr, [sp, #32]
        bl      L8750
        movi    v0.2d, #0x0
        .inst   0xb00000c8  // adrp x8, 0x1f000
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
        b.ne    L6054
        mov     sp, x29
        ldp     x28, x19, [sp, #16]
        ldp     x29, x30, [sp], #32
        ret
L6054:
        bl      L0830

// mlkem512_indcpa_keypair_derand (0x2dc bytes)
L6058:
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
        .inst   0xb00000c8  // adrp x8, 0x1f000
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
        bl      L4c48
        add     x26, sp, #0xe20
        ldr     q0, [sp, #5728]
        add     x21, x26, #0x400
        ldr     q1, [sp, #5744]
        mov     w8, #0x1
        mov     w9, #0x100
        mov     w10, #0x101
        add     x1, x26, #0x200
        add     x3, x26, #0x600
        add     x0, sp, #0xe20
        add     x4, sp, #0xa20
        mov     x2, x21
        str     q0, [sp, #2592]
        add     x27, sp, #0xa20
        str     q1, [sp, #2608]
        str     q0, [sp, #2656]
        str     q1, [sp, #2672]
        str     q0, [sp, #2720]
        str     q1, [sp, #2736]
        strh    w8, [sp, #2688]
        strh    w9, [sp, #2752]
        strh    w10, [sp, #2816]
        str     q1, [sp, #2800]
        str     q0, [sp, #2784]
        strh    wzr, [sp, #2624]
        bl      L8750
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
        bl      L83e8
        add     x0, sp, #0x220
        bl      L8188
        add     x0, sp, #0xa20
        bl      L8188
        add     x0, sp, #0x20
        add     x1, sp, #0x220
        add     x25, sp, #0x20
        bl      L8368
        add     x0, sp, #0x620
        add     x1, sp, #0xe20
        add     x2, sp, #0x220
        add     x3, sp, #0x20
        add     x22, sp, #0x620
        bl      L81b8
        add     x0, x22, #0x200
        add     x2, sp, #0x220
        add     x3, sp, #0x20
        mov     x1, x21
        bl      L81b8
        add     x0, sp, #0x620
        bl      L83d0
        add     x0, sp, #0x620
        add     x1, sp, #0xa20
        bl      L83a8
        add     x0, sp, #0x620
        bl      L8390
        add     x0, sp, #0x220
        bl      L8390
        add     x1, sp, #0x220
        mov     x0, x20
        bl      L8138
        add     x1, sp, #0x620
        mov     x0, x19
        bl      L8138
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
        .inst   0xb00000c8  // adrp x8, 0x1f000
        str     q0, [sp, #5776]
        str     q0, [sp, #5760]
        str     q0, [sp, #5744]
        str     q0, [sp, #5728]
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #5816]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L6330
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L6330:
        bl      L0830

// mlkem512_indcpa_enc (0x48c bytes)
L6334:
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
        .inst   0xb00000c8  // adrp x8, 0x1f000
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
        bl      L8160
        ldp     q0, q1, [x21, #768]
        add     x0, sp, #0x420
        mov     x1, x22
        add     x25, sp, #0x420
        str     q0, [sp, #8224]
        str     q1, [sp, #8240]
        bl      L413c
        add     x22, sp, #0x1, lsl #12
        add     x0, sp, #0x1, lsl #12
        add     x22, x22, #0x820
        add     x4, sp, #0x1, lsl #12
        add     x21, x22, #0x400
        ldr     q0, [sp, #8224]
        ldr     q1, [sp, #8240]
        mov     w8, #0x100
        mov     w9, #0x1
        mov     w10, #0x101
        add     x1, x22, #0x200
        add     x3, x22, #0x600
        add     x0, x0, #0x820
        add     x4, x4, #0x420
        mov     x2, x21
        add     x24, sp, #0x1, lsl #12
        str     q0, [sp, #5152]
        add     x24, x24, #0x420
        str     q1, [sp, #5168]
        str     q0, [sp, #5216]
        str     q1, [sp, #5232]
        str     q0, [sp, #5280]
        str     q1, [sp, #5296]
        strh    w8, [sp, #5248]
        strh    w9, [sp, #5312]
        strh    w10, [sp, #5376]
        str     q1, [sp, #5360]
        str     q0, [sp, #5344]
        strh    wzr, [sp, #5184]
        bl      L8750
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
        bl      L85f4
        add     x0, sp, #0x220
        mov     x1, x20
        mov     w2, #0x4
        add     x27, sp, #0x220
        bl      L8548
        add     x0, sp, #0x1, lsl #12
        add     x0, x0, #0x420
        bl      L8188
        add     x1, sp, #0x1, lsl #12
        add     x0, sp, #0x20
        add     x1, x1, #0x420
        add     x28, sp, #0x20
        bl      L8368
        add     x1, sp, #0x1, lsl #12
        add     x2, sp, #0x1, lsl #12
        add     x0, sp, #0x820
        add     x1, x1, #0x820
        add     x2, x2, #0x420
        add     x3, sp, #0x20
        add     x20, sp, #0x820
        bl      L81b8
        add     x2, sp, #0x1, lsl #12
        add     x0, x20, #0x200
        add     x2, x2, #0x420
        add     x3, sp, #0x20
        mov     x1, x21
        bl      L81b8
        add     x1, sp, #0x1, lsl #12
        add     x2, sp, #0x1, lsl #12
        add     x0, sp, #0x620
        add     x1, x1, #0x20
        add     x2, x2, #0x420
        add     x3, sp, #0x20
        add     x21, sp, #0x620
        bl      L81b8
        add     x0, sp, #0x820
        bl      L81a0
        add     x0, sp, #0x620
        bl      L7e1c
        add     x0, sp, #0x820
        add     x1, sp, #0xc20
        bl      L83a8
        add     x0, sp, #0x620
        add     x1, sp, #0x220
        bl      L7384
        add     x0, sp, #0x620
        add     x1, sp, #0x420
        bl      L7384
        add     x0, sp, #0x820
        bl      L8390
        add     x0, sp, #0x620
        bl      L7334
        add     x1, sp, #0x820
        mov     x0, x19
        bl      L80e8
        add     x0, x19, #0x280
        add     x1, sp, #0x620
        bl      L262c
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
        .inst   0xb00000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #8280]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L67bc
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L67bc:
        bl      L0830

// mlkem512_indcpa_dec (0x220 bytes)
L67c0:
        stp     x29, x30, [sp, #-80]!
        str     x28, [sp, #16]
        stp     x24, x23, [sp, #32]
        stp     x22, x21, [sp, #48]
        stp     x20, x19, [sp, #64]
        mov     x29, sp
        sub     x9, sp, #0xe10
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb00000c8  // adrp x8, 0x1f000
        mov     x21, x0
        add     x0, sp, #0xa00
        mov     x19, x2
        mov     x20, x1
        add     x22, sp, #0xa00
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #3592]
        bl      L8110
        add     x1, x20, #0x280
        add     x0, sp, #0x400
        add     x20, sp, #0x400
        bl      L2c78
        add     x0, sp, #0x600
        mov     x1, x19
        add     x19, sp, #0x600
        bl      L8160
        add     x0, sp, #0xa00
        bl      L8188
        mov     x0, sp
        add     x1, sp, #0xa00
        mov     x24, sp
        bl      L8368
        add     x0, sp, #0x200
        add     x1, sp, #0x600
        add     x2, sp, #0xa00
        mov     x3, sp
        add     x23, sp, #0x200
        bl      L81b8
        add     x0, sp, #0x200
        bl      L7e1c
        add     x0, sp, #0x400
        add     x1, sp, #0x200
        bl      L7504
        add     x0, sp, #0x400
        bl      L7334
        add     x1, sp, #0x400
        mov     x0, x21
        bl      L421c
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
        .inst   0xb00000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #3592]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L69dc
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #64]
        ldp     x22, x21, [sp, #48]
        ldp     x24, x23, [sp, #32]
        ldr     x28, [sp, #16]
        ldp     x29, x30, [sp], #80
        ret
L69dc:
        bl      L0830

// mlkem512_check_pk (0x150 bytes)
L69e0:
        stp     x29, x30, [sp, #-48]!
        stp     x28, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0x710
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb00000c8  // adrp x8, 0x1f000
        mov     x19, x0
        add     x0, sp, #0x300
        mov     x1, x19
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #1800]
        bl      L8160
        add     x0, sp, #0x300
        bl      L8390
        mov     x0, sp
        add     x1, sp, #0x300
        mov     x20, sp
        bl      L8138
        movi    v0.2d, #0x0
        mov     x8, xzr
        movi    v1.2d, #0x0
        movi    v2.2d, #0x0
        movi    v3.2d, #0x0
L6a44:
        add     x9, x19, x8
        add     x10, x20, x8
        add     x8, x8, #0x20
        cmp     x8, #0x300
        ldp     q4, q5, [x9]
        ldp     q6, q7, [x10]
        eor     v4.16b, v6.16b, v4.16b
        orr     v2.16b, v4.16b, v2.16b
        eor     v5.16b, v7.16b, v5.16b
        orr     v3.16b, v5.16b, v3.16b
        eor     v0.16b, v4.16b, v0.16b
        eor     v1.16b, v5.16b, v1.16b
        b.ne    L6a44
        orr     v2.16b, v3.16b, v2.16b
        mov     w20, wzr
        ext     v3.16b, v2.16b, v2.16b, #8
        mov     x0, sp
        eor     v0.16b, v1.16b, v0.16b
        mov     w1, w20
        mov     w2, #0x300
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
        add     x0, sp, #0x300
        mov     w1, w20
        mov     w2, #0x400
        add     x20, sp, #0x300
        bl      L0840
        .inst   0xb00000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #1800]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L6b2c
        mov     w0, w19
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldp     x28, x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L6b2c:
        bl      L0830

// mlkem512_check_sk (0xe0 bytes)
L6b30:
        stp     x29, x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x29, sp
        sub     x9, sp, #0x40
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb00000c8  // adrp x8, 0x1f000
        mov     x19, x0
        add     x1, x0, #0x300
        mov     x0, sp
        mov     w2, #0x320
        mov     x20, sp
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #56]
        bl      L4ba4
        ldp     q2, q3, [sp]
        mov     w8, wzr
        ldr     q0, [x19, #1568]
        ldr     q1, [x19, #1584]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v3.16b, v1.16b
        orr     v2.16b, v1.16b, v0.16b
        ext     v3.16b, v2.16b, v2.16b, #8
        eor     v0.16b, v1.16b, v0.16b
        orr     v1.8b, v2.8b, v3.8b
        ext     v2.16b, v0.16b, v0.16b, #8
        fmov    x9, d1
        orr     x9, x9, x9, lsr #32
        eor     v0.8b, v0.8b, v2.8b
        lsr     x10, x9, #16
        fmov    x11, d0
        orr     w9, w9, w10
        movi    v0.2d, #0x0
        orr     w9, w9, w9, lsr #8
        eor     x10, x11, x11, lsr #32
        sub     w9, w8, w9, uxtb
        eor     x10, x10, x10, lsr #16
        lsr     x11, x10, #8
        eor     w10, w10, w11
        .inst   0xb00000cb  // adrp x11, 0x1f000
        eor     w9, w10, w9, lsr #16
        stp     q0, q0, [sp]
        and     w9, w9, #0xff
        ldr     x11, [x11, #4088]
        cmp     w9, w10, uxtb
        ldr     x12, [sp, #56]
        mov     w9, #0xfffffffb
        csel    w0, w8, w9, eq
        ldr     x11, [x11]
        cmp     x11, x12
        b.ne    L6c0c
        mov     sp, x29
        ldp     x20, x19, [sp, #16]
        ldp     x29, x30, [sp], #32
        ret
L6c0c:
        bl      L0830

// mlkem512_keypair_derand (0x88 bytes)
L6c10:
        str     x30, [sp, #-48]!
        stp     x22, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x22, x2
        mov     x19, x1
        mov     x21, x0
        bl      L6058
        mov     w20, w0
        cbz     w0, L6c58
        mov     x0, x21
        mov     w1, wzr
        mov     w2, #0x320
        bl      L0840
        mov     x0, x19
        mov     w1, wzr
        mov     w2, #0x660
        bl      L0840
        b       L6c84
L6c58:
        add     x0, x19, #0x300
        mov     x1, x21
        mov     w2, #0x320
        bl      L0810
        add     x0, x19, #0x620
        mov     x1, x21
        mov     w2, #0x320
        bl      L4ba4
        ldp     q1, q0, [x22, #32]
        str     q1, [x19, #1600]
        str     q0, [x19, #1616]
L6c84:
        mov     w0, w20
        ldp     x20, x19, [sp, #32]
        ldp     x22, x21, [sp, #16]
        ldr     x30, [sp], #48
        ret

// mlkem512_keypair (0xf4 bytes)
L6c98:
        stp     x29, x30, [sp, #-48]!
        str     x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0x50
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb00000c8  // adrp x8, 0x1f000
        mov     x19, x1
        mov     x21, x0
        mov     x0, sp
        mov     w1, #0x40
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #72]
        bl      L0820
        cbz     w0, L6ce0
        mov     w20, #0xfffffffd
        b       L6d48
L6ce0:
        mov     x2, sp
        mov     x0, x21
        mov     x1, x19
        bl      L6058
        mov     w20, w0
        cbz     w0, L6d1c
        mov     x0, x21
        mov     w1, wzr
        mov     w2, #0x320
        bl      L0840
        mov     x0, x19
        mov     w1, wzr
        mov     w2, #0x660
        bl      L0840
        b       L6d48
L6d1c:
        add     x0, x19, #0x300
        mov     x1, x21
        mov     w2, #0x320
        bl      L0810
        add     x0, x19, #0x620
        mov     x1, x21
        mov     w2, #0x320
        bl      L4ba4
        ldp     q0, q1, [sp, #32]
        str     q0, [x19, #1600]
        str     q1, [x19, #1616]
L6d48:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        .inst   0xb00000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #72]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L6d88
        mov     w0, w20
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldr     x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L6d88:
        bl      L0830

// mlkem512_enc_derand (0x1d8 bytes)
L6d8c:
        stp     x29, x30, [sp, #-96]!
        str     x28, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0x720
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb00000c8  // adrp x8, 0x1f000
        mov     x19, x1
        mov     x21, x0
        add     x0, sp, #0x300
        mov     x1, x2
        mov     x22, x3
        ldr     x8, [x8, #4088]
        mov     x20, x2
        ldr     x8, [x8]
        str     x8, [sp, #1816]
        bl      L8160
        add     x0, sp, #0x300
        bl      L8390
        mov     x0, sp
        add     x1, sp, #0x300
        mov     x23, sp
        bl      L8138
        movi    v0.2d, #0x0
        mov     x8, xzr
        movi    v1.2d, #0x0
        movi    v2.2d, #0x0
        movi    v3.2d, #0x0
L6e08:
        add     x9, x20, x8
        add     x10, x23, x8
        add     x8, x8, #0x20
        cmp     x8, #0x300
        ldp     q4, q5, [x9]
        ldp     q6, q7, [x10]
        eor     v4.16b, v6.16b, v4.16b
        orr     v2.16b, v4.16b, v2.16b
        eor     v5.16b, v7.16b, v5.16b
        orr     v3.16b, v5.16b, v3.16b
        eor     v0.16b, v4.16b, v0.16b
        eor     v1.16b, v5.16b, v1.16b
        b.ne    L6e08
        orr     v2.16b, v3.16b, v2.16b
        mov     w23, wzr
        ext     v3.16b, v2.16b, v2.16b, #8
        mov     x0, sp
        eor     v0.16b, v1.16b, v0.16b
        mov     w1, wzr
        mov     w2, #0x300
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
        add     x0, sp, #0x300
        mov     w1, wzr
        mov     w2, #0x400
        add     x23, sp, #0x300
        bl      L0840
        cmp     w26, w25, uxtb
        b.ne    L6f08
        ldp     q0, q1, [x22]
        add     x0, x23, #0x20
        mov     x1, x20
        mov     w2, #0x320
        stp     q0, q1, [sp, #768]
        bl      L4ba4
        mov     x0, sp
        add     x1, sp, #0x300
        mov     w2, #0x40
        bl      L4c48
        add     x3, x24, #0x20
        add     x1, sp, #0x300
        mov     x0, x21
        mov     x2, x20
        bl      L6334
        cbnz    w0, L6f0c
        ldp     q0, q1, [sp]
        stp     q0, q1, [x19]
        b       L6f0c
L6f08:
        mov     w0, #0xfffffffc
L6f0c:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        stp     q0, q0, [sp, #800]
        add     x8, sp, #0x300
        stp     q0, q0, [sp, #768]
        .inst   0xb00000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #1816]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L6f60
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldr     x28, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L6f60:
        bl      L0830

// mlkem512_enc (0x9c bytes)
L6f64:
        stp     x29, x30, [sp, #-48]!
        str     x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0x30
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb00000c8  // adrp x8, 0x1f000
        mov     x20, x1
        mov     x21, x0
        mov     x0, sp
        mov     w1, #0x20
        mov     x19, x2
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #40]
        bl      L0820
        cbz     w0, L6fb0
        mov     w0, #0xfffffffd
        b       L6fc4
L6fb0:
        mov     x3, sp
        mov     x0, x21
        mov     x1, x20
        mov     x2, x19
        bl      L6d8c
L6fc4:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        .inst   0xb00000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #40]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L6ffc
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldr     x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L6ffc:
        bl      L0830

// mlkem512_dec (0x2a0 bytes)
L7000:
        stp     x29, x30, [sp, #-64]!
        stp     x28, x23, [sp, #16]
        stp     x22, x21, [sp, #32]
        stp     x20, x19, [sp, #48]
        mov     x29, sp
        sub     x9, sp, #0x3c0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0x900000c8  // adrp x8, 0x1f000
        add     x22, x2, #0x300
        mov     x21, x2
        mov     x20, x1
        mov     x19, x0
        mov     x0, sp
        ldr     x8, [x8, #4088]
        mov     x1, x22
        mov     w2, #0x320
        mov     x23, sp
        ldr     x8, [x8]
        str     x8, [sp, #952]
        bl      L4ba4
        ldp     q2, q3, [sp]
        mov     w8, wzr
        ldr     q0, [x21, #1568]
        ldr     q1, [x21, #1584]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v3.16b, v1.16b
        orr     v2.16b, v1.16b, v0.16b
        ext     v3.16b, v2.16b, v2.16b, #8
        eor     v0.16b, v1.16b, v0.16b
        orr     v1.8b, v2.8b, v3.8b
        ext     v2.16b, v0.16b, v0.16b, #8
        fmov    x9, d1
        orr     x9, x9, x9, lsr #32
        eor     v0.8b, v0.8b, v2.8b
        lsr     x10, x9, #16
        orr     w9, w9, w10
        fmov    x10, d0
        movi    v0.2d, #0x0
        orr     w9, w9, w9, lsr #8
        eor     x10, x10, x10, lsr #32
        sub     w8, w8, w9, uxtb
        eor     x9, x10, x10, lsr #16
        lsr     x10, x9, #8
        eor     w9, w9, w10
        eor     w8, w9, w8, lsr #16
        stp     q0, q0, [sp]
        and     w8, w8, #0xff
        cmp     w8, w9, uxtb
        b.ne    L7234
        add     x0, sp, #0x360
        mov     x1, x20
        mov     x2, x21
        bl      L67c0
        mov     w23, w0
        cbnz    w0, L7238
        add     x8, x21, #0x620
        add     x0, sp, #0x320
        add     x1, sp, #0x360
        mov     w2, #0x40
        add     x23, sp, #0x320
        ldp     q0, q1, [x8]
        stp     q0, q1, [sp, #896]
        bl      L4c48
        add     x3, x23, #0x20
        mov     x0, sp
        add     x1, sp, #0x360
        mov     x2, x22
        mov     x22, sp
        bl      L6334
        mov     w23, w0
        cbnz    w0, L7238
        movi    v0.2d, #0x0
        mov     x8, xzr
        movi    v1.2d, #0x0
        movi    v2.2d, #0x0
        movi    v3.2d, #0x0
L7130:
        add     x9, x20, x8
        add     x10, x22, x8
        add     x8, x8, #0x20
        cmp     x8, #0x300
        ldp     q4, q5, [x9]
        ldp     q6, q7, [x10]
        eor     v4.16b, v6.16b, v4.16b
        orr     v2.16b, v4.16b, v2.16b
        eor     v5.16b, v7.16b, v5.16b
        orr     v3.16b, v5.16b, v3.16b
        eor     v0.16b, v4.16b, v0.16b
        eor     v1.16b, v5.16b, v1.16b
        b.ne    L7130
        orr     v2.16b, v3.16b, v2.16b
        mov     w22, wzr
        ext     v3.16b, v2.16b, v2.16b, #8
        mov     x8, sp
        eor     v0.16b, v1.16b, v0.16b
        add     x0, x8, #0x20
        ext     v1.16b, v0.16b, v0.16b, #8
        mov     x1, x20
        mov     w2, #0x300
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
        ldr     q0, [x21, #1600]
        ldr     q1, [x21, #1616]
        eor     w21, w9, w10
        stp     q0, q1, [sp]
        bl      L0810
        add     x0, sp, #0x360
        mov     x2, sp
        mov     w1, #0x20
        mov     w3, #0x320
        add     x20, sp, #0x360
        bl      L4ad0
        mov     x8, xzr
        sub     w9, w22, w21, uxtb
        add     x10, sp, #0x320
L71f8:
        ldrb    w11, [x20, x8]
        mov     w12, w9
        ldrb    w13, [x10, x8]
        lsr     w12, w12, #16
        and     w11, w11, w12
        bic     w13, w13, w12
        orr     w11, w11, w13
        strb    w11, [x20, x8]
        add     x8, x8, #0x1
        cmp     x8, #0x20
        b.ne    L71f8
        ldp     q0, q1, [sp, #864]
        mov     w23, wzr
        stp     q0, q1, [x19]
        b       L7238
L7234:
        mov     w23, #0xfffffffb
L7238:
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
        .inst   0x900000c8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #952]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L729c
        mov     w0, w23
        mov     sp, x29
        ldp     x20, x19, [sp, #48]
        ldp     x22, x21, [sp, #32]
        ldp     x28, x23, [sp, #16]
        ldp     x29, x30, [sp], #64
        ret
L729c:
        bl      L0830

// mlkem_poly_tomont (0x94 bytes)
L72a0:
        mov     w9, #0x549
        mov     w10, #0x50490000
        mov     x8, xzr
        mvni    v2.4s, #0xd, lsl #8
        dup     v0.8h, w9
        dup     v1.4s, w10
L72b8:
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
        b.ne    L72b8
        ret

// mlkem_poly_reduce (0x50 bytes)
L7334:
        mov     x8, xzr
        mov     w9, #0x4ebf
        mov     w10, #0x2000000
        mov     w11, #0xfffff2ff
L7344:
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
        b.ne    L7344
        ret

// mlkem_poly_add (0x180 bytes)
L7384:
        add     x8, x1, #0x200
        cmp     x8, x0
        b.ls    L73c0
        add     x8, x0, #0x200
        cmp     x8, x1
        b.ls    L73c0
        mov     x8, xzr
L73a0:
        ldrh    w9, [x0, x8]
        ldrh    w10, [x1, x8]
        add     w9, w10, w9
        strh    w9, [x0, x8]
        add     x8, x8, #0x2
        cmp     x8, #0x200
        b.ne    L73a0
        ret
L73c0:
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
L7504:
        add     x8, x1, #0x200
        cmp     x8, x0
        b.ls    L7540
        add     x8, x0, #0x200
        cmp     x8, x1
        b.ls    L7540
        mov     x8, xzr
L7520:
        ldrh    w9, [x0, x8]
        ldrh    w10, [x1, x8]
        sub     w9, w9, w10
        strh    w9, [x0, x8]
        add     x8, x8, #0x2
        cmp     x8, #0x200
        b.ne    L7520
        ret
L7540:
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
L7684:
        add     x8, x1, #0x2
        add     x9, x1, #0x200
        cmp     x9, x0
        b.ls    L76a8
        add     x9, x0, #0x100
        cmp     x8, x9
        b.cs    L76a8
        mov     x11, xzr
        b       L7bb0
L76a8:
        ld4     {v1.8h-v4.8h}, [x8]
        .inst   0x90000028  // adrp x8, 0xb000
        .inst   0x90000029  // adrp x9, 0xb000
        .inst   0xf000000b  // adrp x11, 0xa000
        .inst   0xf000000a  // adrp x10, 0xa000
        mvni    v0.4s, #0xd, lsl #8
        ldr     d5, [x8, #432]
        .inst   0x90000028  // adrp x8, 0xb000
        ldr     d6, [x9, #440]
        .inst   0xf0000009  // adrp x9, 0xa000
        ldr     q7, [x11, #3936]
        .inst   0xf000000b  // adrp x11, 0xa000
        ldr     d16, [x8, #456]
        .inst   0x90000028  // adrp x8, 0xb000
        sxtl    v17.4s, v1.4h
        ldr     q23, [x10, #3920]
        sxtl2   v18.4s, v1.8h
        .inst   0x9000002a  // adrp x10, 0xb000
        ext     v19.16b, v1.16b, v1.16b, #8
        smull   v6.4s, v1.4h, v6.4h
        sxtl    v20.4s, v3.4h
        sxtl2   v21.4s, v3.8h
        ext     v22.16b, v3.16b, v3.16b, #8
        smull   v1.4s, v3.4h, v16.4h
        ldr     q4, [x11, #3968]
        mul     v3.4s, v17.4s, v7.4s
        ldr     q2, [x9, #3952]
        mul     v7.4s, v18.4s, v23.4s
        ldr     d16, [x8, #448]
        mul     v4.4s, v20.4s, v4.4s
        mov     x8, x0
        mul     v2.4s, v21.4s, v2.4s
        add     x9, x1, #0x42
        sshr    v3.4s, v3.4s, #16
        .inst   0xf000000b  // adrp x11, 0xa000
        sshr    v7.4s, v7.4s, #16
        mul     v3.4s, v3.4s, v0.4s
        sshr    v4.4s, v4.4s, #16
        smull   v5.4s, v19.4h, v5.4h
        mul     v7.4s, v7.4s, v0.4s
        mul     v4.4s, v4.4s, v0.4s
        addhn   v17.4h, v3.4s, v6.4s
        ldr     d6, [x10, #472]
        sshr    v2.4s, v2.4s, #16
        .inst   0x9000002a  // adrp x10, 0xb000
        smull   v3.4s, v22.4h, v16.4h
        mul     v2.4s, v2.4s, v0.4s
        addhn2  v17.8h, v7.4s, v5.4s
        ldr     q7, [x11, #3984]
        addhn   v18.4h, v4.4s, v1.4s
        .inst   0xf000000b  // adrp x11, 0xa000
        addhn2  v18.8h, v2.4s, v3.4s
        st2     {v17.8h-v18.8h}, [x8], #32
        ld4     {v1.8h-v4.8h}, [x9]
        .inst   0x90000029  // adrp x9, 0xb000
        ldr     d5, [x9, #464]
        .inst   0xf0000009  // adrp x9, 0xa000
        ldr     d17, [x10, #488]
        .inst   0xf000000a  // adrp x10, 0xa000
        ldr     q18, [x11, #4016]
        mov     w11, #0x38
        ldr     q16, [x9, #4000]
        .inst   0xf0000009  // adrp x9, 0xa000
        sxtl    v19.4s, v1.4h
        sxtl2   v20.4s, v1.8h
        ext     v21.16b, v1.16b, v1.16b, #8
        smull   v6.4s, v1.4h, v6.4h
        sxtl    v22.4s, v3.4h
        sxtl2   v23.4s, v3.8h
        smull   v17.4s, v3.4h, v17.4h
        ext     v1.16b, v3.16b, v3.16b, #8
        ldr     q2, [x9, #4032]
        mul     v3.4s, v19.4s, v16.4s
        .inst   0x90000029  // adrp x9, 0xb000
        mul     v4.4s, v20.4s, v7.4s
        mul     v2.4s, v22.4s, v2.4s
        mul     v7.4s, v23.4s, v18.4s
        ldr     d16, [x9, #480]
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
        ldr     q7, [x10, #4048]
        addhn2  v18.8h, v4.4s, v5.4s
        .inst   0xf000000a  // adrp x10, 0xa000
        addhn   v19.4h, v2.4s, v17.4s
        addhn2  v19.8h, v3.4s, v1.4s
        st2     {v18.8h-v19.8h}, [x8]
        .inst   0x90000028  // adrp x8, 0xb000
        ld4     {v1.8h-v4.8h}, [x9]
        .inst   0x90000029  // adrp x9, 0xb000
        ldr     d5, [x8, #496]
        .inst   0xf0000008  // adrp x8, 0xa000
        ldr     d6, [x9, #504]
        .inst   0x90000029  // adrp x9, 0xb000
        ldr     q18, [x10, #4080]
        .inst   0x9000002a  // adrp x10, 0xb000
        ldr     q16, [x8, #4064]
        .inst   0x90000028  // adrp x8, 0xb000
        ldr     d17, [x9, #520]
        add     x9, x1, #0xc2
        sxtl    v19.4s, v1.4h
        sxtl2   v20.4s, v1.8h
        ext     v21.16b, v1.16b, v1.16b, #8
        smull   v6.4s, v1.4h, v6.4h
        sxtl    v22.4s, v3.4h
        sxtl2   v23.4s, v3.8h
        smull   v17.4s, v3.4h, v17.4h
        ext     v1.16b, v3.16b, v3.16b, #8
        ldr     q2, [x8]
        mul     v3.4s, v19.4s, v16.4s
        .inst   0x90000028  // adrp x8, 0xb000
        mul     v4.4s, v20.4s, v7.4s
        mul     v2.4s, v22.4s, v2.4s
        mul     v7.4s, v23.4s, v18.4s
        ldr     d16, [x8, #512]
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
        ldr     q7, [x10, #16]
        addhn2  v18.8h, v4.4s, v5.4s
        .inst   0x9000002a  // adrp x10, 0xb000
        addhn   v19.4h, v2.4s, v17.4s
        addhn2  v19.8h, v3.4s, v1.4s
        st2     {v18.8h-v19.8h}, [x8]
        .inst   0x90000028  // adrp x8, 0xb000
        ld4     {v1.8h-v4.8h}, [x9]
        .inst   0x90000029  // adrp x9, 0xb000
        ldr     d5, [x8, #528]
        .inst   0x90000028  // adrp x8, 0xb000
        ldr     d6, [x9, #536]
        .inst   0x90000029  // adrp x9, 0xb000
        ldr     q18, [x10, #48]
        .inst   0x9000002a  // adrp x10, 0xb000
        ldr     q16, [x8, #32]
        .inst   0x90000028  // adrp x8, 0xb000
        ldr     d17, [x9, #552]
        add     x9, x1, #0x102
        sxtl    v19.4s, v1.4h
        sxtl2   v20.4s, v1.8h
        ext     v21.16b, v1.16b, v1.16b, #8
        smull   v6.4s, v1.4h, v6.4h
        sxtl    v22.4s, v3.4h
        sxtl2   v23.4s, v3.8h
        smull   v17.4s, v3.4h, v17.4h
        ext     v1.16b, v3.16b, v3.16b, #8
        ldr     q2, [x8, #64]
        mul     v3.4s, v19.4s, v16.4s
        .inst   0x90000028  // adrp x8, 0xb000
        mul     v4.4s, v20.4s, v7.4s
        mul     v2.4s, v22.4s, v2.4s
        mul     v7.4s, v23.4s, v18.4s
        ldr     d16, [x8, #544]
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
        ldr     q7, [x10, #80]
        addhn2  v18.8h, v4.4s, v5.4s
        .inst   0x9000002a  // adrp x10, 0xb000
        addhn   v19.4h, v2.4s, v17.4s
        addhn2  v19.8h, v3.4s, v1.4s
        st2     {v18.8h-v19.8h}, [x8]
        .inst   0x90000028  // adrp x8, 0xb000
        ld4     {v1.8h-v4.8h}, [x9]
        .inst   0x90000029  // adrp x9, 0xb000
        ldr     d5, [x8, #560]
        .inst   0x90000028  // adrp x8, 0xb000
        ldr     d6, [x9, #568]
        .inst   0x90000029  // adrp x9, 0xb000
        ldr     q18, [x10, #112]
        .inst   0x9000002a  // adrp x10, 0xb000
        ldr     q16, [x8, #96]
        .inst   0x90000028  // adrp x8, 0xb000
        ldr     d17, [x9, #584]
        add     x9, x1, #0x142
        sxtl    v19.4s, v1.4h
        sxtl2   v20.4s, v1.8h
        ext     v21.16b, v1.16b, v1.16b, #8
        smull   v6.4s, v1.4h, v6.4h
        sxtl    v22.4s, v3.4h
        sxtl2   v23.4s, v3.8h
        smull   v17.4s, v3.4h, v17.4h
        ext     v1.16b, v3.16b, v3.16b, #8
        ldr     q2, [x8, #128]
        mul     v3.4s, v19.4s, v16.4s
        .inst   0x90000028  // adrp x8, 0xb000
        mul     v4.4s, v20.4s, v7.4s
        mul     v2.4s, v22.4s, v2.4s
        mul     v7.4s, v23.4s, v18.4s
        ldr     d16, [x8, #576]
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
        ldr     q7, [x10, #144]
        addhn2  v18.8h, v4.4s, v5.4s
        .inst   0x9000002a  // adrp x10, 0xb000
        addhn   v19.4h, v2.4s, v17.4s
        addhn2  v19.8h, v3.4s, v1.4s
        st2     {v18.8h-v19.8h}, [x8]
        .inst   0x90000028  // adrp x8, 0xb000
        ld4     {v1.8h-v4.8h}, [x9]
        .inst   0x90000029  // adrp x9, 0xb000
        ldr     d5, [x8, #592]
        .inst   0x90000028  // adrp x8, 0xb000
        ldr     d6, [x9, #600]
        .inst   0x90000029  // adrp x9, 0xb000
        ldr     q16, [x8, #160]
        .inst   0x90000028  // adrp x8, 0xb000
        ldr     d17, [x9, #616]
        add     x9, x1, #0x182
        sxtl    v18.4s, v1.4h
        sxtl2   v19.4s, v1.8h
        ext     v20.16b, v1.16b, v1.16b, #8
        smull   v6.4s, v1.4h, v6.4h
        sxtl    v21.4s, v3.4h
        sxtl2   v22.4s, v3.8h
        smull   v17.4s, v3.4h, v17.4h
        ext     v1.16b, v3.16b, v3.16b, #8
        ldr     q4, [x8, #192]
        mul     v3.4s, v18.4s, v16.4s
        ldr     q2, [x10, #176]
        mul     v7.4s, v19.4s, v7.4s
        .inst   0x90000028  // adrp x8, 0xb000
        mul     v4.4s, v21.4s, v4.4s
        .inst   0x9000002a  // adrp x10, 0xb000
        mul     v2.4s, v22.4s, v2.4s
        sshr    v3.4s, v3.4s, #16
        ldr     d16, [x8, #608]
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
        ldr     d7, [x10, #648]
        addhn   v19.4h, v4.4s, v17.4s
        addhn2  v19.8h, v2.4s, v1.4s
        st2     {v18.8h-v19.8h}, [x8]
        .inst   0x90000028  // adrp x8, 0xb000
        ld4     {v1.8h-v4.8h}, [x9]
        .inst   0x90000029  // adrp x9, 0xb000
        ldr     d5, [x8, #632]
        .inst   0x90000028  // adrp x8, 0xb000
        ldr     q6, [x9, #224]
        .inst   0x90000029  // adrp x9, 0xb000
        sxtl    v16.4s, v1.4h
        sxtl2   v17.4s, v1.8h
        ext     v18.16b, v1.16b, v1.16b, #8
        smull   v5.4s, v1.4h, v5.4h
        sxtl    v19.4s, v3.4h
        sxtl2   v20.4s, v3.8h
        smull   v7.4s, v3.4h, v7.4h
        ext     v1.16b, v3.16b, v3.16b, #8
        ldr     q2, [x8, #208]
        mul     v3.4s, v16.4s, v6.4s
        .inst   0x90000028  // adrp x8, 0xb000
        ldr     q4, [x9, #256]
        .inst   0x90000029  // adrp x9, 0xb000
        mul     v2.4s, v17.4s, v2.4s
        ldr     q6, [x8, #240]
        .inst   0x90000028  // adrp x8, 0xb000
        mul     v4.4s, v19.4s, v4.4s
        sshr    v3.4s, v3.4s, #16
        ldr     d16, [x9, #624]
        mul     v3.4s, v3.4s, v0.4s
        sshr    v2.4s, v2.4s, #16
        mul     v6.4s, v20.4s, v6.4s
        ldr     d17, [x8, #640]
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
L7bb0:
        lsl     x9, x11, #1
        add     x10, x1, x11, lsl #3
        add     x11, x0, x11, lsl #2
        mov     w8, #0xf3010000
        add     x10, x10, #0x6
        add     x11, x11, #0x2
        mov     w12, #0xfffff2ff
        .inst   0x9000002d  // adrp x13, 0xb000
        add     x13, x13, #0x380
L7bd4:
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
        b.ne    L7bd4
        ret

// mlkem_poly_ntt (0x1ec bytes)
L7c30:
        stp     x28, x27, [sp, #-80]!
        stp     x26, x25, [sp, #16]
        stp     x24, x23, [sp, #32]
        stp     x22, x21, [sp, #48]
        stp     x20, x19, [sp, #64]
        mov     w10, #0xf3010000
        mov     w8, #0x1
        mov     w9, #0x100
        .inst   0x9000002b  // adrp x11, 0xb000
        add     x11, x11, #0x380
        mov     w12, #0xfffff2ff
        mov     w13, #0x1
        dup     v0.4s, w10
        mvni    v1.4s, #0xd, lsl #8
        b       L7c78
L7c6c:
        add     w13, w13, #0x1
        cmp     w13, #0x8
        b.eq    L7e04
L7c78:
        sub     w2, w13, #0x1
        lsr     w17, w9, w13
        ubfiz   x18, x17, #1, #32
        lsl     x4, x17, #63
        mov     x14, xzr
        mov     x15, xzr
        mov     x16, xzr
        ubfiz   x1, x17, #2, #32
        lsl     w2, w8, w2
        add     x3, x18, #0x2
        sub     x4, x4, x18
        neg     x5, x18
        add     x6, x0, x18
        mov     x7, x0
        mov     w19, #0x1
        mov     x20, x17
        b       L7ce0
L7cbc:
        add     w2, w2, #0x1
        add     x16, x16, x18
        add     x15, x15, #0x1
        add     x20, x20, x18
        add     x19, x19, x18
        sub     x14, x14, x18
        add     x7, x7, x1
        cmp     x16, #0x100
        b.cs    L7c6c
L7ce0:
        cmp     x20, x19
        add     x21, x16, x17
        orr     x26, x16, #0x1
        csel    x25, x20, x19, hi
        cmp     x21, x26
        mov     x24, x16
        csel    x22, x21, x26, hi
        madd    x23, x5, x15, x22
        ldrsh   w22, [x11, w2, uxtw #1]
        cmp     x23, #0x8
        b.cc    L7dc4
        cmp     x21, x26
        mul     x24, x1, x15
        csel    x26, x21, x26, hi
        add     x28, x0, x18
        madd    x26, x4, x15, x26
        orr     x27, x24, #0x2
        add     x27, x0, x27
        add     x28, x28, x24
        lsl     x26, x26, #1
        sub     x26, x26, #0x2
        add     x27, x27, x26
        cmp     x28, x27
        b.cs    L7d5c
        add     x27, x0, x3
        add     x28, x0, x24
        add     x24, x27, x24
        add     x26, x24, x26
        mov     x24, x16
        cmp     x28, x26
        b.cc    L7dc4
L7d5c:
        add     x24, x25, x14
        and     x25, x23, #0xfffffffffffffff8
        and     x26, x24, #0xfffffffffffffff8
        add     x24, x16, x25
        mov     x27, x7
L7d70:
        ldr     q2, [x27, x18]
        dup     v3.8h, w22
        subs    x26, x26, #0x8
        smull   v4.4s, v3.4h, v2.4h
        smull2  v2.4s, v3.8h, v2.8h
        mul     v3.4s, v4.4s, v0.4s
        mul     v5.4s, v2.4s, v0.4s
        sshr    v3.4s, v3.4s, #16
        sshr    v5.4s, v5.4s, #16
        mul     v3.4s, v3.4s, v1.4s
        mul     v5.4s, v5.4s, v1.4s
        addhn   v3.4h, v3.4s, v4.4s
        ldr     q4, [x27]
        addhn2  v3.8h, v5.4s, v2.4s
        sub     v2.8h, v4.8h, v3.8h
        add     v3.8h, v4.8h, v3.8h
        str     q2, [x27, x18]
        str     q3, [x27], #16
        b.ne    L7d70
        cmp     x23, x25
        b.eq    L7cbc
L7dc4:
        lsl     x23, x24, #1
        add     x24, x24, #0x1
        cmp     x24, x21
        ldrsh   w25, [x6, x23]
        ldrh    w27, [x0, x23]
        mul     w25, w25, w22
        mul     w26, w25, w10
        asr     w26, w26, #16
        madd    w25, w26, w12, w25
        lsr     w25, w25, #16
        sub     w26, w27, w25
        add     w25, w27, w25
        strh    w26, [x6, x23]
        strh    w25, [x0, x23]
        b.cc    L7dc4
        b       L7cbc
L7e04:
        ldp     x20, x19, [sp, #64]
        ldp     x22, x21, [sp, #48]
        ldp     x24, x23, [sp, #32]
        ldp     x26, x25, [sp, #16]
        ldp     x28, x27, [sp], #80
        ret

// mlkem_poly_invntt_tomont (0x2cc bytes)
L7e1c:
        mov     w9, #0x5a1
        mov     w10, #0xd8a10000
        mov     x8, xzr
        mvni    v2.4s, #0xd, lsl #8
        dup     v0.8h, w9
        dup     v1.4s, w10
L7e34:
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
        b.ne    L7e34
        stp     x29, x30, [sp, #-96]!
        stp     x28, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     w10, #0x4ebf
        mov     w12, #0xf3010000
        .inst   0x90000028  // adrp x8, 0xb000
        add     x8, x8, #0x380
        mov     w9, #0x7
        mov     w11, #0x100
        mov     w13, #0xffffffff
        mov     w14, #0x2000000
        mov     w15, #0xfffff2ff
        dup     v0.8h, w10
        dup     v2.4s, w12
        mvni    v1.8h, #0xd, lsl #8
        mvni    v3.4s, #0xd, lsl #8
        b       L7f04
L7efc:
        subs    w9, w9, #0x1
        b.eq    L80cc
L7f04:
        lsr     w1, w11, w9
        lsl     w2, w13, w9
        ubfiz   x3, x1, #1, #32
        lsl     x5, x1, #63
        mov     x16, xzr
        mov     x17, xzr
        mov     x18, xzr
        mvn     w2, w2
        ubfiz   x4, x1, #2, #32
        sub     x5, x5, x3
        add     x6, x3, #0x2
        neg     x7, x3
        add     x19, x0, x3
        mov     x20, x0
        mov     w21, #0x1
        mov     x22, x1
        b       L7f6c
L7f48:
        sub     w2, w2, #0x1
        add     x18, x18, x3
        add     x17, x17, #0x1
        add     x22, x22, x3
        add     x21, x21, x3
        sub     x16, x16, x3
        add     x20, x20, x4
        cmp     x18, #0x100
        b.cs    L7efc
L7f6c:
        cmp     x22, x21
        add     x23, x18, x1
        orr     x28, x18, #0x1
        csel    x27, x22, x21, hi
        cmp     x23, x28
        mov     x25, x18
        csel    x24, x23, x28, hi
        madd    x26, x7, x17, x24
        ldrsh   w24, [x8, w2, uxtw #1]
        cmp     x26, #0x8
        b.cc    L8074
        cmp     x23, x28
        add     x29, x0, x6
        csel    x25, x23, x28, hi
        madd    x28, x5, x17, x25
        mul     x25, x4, x17
        lsl     x28, x28, #1
        add     x29, x29, x25
        sub     x28, x28, #0x2
        add     x29, x29, x28
        add     x30, x0, x25
        cmp     x30, x29
        b.cs    L7fe8
        add     x29, x0, x3
        orr     x30, x25, #0x2
        add     x29, x29, x25
        add     x25, x0, x30
        add     x28, x25, x28
        mov     x25, x18
        cmp     x29, x28
        b.cc    L8074
L7fe8:
        add     x25, x27, x16
        and     x27, x26, #0xfffffffffffffff8
        and     x28, x25, #0xfffffffffffffff8
        add     x25, x18, x27
        mov     x29, x20
L7ffc:
        ldr     q5, [x29, x3]
        dup     v16.8h, w24
        ldr     q4, [x29]
        subs    x28, x28, #0x8
        movi    v6.4s, #0x2, lsl #24
        movi    v7.4s, #0x2, lsl #24
        sub     v17.8h, v5.8h, v4.8h
        add     v4.8h, v5.8h, v4.8h
        smull   v5.4s, v16.4h, v17.4h
        smlal   v6.4s, v4.4h, v0.4h
        smlal2  v7.4s, v4.8h, v0.8h
        smull2  v16.4s, v16.8h, v17.8h
        mul     v17.4s, v5.4s, v2.4s
        sshr    v6.4s, v6.4s, #26
        sshr    v7.4s, v7.4s, #26
        mul     v18.4s, v16.4s, v2.4s
        uzp1    v6.8h, v6.8h, v7.8h
        sshr    v7.4s, v17.4s, #16
        mul     v7.4s, v7.4s, v3.4s
        sshr    v17.4s, v18.4s, #16
        mla     v4.8h, v6.8h, v1.8h
        mul     v6.4s, v17.4s, v3.4s
        addhn   v5.4h, v7.4s, v5.4s
        str     q4, [x29]
        addhn2  v5.8h, v6.4s, v16.4s
        str     q5, [x29, x3]
        add     x29, x29, #0x10
        b.ne    L7ffc
        cmp     x26, x27
        b.eq    L7f48
L8074:
        lsl     x26, x25, #1
        add     x25, x25, #0x1
        cmp     x25, x23
        ldrh    w27, [x0, x26]
        ldrh    w28, [x19, x26]
        add     w28, w28, w27
        sxth    w29, w28
        madd    w29, w29, w10, w14
        asr     w29, w29, #26
        madd    w28, w29, w15, w28
        strh    w28, [x0, x26]
        ldrh    w28, [x19, x26]
        sub     w27, w28, w27
        sxth    w27, w27
        mul     w27, w27, w24
        mul     w28, w27, w12
        asr     w28, w28, #16
        madd    w27, w28, w15, w27
        lsr     w27, w27, #16
        strh    w27, [x19, x26]
        b.cc    L8074
        b       L7f48
L80cc:
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret

// mlkem512_polyvec_compress_du (0x28 bytes)
L80e8:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L2bdc
        add     x0, x20, #0x140
        add     x1, x19, #0x200
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L2bdc

// mlkem512_polyvec_decompress_du (0x28 bytes)
L8110:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L3044
        add     x0, x20, #0x200
        add     x1, x19, #0x140
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L3044

// mlkem512_polyvec_tobytes (0x28 bytes)
L8138:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L3bfc
        add     x0, x20, #0x180
        add     x1, x19, #0x200
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L3bfc

// mlkem512_polyvec_frombytes (0x28 bytes)
L8160:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L3e4c
        add     x0, x20, #0x200
        add     x1, x19, #0x180
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L3e4c

// mlkem512_polyvec_ntt (0x18 bytes)
L8188:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L7c30
        add     x0, x19, #0x200
        ldp     x30, x19, [sp], #16
        b       L7c30

// mlkem512_polyvec_invntt_tomont (0x18 bytes)
L81a0:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L7e1c
        add     x0, x19, #0x200
        ldp     x30, x19, [sp], #16
        b       L7e1c

// mlkem512_polyvec_basemul_acc_montgomery_cached (0x1b0 bytes)
L81b8:
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
        b.hi    L82c8
        tbnz    w8, #0, L82c8
        cbnz    w9, L82c8
        mov     w10, #0xf3010000
        mov     x8, xzr
        add     x9, x3, #0x100
        mvni    v1.4s, #0xd, lsl #8
        dup     v0.4s, w10
L8208:
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
        b.ne    L8208
        b       L8364
L82c8:
        mov     x8, xzr
        mov     w9, #0xf3010000
        add     x10, x3, #0x100
        mov     w11, #0xfffff2ff
L82d8:
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
        b.ne    L82d8
L8364:
        ret

// mlkem512_polyvec_mulcache_compute (0x28 bytes)
L8368:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L7684
        add     x0, x20, #0x100
        add     x1, x19, #0x200
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L7684

// mlkem512_polyvec_reduce (0x18 bytes)
L8390:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L7334
        add     x0, x19, #0x200
        ldp     x30, x19, [sp], #16
        b       L7334

// mlkem512_polyvec_add (0x28 bytes)
L83a8:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L7384
        add     x0, x20, #0x200
        add     x1, x19, #0x200
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L7384

// mlkem512_polyvec_tomont (0x18 bytes)
L83d0:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L72a0
        add     x0, x19, #0x200
        ldp     x30, x19, [sp], #16
        b       L72a0

// mlkem512_poly_getnoise_eta1_4x (0x160 bytes)
L83e8:
        stp     x29, x30, [sp, #-80]!
        stp     x28, x25, [sp, #16]
        stp     x24, x23, [sp, #32]
        stp     x22, x21, [sp, #48]
        stp     x20, x19, [sp, #64]
        mov     x29, sp
        sub     x9, sp, #0x430
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xf00000a8  // adrp x8, 0x1f000
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
        str     q0, [sp, #96]
        str     q1, [sp, #112]
        stp     q0, q1, [sp, #160]
        stp     q0, q1, [sp, #224]
        stp     x11, x10, [sp]
        bl      L4f50
        add     x1, sp, #0x120
        mov     x0, x23
        bl      L907c
        mov     x0, x22
        mov     x1, x24
        bl      L907c
        mov     x0, x21
        mov     x1, x25
        bl      L907c
        cbz     x19, L84d4
        mov     x0, x19
        mov     x1, x20
        bl      L907c
L84d4:
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
        .inst   0xf00000a8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #1064]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L8544
        mov     sp, x29
        ldp     x20, x19, [sp, #64]
        ldp     x22, x21, [sp, #48]
        ldp     x24, x23, [sp, #32]
        ldp     x28, x25, [sp, #16]
        ldp     x29, x30, [sp], #80
        ret
L8544:
        bl      L0830

// mlkem512_poly_getnoise_eta2 (0xac bytes)
L8548:
        stp     x29, x30, [sp, #-48]!
        stp     x28, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0xd0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xf00000a8  // adrp x8, 0x1f000
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
        bl      L4ad0
        add     x1, sp, #0x40
        mov     x0, x19
        bl      L8e64
        movi    v0.2d, #0x0
        .inst   0xf00000a8  // adrp x8, 0x1f000
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
        b.ne    L85f0
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldp     x28, x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L85f0:
        bl      L0830

// mlkem512_poly_getnoise_eta1122_4x (0x15c bytes)
L85f4:
        stp     x29, x30, [sp, #-96]!
        stp     x28, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0x440
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xf00000a8  // adrp x8, 0x1f000
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
        str     q0, [sp, #96]
        str     q1, [sp, #112]
        stp     q0, q1, [sp, #160]
        stp     q0, q1, [sp, #224]
        stp     x11, x10, [sp]
        bl      L4f50
        add     x1, sp, #0x120
        mov     x0, x22
        bl      L907c
        mov     x0, x21
        mov     x1, x23
        bl      L907c
        mov     x0, x20
        mov     x1, x24
        bl      L8e64
        mov     x0, x19
        mov     x1, x25
        bl      L8e64
        add     x0, sp, #0x120
        mov     w1, wzr
        mov     w2, #0x300
        bl      L0840
        movi    v0.2d, #0x0
        .inst   0xf00000a8  // adrp x8, 0x1f000
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
        b.ne    L874c
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L874c:
        bl      L0830

// mlkem_poly_rej_uniform_x4 (0x534 bytes)
L8750:
        stp     x29, x30, [sp, #-96]!
        stp     x28, x27, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0xb80
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xf00000a8  // adrp x8, 0x1f000
        mov     x22, x0
        add     x0, sp, #0x40
        mov     x23, x4
        mov     x19, x3
        mov     x20, x2
        ldr     x8, [x8, #4088]
        mov     x21, x1
        ldr     x8, [x8]
        str     x8, [sp, #2936]
        bl      L4f30
        add     x2, x23, #0x40
        add     x3, x23, #0x80
        add     x4, x23, #0xc0
        add     x0, sp, #0x40
        mov     x1, x23
        mov     w5, #0x22
        bl      L4cec
        add     x23, sp, #0x360
        add     x0, sp, #0x360
        add     x1, x23, #0x200
        add     x2, x23, #0x400
        add     x3, x23, #0x600
        add     x5, sp, #0x40
        mov     w4, #0x3
        stp     x2, x1, [sp, #40]
        str     x3, [sp, #32]
        bl      L4eb0
        mov     x8, xzr
        mov     x26, xzr
L87ec:
        add     x9, x23, x8
        ldrb    w11, [x9]
        ldrb    w10, [x9, #1]
        bfi     w11, w10, #8, #4
        cmp     w11, #0xd00
        b.hi    L8810
        add     x12, x26, #0x1
        strh    w11, [x22, x26, lsl #1]
        mov     x26, x12
L8810:
        cmp     x26, #0xff
        b.hi    L8838
        ldrb    w9, [x9, #2]
        lsr     w10, w10, #4
        orr     w9, w10, w9, lsl #4
        cmp     w9, #0xd00
        b.hi    L8838
        add     x10, x26, #0x1
        strh    w9, [x22, x26, lsl #1]
        mov     x26, x10
L8838:
        cmp     x26, #0x100
        cset    w16, cc
        cmp     x26, #0xff
        b.hi    L8858
        add     x9, x8, #0x3
        add     x8, x8, #0x3
        cmp     x9, #0x1f6
        b.cc    L87ec
L8858:
        mov     x8, xzr
        mov     x27, xzr
        add     x9, sp, #0x360
L8864:
        add     x10, x9, x8
        ldrb    w12, [x10, #512]
        ldrb    w11, [x10, #513]
        bfi     w12, w11, #8, #4
        cmp     w12, #0xd00
        b.hi    L8888
        add     x13, x27, #0x1
        strh    w12, [x21, x27, lsl #1]
        mov     x27, x13
L8888:
        cmp     x27, #0xff
        b.hi    L88b0
        ldrb    w10, [x10, #514]
        lsr     w11, w11, #4
        orr     w10, w11, w10, lsl #4
        cmp     w10, #0xd00
        b.hi    L88b0
        add     x11, x27, #0x1
        strh    w10, [x21, x27, lsl #1]
        mov     x27, x11
L88b0:
        cmp     x27, #0x100
        cset    w15, cc
        cmp     x27, #0xff
        b.hi    L88d0
        add     x10, x8, #0x3
        add     x8, x8, #0x3
        cmp     x10, #0x1f6
        b.cc    L8864
L88d0:
        mov     x8, xzr
        mov     x28, xzr
        add     x9, sp, #0x360
L88dc:
        add     x10, x9, x8
        ldrb    w12, [x10, #1024]
        ldrb    w11, [x10, #1025]
        bfi     w12, w11, #8, #4
        cmp     w12, #0xd00
        b.hi    L8900
        add     x13, x28, #0x1
        strh    w12, [x20, x28, lsl #1]
        mov     x28, x13
L8900:
        cmp     x28, #0xff
        b.hi    L8928
        ldrb    w10, [x10, #1026]
        lsr     w11, w11, #4
        orr     w10, w11, w10, lsl #4
        cmp     w10, #0xd00
        b.hi    L8928
        add     x11, x28, #0x1
        strh    w10, [x20, x28, lsl #1]
        mov     x28, x11
L8928:
        cmp     x28, #0x100
        cset    w14, cc
        cmp     x28, #0xff
        b.hi    L8948
        add     x10, x8, #0x3
        add     x8, x8, #0x3
        cmp     x10, #0x1f6
        b.cc    L88dc
L8948:
        mov     x8, xzr
        mov     x23, xzr
        add     x9, sp, #0x360
L8954:
        add     x10, x9, x8
        ldrb    w12, [x10, #1536]
        ldrb    w11, [x10, #1537]
        bfi     w12, w11, #8, #4
        cmp     w12, #0xd00
        b.hi    L8978
        add     x13, x23, #0x1
        strh    w12, [x19, x23, lsl #1]
        mov     x23, x13
L8978:
        cmp     x23, #0xff
        b.hi    L89a0
        ldrb    w10, [x10, #1538]
        lsr     w11, w11, #4
        orr     w10, w11, w10, lsl #4
        cmp     w10, #0xd00
        b.hi    L89a0
        add     x11, x23, #0x1
        strh    w10, [x19, x23, lsl #1]
        mov     x23, x11
L89a0:
        cmp     x23, #0x100
        cset    w25, cc
        cmp     x23, #0xff
        b.hi    L89c0
        add     x10, x8, #0x3
        add     x8, x8, #0x3
        cmp     x10, #0x1f6
        b.cc    L8954
L89c0:
        cmp     x26, #0x100
        str     x21, [sp, #24]
        b.cc    L89e4
        cmp     x27, #0x100
        b.cc    L89e4
        cmp     x28, #0x100
        b.cc    L89e4
        cmp     x23, #0xff
        b.hi    L8c2c
L89e4:
        add     x24, sp, #0x360
        str     x22, [sp, #16]
L89ec:
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
        bl      L4eb0
        tbz     w22, #0, L8a98
        ldp     x22, x15, [sp, #16]
        mov     x8, xzr
        mov     w14, w19
        mov     x19, x20
        mov     x20, x21
L8a30:
        add     x9, x24, x8
        ldrb    w11, [x9]
        ldrb    w10, [x9, #1]
        bfi     w11, w10, #8, #4
        cmp     w11, #0xd00
        b.hi    L8a54
        add     x12, x26, #0x1
        strh    w11, [x22, x26, lsl #1]
        mov     x26, x12
L8a54:
        cmp     x26, #0xff
        b.hi    L8a7c
        ldrb    w9, [x9, #2]
        lsr     w10, w10, #4
        orr     w9, w10, w9, lsl #4
        cmp     w9, #0xd00
        b.hi    L8a7c
        add     x10, x26, #0x1
        strh    w9, [x22, x26, lsl #1]
        mov     x26, x10
L8a7c:
        cmp     x26, #0xff
        b.hi    L8aa8
        add     x9, x8, #0x3
        add     x8, x8, #0x3
        cmp     x9, #0xa6
        b.cc    L8a30
        b       L8aa8
L8a98:
        ldr     x15, [sp, #24]
        mov     w14, w19
        mov     x19, x20
        mov     x20, x21
L8aa8:
        ldr     w8, [sp, #60]
        tbz     w8, #0, L8b18
        mov     x8, xzr
L8ab4:
        add     x9, x24, x8
        ldrb    w11, [x9, #512]
        ldrb    w10, [x9, #513]
        bfi     w11, w10, #8, #4
        cmp     w11, #0xd00
        b.hi    L8ad8
        add     x12, x27, #0x1
        strh    w11, [x15, x27, lsl #1]
        mov     x27, x12
L8ad8:
        cmp     x27, #0xff
        b.hi    L8b00
        ldrb    w9, [x9, #514]
        lsr     w10, w10, #4
        orr     w9, w10, w9, lsl #4
        cmp     w9, #0xd00
        b.hi    L8b00
        add     x10, x27, #0x1
        strh    w9, [x15, x27, lsl #1]
        mov     x27, x10
L8b00:
        cmp     x27, #0xff
        b.hi    L8b18
        add     x9, x8, #0x3
        add     x8, x8, #0x3
        cmp     x9, #0xa6
        b.cc    L8ab4
L8b18:
        tbz     w14, #0, L8b84
        mov     x8, xzr
L8b20:
        add     x9, x24, x8
        ldrb    w11, [x9, #1024]
        ldrb    w10, [x9, #1025]
        bfi     w11, w10, #8, #4
        cmp     w11, #0xd00
        b.hi    L8b44
        add     x12, x28, #0x1
        strh    w11, [x20, x28, lsl #1]
        mov     x28, x12
L8b44:
        cmp     x28, #0xff
        b.hi    L8b6c
        ldrb    w9, [x9, #1026]
        lsr     w10, w10, #4
        orr     w9, w10, w9, lsl #4
        cmp     w9, #0xd00
        b.hi    L8b6c
        add     x10, x28, #0x1
        strh    w9, [x20, x28, lsl #1]
        mov     x28, x10
L8b6c:
        cmp     x28, #0xff
        b.hi    L8b84
        add     x9, x8, #0x3
        add     x8, x8, #0x3
        cmp     x9, #0xa6
        b.cc    L8b20
L8b84:
        tbz     w25, #0, L8bf0
        mov     x8, xzr
L8b8c:
        add     x9, x24, x8
        ldrb    w11, [x9, #1536]
        ldrb    w10, [x9, #1537]
        bfi     w11, w10, #8, #4
        cmp     w11, #0xd00
        b.hi    L8bb0
        add     x12, x23, #0x1
        strh    w11, [x19, x23, lsl #1]
        mov     x23, x12
L8bb0:
        cmp     x23, #0xff
        b.hi    L8bd8
        ldrb    w9, [x9, #1538]
        lsr     w10, w10, #4
        orr     w9, w10, w9, lsl #4
        cmp     w9, #0xd00
        b.hi    L8bd8
        add     x10, x23, #0x1
        strh    w9, [x19, x23, lsl #1]
        mov     x23, x10
L8bd8:
        cmp     x23, #0xff
        b.hi    L8bf0
        add     x9, x8, #0x3
        add     x8, x8, #0x3
        cmp     x9, #0xa6
        b.cc    L8b8c
L8bf0:
        cmp     x27, #0x100
        cset    w15, cc
        cmp     x28, #0x100
        cset    w14, cc
        cmp     x23, #0x100
        cset    w25, cc
        cmp     x26, #0x100
        cset    w16, cc
        b.cc    L89ec
        cmp     x27, #0x100
        b.cc    L89ec
        cmp     x28, #0x100
        b.cc    L89ec
        cmp     x23, #0x100
        b.cc    L89ec
L8c2c:
        add     x0, sp, #0x40
        bl      L4f34
        add     x0, sp, #0x360
        mov     w1, wzr
        mov     w2, #0x800
        add     x19, sp, #0x360
        bl      L0840
        .inst   0xf00000a8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #2936]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L8c80
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L8c80:
        bl      L0830

// mlkem_poly_rej_uniform (0x1e0 bytes)
L8c84:
        stp     x29, x30, [sp, #-48]!
        stp     x28, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0x2f0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xf00000a8  // adrp x8, 0x1f000
        mov     x19, x0
        add     x0, sp, #0x200
        mov     x20, x1
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #744]
        bl      L4aa8
        add     x0, sp, #0x200
        mov     x1, x20
        mov     w2, #0x22
        bl      L491c
        mov     x0, sp
        add     x2, sp, #0x200
        mov     w1, #0x3
        mov     x21, sp
        bl      L4a5c
        mov     x8, xzr
        mov     x20, xzr
L8ce8:
        add     x9, x21, x8
        ldrb    w11, [x9]
        ldrb    w10, [x9, #1]
        bfi     w11, w10, #8, #4
        cmp     w11, #0xd00
        b.hi    L8d0c
        add     x12, x20, #0x1
        strh    w11, [x19, x20, lsl #1]
        mov     x20, x12
L8d0c:
        cmp     x20, #0xff
        b.hi    L8d34
        ldrb    w9, [x9, #2]
        lsr     w10, w10, #4
        orr     w9, w10, w9, lsl #4
        cmp     w9, #0xd00
        b.hi    L8d34
        add     x10, x20, #0x1
        strh    w9, [x19, x20, lsl #1]
        mov     x20, x10
L8d34:
        cmp     x20, #0xff
        b.hi    L8d4c
        add     x9, x8, #0x3
        add     x8, x8, #0x3
        cmp     x9, #0x1f6
        b.cc    L8ce8
L8d4c:
        cmp     x20, #0xff
        b.hi    L8de0
        mov     x21, sp
        b       L8d64
L8d5c:
        cmp     x20, #0x100
        b.cs    L8de0
L8d64:
        mov     x0, sp
        add     x2, sp, #0x200
        mov     w1, #0x1
        bl      L4a5c
        mov     x8, xzr
L8d78:
        add     x10, x21, x8
        ldrb    w11, [x10]
        ldrb    w9, [x10, #1]
        ldrb    w10, [x10, #2]
        bfi     w11, w9, #8, #4
        cmp     w11, #0xd00
        b.hi    L8da0
        add     x12, x20, #0x1
        strh    w11, [x19, x20, lsl #1]
        mov     x20, x12
L8da0:
        cmp     x20, #0xff
        b.hi    L8dc4
        lsr     w9, w9, #4
        orr     w9, w9, w10, lsl #4
        cmp     w9, #0xd00
        b.hi    L8dc4
        add     x10, x20, #0x1
        strh    w9, [x19, x20, lsl #1]
        mov     x20, x10
L8dc4:
        cmp     x20, #0xff
        b.hi    L8d5c
        add     x9, x8, #0x3
        add     x8, x8, #0x3
        cmp     x9, #0xa6
        b.cc    L8d78
        b       L8d5c
L8de0:
        add     x0, sp, #0x200
        bl      L4aac
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
        .inst   0xf00000a8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #744]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L8e60
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldp     x28, x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L8e60:
        bl      L0830

// mlkem_poly_cbd2 (0x218 bytes)
L8e64:
        add     x8, x1, #0x80
        cmp     x8, x0
        b.ls    L8f2c
        add     x8, x0, #0x200
        cmp     x8, x1
        b.ls    L8f2c
        .inst   0xf0000009  // adrp x9, 0xb000
        .inst   0xf000000a  // adrp x10, 0xb000
        .inst   0xf000000b  // adrp x11, 0xb000
        .inst   0xf000000c  // adrp x12, 0xb000
        movi    v2.4s, #0x3
        mov     x8, xzr
        ldr     d0, [x9, #656]
        mov     w9, #0x55555555
        ldr     q1, [x10, #336]
        add     x10, x0, #0x8
        ldr     d3, [x11, #664]
        ldr     q4, [x12, #352]
L8eac:
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
        b.ne    L8eac
        b       L9078
L8f2c:
        .inst   0xf0000009  // adrp x9, 0xb000
        .inst   0xd000000a  // adrp x10, 0xa000
        .inst   0xf000000b  // adrp x11, 0xb000
        mov     x8, xzr
        movi    v7.16b, #0x55
        ldr     q0, [x9, #272]
        .inst   0xd0000009  // adrp x9, 0xa000
        ldr     q1, [x10, #3696]
        .inst   0xf000000a  // adrp x10, 0xb000
        ldr     q2, [x11, #288]
        .inst   0xd000000b  // adrp x11, 0xa000
        ldr     q3, [x9, #3728]
        .inst   0xf0000009  // adrp x9, 0xb000
        movi    v16.4s, #0x3
        ldr     q4, [x10, #304]
        ldr     q5, [x11, #3760]
        ldr     q6, [x9, #320]
        .inst   0xd0000009  // adrp x9, 0xa000
        ldr     q17, [x9, #3792]
L8f78:
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
        b.ne    L8f78
L9078:
        ret

// mlkem_poly_cbd3 (0x334 bytes)
L907c:
        add     x8, x1, #0xc0
        cmp     x8, x0
        b.ls    L9134
        add     x8, x0, #0x200
        cmp     x8, x1
        b.ls    L9134
        .inst   0xd000000a  // adrp x10, 0xb000
        .inst   0xd000000b  // adrp x11, 0xb000
        mov     w9, #0x9249
        movi    v0.2s, #0x7
        mov     x8, xzr
        movk    w9, #0x24, lsl #16
        ldr     d1, [x10, #672]
        add     x10, x1, #0x1
        ldr     d2, [x11, #680]
L90b8:
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
        b.ne    L90b8
        b       L93ac
L9134:
        .inst   0xd0000009  // adrp x9, 0xb000
        .inst   0xd000000a  // adrp x10, 0xb000
        .inst   0xb000000b  // adrp x11, 0xa000
        mov     x8, xzr
        movi    v3.4s, #0x7
        ldr     q0, [x9, #368]
        .inst   0xd0000009  // adrp x9, 0xb000
        ldr     q1, [x10, #384]
        mov     w10, #0x9249
        movk    w10, #0x24, lsl #16
        ldr     q2, [x11, #3344]
        ldr     q4, [x9, #400]
        dup     v5.4s, w10
L9168:
        add     x9, x1, x8
        add     x8, x8, #0x30
        cmp     x8, #0xc0
        ld3     {v16.16b-v18.16b}, [x9]
        add     x9, x0, #0x80
        tbl     v21.16b, {v17.16b}, v4.16b
        tbl     v23.16b, {v17.16b}, v1.16b
        tbl     v24.16b, {v17.16b}, v0.16b
        tbl     v22.16b, {v17.16b}, v2.16b
        tbl     v6.16b, {v16.16b}, v0.16b
        tbl     v7.16b, {v16.16b}, v1.16b
        tbl     v19.16b, {v16.16b}, v2.16b
        tbl     v20.16b, {v16.16b}, v4.16b
        tbl     v25.16b, {v18.16b}, v0.16b
        tbl     v26.16b, {v18.16b}, v1.16b
        tbl     v27.16b, {v18.16b}, v2.16b
        tbl     v16.16b, {v18.16b}, v4.16b
        shl     v17.4s, v24.4s, #8
        shl     v18.4s, v21.4s, #8
        shl     v21.4s, v23.4s, #8
        shl     v22.4s, v22.4s, #8
        orr     v18.16b, v18.16b, v20.16b
        shl     v16.4s, v16.4s, #16
        orr     v7.16b, v21.16b, v7.16b
        orr     v6.16b, v17.16b, v6.16b
        shl     v17.4s, v25.4s, #16
        shl     v20.4s, v27.4s, #16
        shl     v21.4s, v26.4s, #16
        orr     v19.16b, v22.16b, v19.16b
        orr     v6.16b, v6.16b, v17.16b
        orr     v7.16b, v7.16b, v21.16b
        orr     v17.16b, v19.16b, v20.16b
        orr     v16.16b, v18.16b, v16.16b
        ushr    v22.4s, v6.4s, #1
        ushr    v23.4s, v16.4s, #1
        ushr    v24.4s, v7.4s, #1
        ushr    v25.4s, v17.4s, #1
        and     v18.16b, v16.16b, v5.16b
        ushr    v16.4s, v16.4s, #2
        and     v19.16b, v17.16b, v5.16b
        and     v20.16b, v7.16b, v5.16b
        and     v21.16b, v6.16b, v5.16b
        and     v23.16b, v23.16b, v5.16b
        and     v25.16b, v25.16b, v5.16b
        and     v24.16b, v24.16b, v5.16b
        and     v22.16b, v22.16b, v5.16b
        ushr    v6.4s, v6.4s, #2
        ushr    v17.4s, v17.4s, #2
        ushr    v7.4s, v7.4s, #2
        add     v21.4s, v22.4s, v21.4s
        add     v20.4s, v24.4s, v20.4s
        add     v19.4s, v25.4s, v19.4s
        add     v18.4s, v23.4s, v18.4s
        and     v6.16b, v6.16b, v5.16b
        and     v22.16b, v7.16b, v5.16b
        and     v7.16b, v17.16b, v5.16b
        and     v16.16b, v16.16b, v5.16b
        add     v17.4s, v18.4s, v16.4s
        add     v16.4s, v19.4s, v7.4s
        add     v7.4s, v21.4s, v6.4s
        add     v6.4s, v20.4s, v22.4s
        ushr    v23.4s, v7.4s, #3
        ushr    v25.4s, v6.4s, #3
        ushr    v26.4s, v7.4s, #9
        and     v18.16b, v7.16b, v3.16b
        ushr    v27.4s, v6.4s, #9
        and     v19.16b, v6.16b, v3.16b
        and     v23.16b, v23.16b, v3.16b
        and     v25.16b, v25.16b, v3.16b
        sub     v19.4s, v19.4s, v25.4s
        sub     v18.4s, v18.4s, v23.4s
        ushr    v23.4s, v7.4s, #6
        ushr    v25.4s, v6.4s, #6
        ushr    v22.4s, v17.4s, #3
        ushr    v24.4s, v16.4s, #3
        and     v23.16b, v23.16b, v3.16b
        and     v25.16b, v25.16b, v3.16b
        and     v26.16b, v26.16b, v3.16b
        and     v27.16b, v27.16b, v3.16b
        and     v20.16b, v16.16b, v3.16b
        and     v21.16b, v17.16b, v3.16b
        and     v24.16b, v24.16b, v3.16b
        and     v22.16b, v22.16b, v3.16b
        sub     v25.4s, v25.4s, v27.4s
        sub     v23.4s, v23.4s, v26.4s
        sub     v22.4s, v21.4s, v22.4s
        sub     v24.4s, v20.4s, v24.4s
        uzp1    v18.8h, v18.8h, v19.8h
        uzp1    v19.8h, v23.8h, v25.8h
        ushr    v23.4s, v16.4s, #6
        ushr    v25.4s, v17.4s, #6
        ushr    v26.4s, v16.4s, #9
        ushr    v27.4s, v17.4s, #9
        and     v23.16b, v23.16b, v3.16b
        and     v25.16b, v25.16b, v3.16b
        and     v26.16b, v26.16b, v3.16b
        and     v27.16b, v27.16b, v3.16b
        sub     v25.4s, v25.4s, v27.4s
        sub     v23.4s, v23.4s, v26.4s
        uzp1    v26.8h, v24.8h, v22.8h
        ushr    v22.4s, v17.4s, #12
        ushr    v24.4s, v17.4s, #15
        and     v22.16b, v22.16b, v3.16b
        and     v24.16b, v24.16b, v3.16b
        uzp1    v27.8h, v23.8h, v25.8h
        ushr    v23.4s, v16.4s, #12
        sub     v22.4s, v22.4s, v24.4s
        ushr    v24.4s, v16.4s, #15
        and     v23.16b, v23.16b, v3.16b
        and     v24.16b, v24.16b, v3.16b
        sub     v23.4s, v23.4s, v24.4s
        ushr    v24.4s, v6.4s, #12
        uzp1    v28.8h, v23.8h, v22.8h
        ushr    v22.4s, v6.4s, #15
        and     v23.16b, v24.16b, v3.16b
        and     v22.16b, v22.16b, v3.16b
        ushr    v24.4s, v17.4s, #18
        sub     v22.4s, v23.4s, v22.4s
        ushr    v23.4s, v16.4s, #18
        ushr    v17.4s, v17.4s, #21
        ushr    v16.4s, v16.4s, #21
        bic     v24.4s, #0x38
        bic     v23.4s, #0x38
        sub     v17.4s, v24.4s, v17.4s
        sub     v16.4s, v23.4s, v16.4s
        ushr    v24.4s, v7.4s, #12
        ushr    v23.4s, v7.4s, #15
        uzp1    v29.8h, v16.8h, v17.8h
        ushr    v16.4s, v6.4s, #18
        ushr    v17.4s, v7.4s, #18
        and     v24.16b, v24.16b, v3.16b
        ushr    v7.4s, v7.4s, #21
        and     v23.16b, v23.16b, v3.16b
        ushr    v6.4s, v6.4s, #21
        sub     v23.4s, v24.4s, v23.4s
        bic     v17.4s, #0x38
        bic     v16.4s, #0x38
        sub     v6.4s, v16.4s, v6.4s
        sub     v7.4s, v17.4s, v7.4s
        st4     {v26.8h-v29.8h}, [x0], #64
        uzp1    v20.8h, v23.8h, v22.8h
        uzp1    v21.8h, v7.8h, v6.8h
        st4     {v18.8h-v21.8h}, [x0]
        mov     x0, x9
        b.ne    L9168
L93ac:
        ret

// mlkem768_gen_matrix (0x1fc bytes)
L93b0:
        stp     x29, x30, [sp, #-64]!
        stp     x28, x23, [sp, #16]
        stp     x22, x21, [sp, #32]
        stp     x20, x19, [sp, #48]
        mov     x29, sp
        sub     x9, sp, #0x120
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd00000a9  // adrp x9, 0x1f000
        mov     w20, w2
        mov     x19, x0
        mov     w8, wzr
        mov     w21, #0xab
        mov     w22, #0x600
        ldr     x9, [x9, #4088]
        ldr     x9, [x9]
        str     x9, [sp, #280]
        mov     w9, #0x1
        ldp     q0, q1, [x1]
        stp     q0, q1, [sp]
        stp     q0, q1, [sp, #64]
        stp     q0, q1, [sp, #128]
        stp     q0, q1, [sp, #192]
        b       L94bc
L940c:
        strb    w12, [sp, #97]
        mov     w12, w10
        mov     w10, w14
        strb    w11, [sp, #32]
        strb    w9, [sp, #33]
        strb    w16, [sp, #96]
        strb    w15, [sp, #160]
        strb    w13, [sp, #161]
L942c:
        orr     w13, w8, #0x1
        orr     w14, w8, #0x2
        and     w15, w13, #0xff
        orr     w8, w8, #0x3
        and     w16, w14, #0xff
        and     w17, w8, #0xff
        mul     w15, w15, w21
        mov     x4, sp
        mul     w16, w16, w21
        strb    w12, [sp, #224]
        mul     w17, w17, w21
        lsr     w15, w15, #9
        lsr     w16, w16, #9
        umaddl  x9, w9, w22, x19
        lsr     w17, w17, #9
        add     w18, w15, w15, lsl #1
        sub     w13, w13, w18
        add     w18, w16, w16, lsl #1
        sub     w14, w14, w18
        add     w18, w17, w17, lsl #1
        sub     w8, w8, w18
        umaddl  x15, w15, w22, x19
        and     x13, x13, #0xff
        umaddl  x16, w16, w22, x19
        and     x14, x14, #0xff
        umaddl  x17, w17, w22, x19
        and     x8, x8, #0xff
        add     x0, x9, x11, lsl #9
        add     x1, x15, x13, lsl #9
        add     x2, x16, x14, lsl #9
        add     x3, x17, x8, lsl #9
        strb    w10, [sp, #225]
        bl      L8750
        mov     w9, wzr
        mov     w8, #0x4
        tbz     w23, #0, L953c
L94bc:
        orr     w10, w8, #0x1
        orr     w15, w8, #0x2
        and     w11, w10, #0xff
        and     w12, w15, #0xff
        orr     w17, w8, #0x3
        mov     w23, w9
        mul     w11, w11, w21
        and     w13, w17, #0xff
        mul     w14, w12, w21
        sub     w18, w8, #0x3
        lsr     w12, w11, #9
        mul     w11, w13, w21
        lsr     w13, w14, #9
        tst     w23, #0x1
        add     w16, w12, w12, lsl #1
        lsr     w14, w11, #9
        sub     w16, w10, w16
        add     w10, w13, w13, lsl #1
        sub     w15, w15, w10
        add     w10, w14, w14, lsl #1
        lsr     w9, w8, #2
        csel    w11, wzr, w18, ne
        sub     w10, w17, w10
        cbz     w20, L940c
        strb    w9, [sp, #32]
        strb    w11, [sp, #33]
        strb    w12, [sp, #96]
        mov     w12, w14
        strb    w16, [sp, #97]
        strb    w13, [sp, #160]
        strb    w15, [sp, #161]
        b       L942c
L953c:
        mov     w8, #0x202
        add     x0, x19, #0x1, lsl #12
        mov     x1, sp
        mov     x19, sp
        strh    w8, [sp, #32]
        bl      L8c84
        movi    v0.2d, #0x0
        .inst   0xd00000a8  // adrp x8, 0x1f000
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
        b.ne    L95a8
        mov     sp, x29
        ldp     x20, x19, [sp, #48]
        ldp     x22, x21, [sp, #32]
        ldp     x28, x23, [sp, #16]
        ldp     x29, x30, [sp], #64
        ret
L95a8:
        bl      L0830

// mlkem768_indcpa_keypair_derand (0x268 bytes)
L95ac:
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
        .inst   0xd00000a8  // adrp x8, 0x1f000
        mov     x20, x1
        mov     x19, x0
        add     x23, sp, #0x2, lsl #12
        add     x0, sp, #0x2, lsl #12
        add     x1, sp, #0x2, lsl #12
        ldr     x8, [x8, #4088]
        add     x23, x23, #0x720
        add     x0, x0, #0x760
        add     x1, x1, #0x720
        add     x22, sp, #0x2, lsl #12
        add     x24, sp, #0x2, lsl #12
        ldr     x8, [x8]
        add     x22, x22, #0x760
        add     x21, x22, #0x20
        add     x24, x24, #0x720
        str     x8, [sp, #10168]
        mov     w8, #0x3
        ldp     q0, q1, [x2]
        mov     w2, #0x21
        strb    w8, [x23, #32]
        str     q0, [sp, #10016]
        str     q1, [sp, #10032]
        bl      L4c48
        add     x0, sp, #0x1, lsl #12
        add     x1, sp, #0x2, lsl #12
        add     x0, x0, #0x520
        add     x1, x1, #0x760
        mov     w2, wzr
        add     x25, sp, #0x1, lsl #12
        add     x25, x25, #0x520
        bl      L93b0
        add     x26, sp, #0x320
        mov     w28, #0xff
        add     x1, x26, #0x200
        add     x2, x26, #0x400
        add     x0, sp, #0x320
        mov     x3, xzr
        mov     x4, x21
        mov     w5, wzr
        mov     w6, #0x1
        mov     w7, #0x2
        strb    w28, [sp]
        bl      Laaf0
        add     x27, sp, #0xf20
        add     x0, sp, #0xf20
        add     x1, x27, #0x200
        add     x2, x27, #0x400
        mov     x3, xzr
        mov     x4, x21
        mov     w5, #0x3
        mov     w6, #0x4
        mov     w7, #0x5
        strb    w28, [sp]
        bl      Laaf0
        add     x0, sp, #0x320
        bl      La7fc
        add     x0, sp, #0xf20
        bl      La7fc
        add     x0, sp, #0x20
        add     x1, sp, #0x320
        add     x28, sp, #0x20
        bl      Laa48
        add     x1, sp, #0x1, lsl #12
        add     x0, sp, #0x920
        add     x1, x1, #0x520
        add     x2, sp, #0x320
        add     x3, sp, #0x20
        add     x21, sp, #0x920
        bl      La83c
        add     x0, x21, #0x200
        add     x1, x25, #0x600
        add     x2, sp, #0x320
        add     x3, sp, #0x20
        bl      La83c
        add     x0, x21, #0x400
        add     x1, x25, #0xc00
        add     x2, sp, #0x320
        add     x3, sp, #0x20
        bl      La83c
        add     x0, sp, #0x920
        bl      Laad0
        add     x0, sp, #0x920
        add     x1, sp, #0xf20
        bl      Laa9c
        add     x0, sp, #0x920
        bl      Laa7c
        add     x0, sp, #0x320
        bl      Laa7c
        add     x1, sp, #0x320
        mov     x0, x20
        bl      La794
        add     x1, sp, #0x920
        mov     x0, x19
        bl      La794
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
        movi    v0.2d, #0x0
        strb    wzr, [x23, #32]
        .inst   0xd00000a8  // adrp x8, 0x1f000
        str     q0, [sp, #10032]
        str     q0, [sp, #10016]
        str     q0, [sp, #10128]
        str     q0, [sp, #10112]
        str     q0, [sp, #10096]
        str     q0, [sp, #10080]
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #10168]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L9810
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L9810:
        bl      L0830

// mlkem768_indcpa_enc (0x420 bytes)
L9814:
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
        .inst   0xd00000a8  // adrp x8, 0x1f000
        mov     x19, x0
        add     x0, sp, #0x1, lsl #12
        mov     x22, x1
        add     x0, x0, #0x520
        mov     x1, x2
        ldr     x8, [x8, #4088]
        add     x23, sp, #0x1, lsl #12
        mov     x20, x3
        mov     x21, x2
        add     x23, x23, #0x520
        ldr     x8, [x8]
        str     x8, [sp, #13144]
        bl      La7c8
        ldr     q0, [x21, #1152]
        add     x0, sp, #0x520
        ldr     q1, [x21, #1168]
        mov     x1, x22
        add     x26, sp, #0x520
        str     q0, [sp, #13088]
        str     q1, [sp, #13104]
        bl      L413c
        add     x0, sp, #0x2, lsl #12
        add     x1, sp, #0x3, lsl #12
        add     x0, x0, #0x120
        add     x1, x1, #0x320
        mov     w2, #0x1
        add     x22, sp, #0x2, lsl #12
        add     x22, x22, #0x120
        bl      L93b0
        add     x24, sp, #0x1, lsl #12
        add     x0, sp, #0x1, lsl #12
        add     x24, x24, #0xb20
        mov     w8, #0xff
        add     x1, x24, #0x200
        add     x2, x24, #0x400
        add     x0, x0, #0xb20
        mov     x3, xzr
        mov     x4, x20
        mov     w5, wzr
        mov     w6, #0x1
        mov     w7, #0x2
        strb    w8, [sp]
        bl      Laaf0
        add     x25, sp, #0xf20
        mov     w8, #0x6
        add     x1, x25, #0x200
        add     x2, x25, #0x400
        add     x0, sp, #0xf20
        add     x3, sp, #0x320
        mov     x4, x20
        mov     w5, #0x3
        mov     w6, #0x4
        mov     w7, #0x5
        add     x28, sp, #0x320
        strb    w8, [sp]
        bl      Laaf0
        add     x0, sp, #0x1, lsl #12
        add     x0, x0, #0xb20
        bl      La7fc
        add     x1, sp, #0x1, lsl #12
        add     x0, sp, #0x20
        add     x1, x1, #0xb20
        add     x21, sp, #0x20
        bl      Laa48
        add     x1, sp, #0x2, lsl #12
        add     x2, sp, #0x1, lsl #12
        add     x0, sp, #0x920
        add     x1, x1, #0x120
        add     x2, x2, #0xb20
        add     x3, sp, #0x20
        add     x20, sp, #0x920
        bl      La83c
        add     x2, sp, #0x1, lsl #12
        add     x0, x20, #0x200
        add     x1, x22, #0x600
        add     x2, x2, #0xb20
        add     x3, sp, #0x20
        bl      La83c
        add     x2, sp, #0x1, lsl #12
        add     x0, x20, #0x400
        add     x1, x22, #0xc00
        add     x2, x2, #0xb20
        add     x3, sp, #0x20
        bl      La83c
        add     x1, sp, #0x1, lsl #12
        add     x2, sp, #0x1, lsl #12
        add     x0, sp, #0x720
        add     x1, x1, #0x520
        add     x2, x2, #0xb20
        add     x3, sp, #0x20
        add     x27, sp, #0x720
        bl      La83c
        add     x0, sp, #0x920
        bl      La81c
        add     x0, sp, #0x720
        bl      L7e1c
        add     x0, sp, #0x920
        add     x1, sp, #0xf20
        bl      Laa9c
        add     x0, sp, #0x720
        add     x1, sp, #0x320
        bl      L7384
        add     x0, sp, #0x720
        add     x1, sp, #0x520
        bl      L7384
        add     x0, sp, #0x920
        bl      Laa7c
        add     x0, sp, #0x720
        bl      L7334
        add     x1, sp, #0x920
        mov     x0, x19
        bl      La72c
        add     x0, x19, #0x3c0
        add     x1, sp, #0x720
        bl      L262c
        add     x0, sp, #0x20
        mov     w1, wzr
        mov     w2, #0x300
        bl      L0840
        movi    v0.2d, #0x0
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
        add     x0, sp, #0x1, lsl #12
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
        .inst   0xd00000a8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #13144]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L9c30
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldp     x28, x27, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
L9c30:
        bl      L0830

// mlkem768_indcpa_dec (0x214 bytes)
L9c34:
        stp     x29, x30, [sp, #-80]!
        str     x28, [sp, #16]
        stp     x24, x23, [sp, #32]
        stp     x22, x21, [sp, #48]
        stp     x20, x19, [sp, #64]
        mov     x29, sp
        sub     x9, sp, #0x1, lsl #12
        sub     x9, x9, #0x310
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd00000a8  // adrp x8, 0x1f000
        mov     x21, x0
        add     x0, sp, #0xd00
        mov     x19, x2
        mov     x20, x1
        add     x22, sp, #0xd00
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #4872]
        bl      La760
        add     x1, x20, #0x3c0
        add     x0, sp, #0x500
        add     x20, sp, #0x500
        bl      L2c78
        add     x0, sp, #0x700
        mov     x1, x19
        add     x19, sp, #0x700
        bl      La7c8
        add     x0, sp, #0xd00
        bl      La7fc
        mov     x0, sp
        add     x1, sp, #0xd00
        mov     x24, sp
        bl      Laa48
        add     x0, sp, #0x300
        add     x1, sp, #0x700
        add     x2, sp, #0xd00
        mov     x3, sp
        add     x23, sp, #0x300
        bl      La83c
        add     x0, sp, #0x300
        bl      L7e1c
        add     x0, sp, #0x500
        add     x1, sp, #0x300
        bl      L7504
        add     x0, sp, #0x500
        bl      L7334
        add     x1, sp, #0x500
        mov     x0, x21
        bl      L421c
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
        .inst   0xd00000a8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #4872]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L9e44
        mov     w0, wzr
        mov     sp, x29
        ldp     x20, x19, [sp, #64]
        ldp     x22, x21, [sp, #48]
        ldp     x24, x23, [sp, #32]
        ldr     x28, [sp, #16]
        ldp     x29, x30, [sp], #80
        ret
L9e44:
        bl      L0830

// mlkem768_check_pk (0x150 bytes)
L9e48:
        stp     x29, x30, [sp, #-48]!
        stp     x28, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0xa90
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd00000a8  // adrp x8, 0x1f000
        mov     x19, x0
        add     x0, sp, #0x480
        mov     x1, x19
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #2696]
        bl      La7c8
        add     x0, sp, #0x480
        bl      Laa7c
        mov     x0, sp
        add     x1, sp, #0x480
        mov     x20, sp
        bl      La794
        movi    v0.2d, #0x0
        mov     x8, xzr
        movi    v1.2d, #0x0
        movi    v2.2d, #0x0
        movi    v3.2d, #0x0
L9eac:
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
        b.ne    L9eac
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
        .inst   0xd00000a8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #2696]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    L9f94
        mov     w0, w19
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldp     x28, x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
L9f94:
        bl      L0830

// mlkem768_check_sk (0xe0 bytes)
L9f98:
        stp     x29, x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x29, sp
        sub     x9, sp, #0x40
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xd00000a8  // adrp x8, 0x1f000
        mov     x19, x0
        add     x1, x0, #0x480
        mov     x0, sp
        mov     w2, #0x4a0
        mov     x20, sp
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #56]
        bl      L4ba4
        ldp     q2, q3, [sp]
        mov     w8, wzr
        ldr     q0, [x19, #2336]
        ldr     q1, [x19, #2352]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v3.16b, v1.16b
        orr     v2.16b, v1.16b, v0.16b
        ext     v3.16b, v2.16b, v2.16b, #8
        eor     v0.16b, v1.16b, v0.16b
        orr     v1.8b, v2.8b, v3.8b
        ext     v2.16b, v0.16b, v0.16b, #8
        fmov    x9, d1
        orr     x9, x9, x9, lsr #32
        eor     v0.8b, v0.8b, v2.8b
        lsr     x10, x9, #16
        fmov    x11, d0
        orr     w9, w9, w10
        movi    v0.2d, #0x0
        orr     w9, w9, w9, lsr #8
        eor     x10, x11, x11, lsr #32
        sub     w9, w8, w9, uxtb
        eor     x10, x10, x10, lsr #16
        lsr     x11, x10, #8
        eor     w10, w10, w11
        .inst   0xb00000ab  // adrp x11, 0x1f000
        eor     w9, w10, w9, lsr #16
        stp     q0, q0, [sp]
        and     w9, w9, #0xff
        ldr     x11, [x11, #4088]
        cmp     w9, w10, uxtb
        ldr     x12, [sp, #56]
        mov     w9, #0xfffffffb
        csel    w0, w8, w9, eq
        ldr     x11, [x11]
        cmp     x11, x12
        b.ne    La074
        mov     sp, x29
        ldp     x20, x19, [sp, #16]
        ldp     x29, x30, [sp], #32
        ret
La074:
        bl      L0830

// mlkem768_keypair_derand (0x88 bytes)
La078:
        str     x30, [sp, #-48]!
        stp     x22, x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x22, x2
        mov     x19, x1
        mov     x21, x0
        bl      L95ac
        mov     w20, w0
        cbz     w0, La0c0
        mov     x0, x21
        mov     w1, wzr
        mov     w2, #0x4a0
        bl      L0840
        mov     x0, x19
        mov     w1, wzr
        mov     w2, #0x960
        bl      L0840
        b       La0ec
La0c0:
        add     x0, x19, #0x480
        mov     x1, x21
        mov     w2, #0x4a0
        bl      L0810
        add     x0, x19, #0x920
        mov     x1, x21
        mov     w2, #0x4a0
        bl      L4ba4
        ldp     q1, q0, [x22, #32]
        str     q1, [x19, #2368]
        str     q0, [x19, #2384]
La0ec:
        mov     w0, w20
        ldp     x20, x19, [sp, #32]
        ldp     x22, x21, [sp, #16]
        ldr     x30, [sp], #48
        ret

// mlkem768_keypair (0xf4 bytes)
La100:
        stp     x29, x30, [sp, #-48]!
        str     x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0x50
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb00000a8  // adrp x8, 0x1f000
        mov     x19, x1
        mov     x21, x0
        mov     x0, sp
        mov     w1, #0x40
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #72]
        bl      L0820
        cbz     w0, La148
        mov     w20, #0xfffffffd
        b       La1b0
La148:
        mov     x2, sp
        mov     x0, x21
        mov     x1, x19
        bl      L95ac
        mov     w20, w0
        cbz     w0, La184
        mov     x0, x21
        mov     w1, wzr
        mov     w2, #0x4a0
        bl      L0840
        mov     x0, x19
        mov     w1, wzr
        mov     w2, #0x960
        bl      L0840
        b       La1b0
La184:
        add     x0, x19, #0x480
        mov     x1, x21
        mov     w2, #0x4a0
        bl      L0810
        add     x0, x19, #0x920
        mov     x1, x21
        mov     w2, #0x4a0
        bl      L4ba4
        ldp     q0, q1, [sp, #32]
        str     q0, [x19, #2368]
        str     q1, [x19, #2384]
La1b0:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        .inst   0xb00000a8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #72]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    La1f0
        mov     w0, w20
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldr     x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
La1f0:
        bl      L0830

// mlkem768_enc_derand (0x1e4 bytes)
La1f4:
        stp     x29, x30, [sp, #-96]!
        str     x28, [sp, #16]
        stp     x26, x25, [sp, #32]
        stp     x24, x23, [sp, #48]
        stp     x22, x21, [sp, #64]
        stp     x20, x19, [sp, #80]
        mov     x29, sp
        sub     x9, sp, #0xaa0
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb00000a8  // adrp x8, 0x1f000
        mov     x19, x1
        mov     x21, x0
        add     x0, sp, #0x480
        mov     x1, x2
        mov     x22, x3
        ldr     x8, [x8, #4088]
        mov     x20, x2
        ldr     x8, [x8]
        str     x8, [sp, #2712]
        bl      La7c8
        add     x0, sp, #0x480
        bl      Laa7c
        mov     x0, sp
        add     x1, sp, #0x480
        mov     x23, sp
        bl      La794
        movi    v0.2d, #0x0
        mov     x8, xzr
        movi    v1.2d, #0x0
        movi    v2.2d, #0x0
        movi    v3.2d, #0x0
La270:
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
        b.ne    La270
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
        b.ne    La374
        ldp     q0, q1, [x22]
        add     x0, x23, #0x20
        mov     x1, x20
        mov     w2, #0x4a0
        str     q0, [sp, #1152]
        str     q1, [sp, #1168]
        bl      L4ba4
        mov     x0, sp
        add     x1, sp, #0x480
        mov     w2, #0x40
        bl      L4c48
        add     x3, x24, #0x20
        add     x1, sp, #0x480
        mov     x0, x21
        mov     x2, x20
        bl      L9814
        cbnz    w0, La378
        ldp     q0, q1, [sp]
        stp     q0, q1, [x19]
        b       La378
La374:
        mov     w0, #0xfffffffc
La378:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        stp     q0, q0, [sp, #32]
        str     q0, [sp, #1200]
        add     x8, sp, #0x480
        str     q0, [sp, #1184]
        str     q0, [sp, #1168]
        str     q0, [sp, #1152]
        .inst   0xb00000a8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #2712]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    La3d4
        mov     sp, x29
        ldp     x20, x19, [sp, #80]
        ldp     x22, x21, [sp, #64]
        ldp     x24, x23, [sp, #48]
        ldp     x26, x25, [sp, #32]
        ldr     x28, [sp, #16]
        ldp     x29, x30, [sp], #96
        ret
La3d4:
        bl      L0830

// mlkem768_enc (0x9c bytes)
La3d8:
        stp     x29, x30, [sp, #-48]!
        str     x21, [sp, #16]
        stp     x20, x19, [sp, #32]
        mov     x29, sp
        sub     x9, sp, #0x30
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb00000a8  // adrp x8, 0x1f000
        mov     x20, x1
        mov     x21, x0
        mov     x0, sp
        mov     w1, #0x20
        mov     x19, x2
        ldr     x8, [x8, #4088]
        ldr     x8, [x8]
        str     x8, [sp, #40]
        bl      L0820
        cbz     w0, La424
        mov     w0, #0xfffffffd
        b       La438
La424:
        mov     x3, sp
        mov     x0, x21
        mov     x1, x20
        mov     x2, x19
        bl      La1f4
La438:
        movi    v0.2d, #0x0
        mov     x8, sp
        stp     q0, q0, [sp]
        .inst   0xb00000a8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #40]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    La470
        mov     sp, x29
        ldp     x20, x19, [sp, #32]
        ldr     x21, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
La470:
        bl      L0830

// mlkem768_dec (0x2b8 bytes)
La474:
        stp     x29, x30, [sp, #-64]!
        stp     x28, x23, [sp, #16]
        stp     x22, x21, [sp, #32]
        stp     x20, x19, [sp, #48]
        mov     x29, sp
        sub     x9, sp, #0x500
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb00000a8  // adrp x8, 0x1f000
        add     x22, x2, #0x480
        mov     x21, x2
        mov     x20, x1
        mov     x19, x0
        mov     x0, sp
        ldr     x8, [x8, #4088]
        mov     x1, x22
        mov     w2, #0x4a0
        mov     x23, sp
        ldr     x8, [x8]
        str     x8, [sp, #1272]
        bl      L4ba4
        ldp     q2, q3, [sp]
        mov     w8, wzr
        ldr     q0, [x21, #2336]
        ldr     q1, [x21, #2352]
        eor     v0.16b, v2.16b, v0.16b
        eor     v1.16b, v3.16b, v1.16b
        orr     v2.16b, v1.16b, v0.16b
        ext     v3.16b, v2.16b, v2.16b, #8
        eor     v0.16b, v1.16b, v0.16b
        orr     v1.8b, v2.8b, v3.8b
        ext     v2.16b, v0.16b, v0.16b, #8
        fmov    x9, d1
        orr     x9, x9, x9, lsr #32
        eor     v0.8b, v0.8b, v2.8b
        lsr     x10, x9, #16
        orr     w9, w9, w10
        fmov    x10, d0
        movi    v0.2d, #0x0
        orr     w9, w9, w9, lsr #8
        eor     x10, x10, x10, lsr #32
        sub     w8, w8, w9, uxtb
        eor     x9, x10, x10, lsr #16
        lsr     x10, x9, #8
        eor     w9, w9, w10
        eor     w8, w9, w8, lsr #16
        stp     q0, q0, [sp]
        and     w8, w8, #0xff
        cmp     w8, w9, uxtb
        b.ne    La6b0
        add     x0, sp, #0x4a0
        mov     x1, x20
        mov     x2, x21
        bl      L9c34
        mov     w23, w0
        cbnz    w0, La6b4
        add     x8, x21, #0x920
        add     x0, sp, #0x460
        add     x1, sp, #0x4a0
        mov     w2, #0x40
        add     x23, sp, #0x460
        ldp     q0, q1, [x8]
        str     q0, [sp, #1216]
        str     q1, [sp, #1232]
        bl      L4c48
        add     x3, x23, #0x20
        mov     x0, sp
        add     x1, sp, #0x4a0
        mov     x2, x22
        mov     x22, sp
        bl      L9814
        mov     w23, w0
        cbnz    w0, La6b4
        movi    v0.2d, #0x0
        mov     x8, xzr
        movi    v1.2d, #0x0
        movi    v2.2d, #0x0
        movi    v3.2d, #0x0
La5a8:
        add     x9, x20, x8
        add     x10, x22, x8
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
        b.ne    La5a8
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
        add     x0, sp, #0x4a0
        mov     x2, sp
        mov     w1, #0x20
        mov     w3, #0x460
        add     x20, sp, #0x4a0
        bl      L4ad0
        mov     x8, xzr
        sub     w9, w22, w21, uxtb
        add     x10, sp, #0x460
La670:
        ldrb    w11, [x20, x8]
        mov     w12, w9
        ldrb    w13, [x10, x8]
        lsr     w12, w12, #16
        and     w11, w11, w12
        bic     w13, w13, w12
        orr     w11, w11, w13
        strb    w11, [x20, x8]
        add     x8, x8, #0x1
        cmp     x8, #0x20
        b.ne    La670
        mov     w23, wzr
        ldr     q0, [sp, #1184]
        ldr     q1, [sp, #1200]
        stp     q0, q1, [x19]
        b       La6b4
La6b0:
        mov     w23, #0xfffffffb
La6b4:
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
        .inst   0xb00000a8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #1272]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    La728
        mov     w0, w23
        mov     sp, x29
        ldp     x20, x19, [sp, #48]
        ldp     x22, x21, [sp, #32]
        ldp     x28, x23, [sp, #16]
        ldp     x29, x30, [sp], #64
        ret
La728:
        bl      L0830

// mlkem768_polyvec_compress_du (0x34 bytes)
La72c:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L2bdc
        add     x0, x20, #0x140
        add     x1, x19, #0x200
        bl      L2bdc
        add     x0, x20, #0x280
        add     x1, x19, #0x400
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L2bdc

// mlkem768_polyvec_decompress_du (0x34 bytes)
La760:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L3044
        add     x0, x20, #0x200
        add     x1, x19, #0x140
        bl      L3044
        add     x0, x20, #0x400
        add     x1, x19, #0x280
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L3044

// mlkem768_polyvec_tobytes (0x34 bytes)
La794:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L3bfc
        add     x0, x20, #0x180
        add     x1, x19, #0x200
        bl      L3bfc
        add     x0, x20, #0x300
        add     x1, x19, #0x400
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L3bfc

// mlkem768_polyvec_frombytes (0x34 bytes)
La7c8:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L3e4c
        add     x0, x20, #0x200
        add     x1, x19, #0x180
        bl      L3e4c
        add     x0, x20, #0x400
        add     x1, x19, #0x300
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L3e4c

// mlkem768_polyvec_ntt (0x20 bytes)
La7fc:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L7c30
        add     x0, x19, #0x200
        bl      L7c30
        add     x0, x19, #0x400
        ldp     x30, x19, [sp], #16
        b       L7c30

// mlkem768_polyvec_invntt_tomont (0x20 bytes)
La81c:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L7e1c
        add     x0, x19, #0x200
        bl      L7e1c
        add     x0, x19, #0x400
        ldp     x30, x19, [sp], #16
        b       L7e1c

// mlkem768_polyvec_basemul_acc_montgomery_cached (0x20c bytes)
La83c:
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
        b.hi    La984
        tbnz    w8, #0, La984
        cbnz    w9, La984
        mov     w10, #0xf3010000
        mov     x8, xzr
        add     x9, x3, #0x100
        mvni    v1.4s, #0xd, lsl #8
        dup     v0.4s, w10
La88c:
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
        b.ne    La88c
        b       Laa44
La984:
        mov     x8, xzr
        mov     w9, #0xf3010000
        add     x10, x3, #0x100
        mov     w11, #0xfffff2ff
La994:
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
        b.ne    La994
Laa44:
        ret

// mlkem768_polyvec_mulcache_compute (0x34 bytes)
Laa48:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L7684
        add     x0, x20, #0x100
        add     x1, x19, #0x200
        bl      L7684
        add     x0, x20, #0x200
        add     x1, x19, #0x400
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L7684

// mlkem768_polyvec_reduce (0x20 bytes)
Laa7c:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L7334
        add     x0, x19, #0x200
        bl      L7334
        add     x0, x19, #0x400
        ldp     x30, x19, [sp], #16
        b       L7334

// mlkem768_polyvec_add (0x34 bytes)
Laa9c:
        str     x30, [sp, #-32]!
        stp     x20, x19, [sp, #16]
        mov     x19, x1
        mov     x20, x0
        bl      L7384
        add     x0, x20, #0x200
        add     x1, x19, #0x200
        bl      L7384
        add     x0, x20, #0x400
        add     x1, x19, #0x400
        ldp     x20, x19, [sp, #16]
        ldr     x30, [sp], #32
        b       L7384

// mlkem768_polyvec_tomont (0x20 bytes)
Laad0:
        stp     x30, x19, [sp, #-16]!
        mov     x19, x0
        bl      L72a0
        add     x0, x19, #0x200
        bl      L72a0
        add     x0, x19, #0x400
        ldp     x30, x19, [sp], #16
        b       L72a0

// mlkem768_poly_getnoise_eta1_4x (0x190 bytes)
Laaf0:
        stp     x29, x30, [sp, #-80]!
        stp     x28, x25, [sp, #16]
        stp     x24, x23, [sp, #32]
        stp     x22, x21, [sp, #48]
        stp     x20, x19, [sp, #64]
        mov     x29, sp
        sub     x9, sp, #0x330
        and     sp, x9, #0xffffffffffffffe0
        .inst   0xb00000a8  // adrp x8, 0x1f000
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
        str     q0, [sp, #96]
        str     q1, [sp, #112]
        stp     q0, q1, [sp, #160]
        stp     q0, q1, [sp, #224]
        stp     x11, x10, [sp]
        bl      L4f50
        add     x1, sp, #0x120
        mov     x0, x23
        bl      L8e64
        mov     x0, x22
        mov     x1, x24
        bl      L8e64
        mov     x0, x21
        mov     x1, x25
        bl      L8e64
        cbz     x19, Labdc
        mov     x0, x19
        mov     x1, x20
        bl      L8e64
Labdc:
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
        .inst   0xb00000a8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        ldr     x9, [sp, #808]
        ldr     x8, [x8]
        cmp     x8, x9
        b.ne    Lac7c
        mov     sp, x29
        ldp     x20, x19, [sp, #64]
        ldp     x22, x21, [sp, #48]
        ldp     x24, x23, [sp, #32]
        ldp     x28, x25, [sp, #16]
        ldp     x29, x30, [sp], #80
        ret
Lac7c:
        bl      L0830

// Padding (0xac80 to 0xac80)


// The read-only data (0xac80 to 0xb480)

        .quad   0x1c1814100c080400
        .quad   0x3c3834302c282420
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
        .quad   0xffffff09ffffff08
        .quad   0xffffff0bffffff0a
        .quad   0xffffff0dffffff0c
        .quad   0xffffff0fffffff0e
        .quad   0xffffff05ffffff04
        .quad   0xffffff07ffffff06
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
