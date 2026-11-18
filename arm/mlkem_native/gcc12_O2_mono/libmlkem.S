// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// The code and read-only data of mlkem-native's libmlkem.so (gcc 12, -O2, monolithic build)
//
// This is a transcription of the binary
// binaries/multilevel-mono/gcc12/O2/libmlkem.so from the binary branch of
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

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_libmlkem_gcc12_O2_mono)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_libmlkem_gcc12_O2_mono)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_libmlkem_gcc12_O2_mono):

// ELF header and dynamic linking information (0x0 to 0x7f0)

        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x0000000100b70003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x00000000000239b0
        .quad   0x0038004000000000
        .quad   0x0019001a00400005
        .quad   0x0000000500000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000006990
        .quad   0x0000000000006990
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
        .quad   0x000000100000002b
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x000000100000007f
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000013
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000024
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x00080012000000ac
        .quad   0x0000000000004650
        .quad   0x0000000000000334
        .quad   0x0008001200000147
        .quad   0x0000000000005380
        .quad   0x00000000000000e8
        .quad   0x000800120000008b
        .quad   0x00000000000044d0
        .quad   0x00000000000000e0
        .quad   0x0008001200000127
        .quad   0x0000000000004e90
        .quad   0x0000000000000374
        .quad   0x00080012000000cb
        .quad   0x0000000000004b00
        .quad   0x00000000000000e8
        .quad   0x0008001200000173
        .quad   0x0000000000005504
        .quad   0x000000000000008c
        .quad   0x0008001200000134
        .quad   0x0000000000005204
        .quad   0x000000000000017c
        .quad   0x000800120000019a
        .quad   0x0000000000005670
        .quad   0x0000000000000098
        .quad   0x0008001200000056
        .quad   0x00000000000043b0
        .quad   0x0000000000000094
        .quad   0x00080012000000b9
        .quad   0x0000000000004984
        .quad   0x000000000000017c
        .quad   0x00080012000000f5
        .quad   0x0000000000004c84
        .quad   0x000000000000008c
        .quad   0x0008001200000185
        .quad   0x0000000000005590
        .quad   0x00000000000000e0
        .quad   0x00080012000000dd
        .quad   0x0000000000004bf0
        .quad   0x0000000000000094
        .quad   0x000800120000009f
        .quad   0x00000000000045b0
        .quad   0x0000000000000098
        .quad   0x0008001200000044
        .quad   0x00000000000042c0
        .quad   0x00000000000000e8
        .quad   0x0008001200000106
        .quad   0x0000000000004d10
        .quad   0x00000000000000e0
        .quad   0x000800120000011a
        .quad   0x0000000000004df0
        .quad   0x0000000000000098
        .quad   0x0008001200000032
        .quad   0x0000000000004160
        .quad   0x0000000000000158
        .quad   0x00080012000001a8
        .quad   0x0000000000005710
        .quad   0x0000000000000534
        .quad   0x000800120000006e
        .quad   0x0000000000004444
        .quad   0x000000000000008c
        .quad   0x000800120000015a
        .quad   0x0000000000005470
        .quad   0x0000000000000094
        .quad   0x6b636174735f5f00
        .quad   0x6175675f6b68635f
        .quad   0x6174735f5f006472
        .quad   0x665f6b68635f6b63
        .quad   0x736d656d006c6961
        .quad   0x70636d656d007465
        .quad   0x356d656b6c6d0079
        .quad   0x6b636568635f3231
        .quad   0x656b6c6d006b705f
        .quad   0x6568635f3231356d
        .quad   0x6c6d006b735f6b63
        .quad   0x6b5f3231356d656b
        .quad   0x645f726961707965
        .quad   0x6c6d00646e617265
        .quad   0x6b5f3231356d656b
        .quad   0x7200726961707965
        .quad   0x7479626d6f646e61
        .quad   0x6d656b6c6d007365
        .quad   0x5f636e655f323135
        .quad   0x6d00646e61726564
        .quad   0x5f3231356d656b6c
        .quad   0x656b6c6d00636e65
        .quad   0x6365645f3231356d
        .quad   0x36376d656b6c6d00
        .quad   0x5f6b636568635f38
        .quad   0x6d656b6c6d006b70
        .quad   0x636568635f383637
        .quad   0x6b6c6d006b735f6b
        .quad   0x656b5f3836376d65
        .quad   0x65645f7269617079
        .quad   0x6b6c6d00646e6172
        .quad   0x656b5f3836376d65
        .quad   0x6c6d007269617079
        .quad   0x655f3836376d656b
        .quad   0x6e617265645f636e
        .quad   0x376d656b6c6d0064
        .quad   0x6d00636e655f3836
        .quad   0x5f3836376d656b6c
        .quad   0x656b6c6d00636564
        .quad   0x68635f343230316d
        .quad   0x6d006b705f6b6365
        .quad   0x343230316d656b6c
        .quad   0x735f6b636568635f
        .quad   0x316d656b6c6d006b
        .quad   0x7079656b5f343230
        .quad   0x617265645f726961
        .quad   0x6d656b6c6d00646e
        .quad   0x79656b5f34323031
        .quad   0x6b6c6d0072696170
        .quad   0x655f343230316d65
        .quad   0x6e617265645f636e
        .quad   0x316d656b6c6d0064
        .quad   0x00636e655f343230
        .quad   0x3230316d656b6c6d
        .quad   0x696c006365645f34
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

// The procedure linkage table and the code (0x7f0 to 0x5c44)
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

// mlk_poly_compress_d4_c (0xe4 bytes)
L0850:
        .inst   0xf00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        mov     x8, x0
        mov     w6, #0xafb0
        mov     x4, x1
        ldr     x0, [x2]
        str     x0, [sp, #24]
        mov     x0, #0x0
        add     x7, sp, #0x10
        mov     w9, #0x0
        movk    w6, #0x13, lsl #16
        mov     w5, #0x8000000
        nop
L0888:
        sub     w3, w9, #0x1
        mov     x1, #0x1
        str     xzr, [sp, #16]
        nop
L0898:
        add     w0, w3, w1
        add     x2, x7, x1
        add     x1, x1, #0x1
        ldrsh   w0, [x4, x0, lsl #1]
        madd    w0, w0, w6, w5
        lsr     w0, w0, #28
        sturb   w0, [x2, #-1]
        cmp     x1, #0x9
        b.ne    L0898
        ldrb    w13, [sp, #16]
        add     w9, w9, #0x8
        ldrb    w12, [sp, #18]
        add     x8, x8, #0x4
        ldrb    w11, [sp, #20]
        ldrb    w10, [sp, #22]
        ldrb    w3, [sp, #17]
        ldrb    w2, [sp, #19]
        ldrb    w1, [sp, #21]
        ldrb    w0, [sp, #23]
        orr     w3, w13, w3, lsl #4
        orr     w2, w12, w2, lsl #4
        sturb   w3, [x8, #-4]
        orr     w1, w11, w1, lsl #4
        sturb   w2, [x8, #-3]
        orr     w0, w10, w0, lsl #4
        sturb   w1, [x8, #-2]
        sturb   w0, [x8, #-1]
        cmp     w9, #0x100
        b.ne    L0888
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L0930
        ldr     x30, [sp], #32
        ret
L0930:
        bl      L0830

// mlk_poly_compress_d10_c (0xd0 bytes)
L0934:
        .inst   0xf00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        str     x30, [sp, #-32]!
        mov     x4, x0
        mov     x8, #0xbc00
        mov     x6, x1
        ldr     x0, [x2]
        str     x0, [sp, #24]
        mov     x0, #0x0
        add     x12, sp, #0x10
        mov     w3, #0x4
        movk    x8, #0x9d7d, lsl #16
        mov     x7, #0x100000000
L0968:
        sub     w1, w3, #0x4
        mov     x2, x12
L0970:
        ldrsh   x0, [x6, w1, uxtw #1]
        add     w1, w1, #0x1
        madd    x0, x0, x8, x7
        ubfx    x0, x0, #33, #10
        strh    w0, [x2], #2
        cmp     w3, w1
        b.ne    L0970
        ldrh    w2, [sp, #18]
        add     w3, w3, #0x4
        ldrh    w1, [sp, #20]
        add     x4, x4, #0x5
        ldrh    w0, [sp, #22]
        ldrh    w5, [sp, #16]
        lsl     w9, w2, #2
        lsl     w11, w1, #4
        sturb   w5, [x4, #-5]
        lsl     w10, w0, #6
        orr     w2, w11, w2, lsr #6
        orr     w1, w10, w1, lsr #4
        lsr     w0, w0, #2
        orr     w5, w9, w5, lsr #8
        sturb   w5, [x4, #-4]
        sturb   w2, [x4, #-3]
        sturb   w1, [x4, #-2]
        sturb   w0, [x4, #-1]
        cmp     w3, #0x104
        b.ne    L0968
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L0a00
        ldr     x30, [sp], #32
        ret
L0a00:
        bl      L0830

// mlk_poly_decompress_d4_c (0x4c bytes)
L0a04:
        add     x4, x0, #0x200
        mov     w3, #0xd01
        nop
L0a10:
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
        b.ne    L0a10
        ret

// mlk_poly_decompress_d10_c (0x84 bytes)
L0a50:
        mov     x5, x0
        .inst   0xb0000020  // adrp x0, 0x5000
        movi    v2.4s, #0x2, lsl #8
        add     x7, x1, #0x140
        ldr     q3, [x0, #3168]
        nop
L0a68:
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
        b.ne    L0a68
        ret

// mlk_poly_tobytes_c (0x38 bytes)
L0ad4:
        add     x4, x0, #0x180
L0ad8:
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
        b.ne    L0ad8
        ret
        nop

// mlk_poly_frombytes_c (0x3c bytes)
L0b10:
        add     x6, x1, #0x180
        nop
L0b18:
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
        b.ne    L0b18
        ret
        nop

// mlkem_poly_frommsg (0x5c bytes)
L0b50:
        mov     x6, x0
        mov     x5, x1
        mov     x3, #0x0
        mov     w8, #0x1
        mov     w7, #0x681
        nop
L0b68:
        lsl     w4, w3, #3
        mov     w1, #0x0
L0b70:
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
        b.ne    L0b70
        add     x3, x3, #0x1
        cmp     x3, #0x20
        b.ne    L0b68
        ret
        nop

// mlkem_poly_tomsg (0x64 bytes)
L0bb0:
        mov     w8, #0xafb8
        mov     x4, x0
        mov     x6, x1
        mov     x3, #0x0
        movk    w8, #0x13, lsl #16
        mov     w7, #0x40000000
L0bc8:
        lsl     w5, w3, #3
        mov     w2, #0x0
        mov     w1, #0x0
        strb    wzr, [x4, x3]
L0bd8:
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
        b.ne    L0bd8
        add     x3, x3, #0x1
        cmp     x3, #0x20
        b.ne    L0bc8
        ret

// mlk_poly_reduce_c (0x50 bytes)
L0c14:
        add     x5, x0, #0x200
        mov     w7, #0x4ebf
        mov     w6, #0x2000000
        mov     w4, #0xfffff2ff
        nop
L0c28:
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
        b.ne    L0c28
        ret

// mlk_poly_mulcache_compute_c (0x78 bytes)
L0c64:
        .inst   0xb0000028  // adrp x8, 0x5000
        add     x8, x8, #0xd20
        add     x5, x8, #0x80
        add     x4, x0, #0x2
        add     x3, x1, #0x2
        add     x8, x8, #0x100
        mov     w7, #0xfffff301
        mov     w6, #0xfffff2ff
        nop
L0c88:
        ldrsh   w0, [x5], #2
        add     x3, x3, #0x8
        ldursh  w2, [x3, #-8]
        neg     w1, w0
        sxth    w1, w1
        mul     w2, w2, w0
        mul     w0, w2, w7
        sxth    w0, w0
        madd    w0, w0, w6, w2
        asr     w0, w0, #16
        sturh   w0, [x4, #-2]
        ldursh  w0, [x3, #-4]
        mul     w1, w1, w0
        mul     w0, w1, w7
        sxth    w0, w0
        madd    w0, w0, w6, w1
        asr     w0, w0, #16
        strh    w0, [x4], #4
        cmp     x8, x5
        b.ne    L0c88
        ret
        nop

// mlk_poly_invntt_tomont_c (0x14c bytes)
L0ce0:
        mov     x15, x0
        .inst   0xb0000020  // adrp x0, 0x5000
        mvni    v3.8h, #0xd, lsl #8
        add     x1, x15, #0x200
        ldr     q4, [x0, #3184]
        .inst   0xb0000020  // adrp x0, 0x5000
        stp     x19, x30, [sp, #-16]!
        ldr     q5, [x0, #3200]
        mov     x0, x15
        nop
L0d08:
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
        b.ne    L0d08
        .inst   0xb000002e  // adrp x14, 0x5000
        add     x16, x15, #0x2
        add     x14, x14, #0xd20
        mov     w6, #0x65c
        mov     w17, #0x7
        mov     w30, #0x100
        mov     w18, #0x1
        mov     w9, #0x4ebf
        mov     w8, #0x2000000
        mov     w4, #0xfffff2ff
        mov     w7, #0xfffff301
L0d60:
        lsr     w10, w30, w17
        mov     w11, #0x0
        lsl     w12, w18, w17
        lsl     w13, w10, #1
        sub     w12, w12, #0x1
        nop
L0d78:
        sub     w12, w12, #0x1
        cmp     w11, w10
        b.cs    L0df4
        sub     w5, w10, w11
        mov     w0, w10
        sub     w5, w5, #0x1
        mov     w3, w11
        add     x5, x5, x0
        sub     x3, x3, x0
        add     x2, x15, w10, uxtw #1
        add     x5, x16, x5, lsl #1
        nop
L0da8:
        ldrsh   w19, [x2, x3, lsl #1]
        ldrh    w0, [x2]
        add     w0, w19, w0
        sxth    w0, w0
        madd    w1, w0, w9, w8
        asr     w1, w1, #26
        madd    w0, w1, w4, w0
        strh    w0, [x2, x3, lsl #1]
        ldrh    w0, [x2]
        sub     w0, w0, w19
        sxth    w0, w0
        mul     w0, w0, w6
        mul     w1, w0, w7
        sxth    w1, w1
        madd    w0, w1, w4, w0
        asr     w0, w0, #16
        strh    w0, [x2], #2
        cmp     x2, x5
        b.ne    L0da8
L0df4:
        add     w11, w11, w13
        add     w10, w10, w13
        cmp     w11, #0xff
        b.hi    L0e0c
        ldrsh   w6, [x14, w12, uxtw #1]
        b       L0d78
L0e0c:
        subs    w17, w17, #0x1
        b.eq    L0e24
        lsl     w0, w18, w17
        sub     w0, w0, #0x1
        ldrsh   w6, [x14, x0, lsl #1]
        b       L0d60
L0e24:
        ldp     x19, x30, [sp], #16
        ret
        nop

// mlk_polyvec_basemul_acc_montgomery_cached_c512 (0xb4 bytes)
L0e30:
        mov     x4, x1
        mov     x7, x0
        mov     x5, x2
        mov     x6, x3
        add     x13, x1, #0x200
        mov     w12, #0xfffff301
        mov     w11, #0xfffff2ff
        nop
L0e50:
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
        b.ne    L0e50
        ret

// mlkem_poly_cbd2 (0x88 bytes)
L0ee4:
        mov     x5, x0
        .inst   0xb0000020  // adrp x0, 0x5000
        .inst   0xb0000022  // adrp x2, 0x5000
        mov     x4, x1
        ldr     q7, [x0, #3232]
        .inst   0xb0000020  // adrp x0, 0x5000
        ldr     q16, [x2, #3216]
        mov     x1, #0x0
        ldr     q6, [x0, #3248]
        .inst   0xb0000020  // adrp x0, 0x5000
        movi    v3.8h, #0x3
        ldr     q5, [x0, #3264]
        nop
L0f18:
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
        b.ne    L0f18
        ret
        nop

// mlkem_poly_cbd3 (0x88 bytes)
L0f70:
        mov     x2, x1
        mov     x4, x0
        .inst   0xb0000021  // adrp x1, 0x5000
        .inst   0xb0000020  // adrp x0, 0x5000
        movi    v2.4h, #0x7
        mov     w3, #0x9249
        ldr     q4, [x1, #3280]
        add     x6, x2, #0xc0
        ldr     q3, [x0, #3296]
        movk    w3, #0x24, lsl #16
L0f98:
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
        b.ne    L0f98
        ret
        nop
        nop

// mlk_keccakf1600x4_xor_bytes_c (0xa8 bytes)
L1000:
        add     x5, x0, w5, uxtw
        mov     w6, w6
        mov     x7, #0x0
        nop
L1010:
        ldrb    w0, [x5, x7]
        mov     x8, x7
        ldrb    w9, [x1, x7]
        eor     w0, w0, w9
        strb    w0, [x5, x7]
        add     x7, x7, #0x1
        cmp     x6, x7
        b.ne    L1010
        add     x7, x5, #0xc8
        mov     x1, #0x0
L1038:
        ldrb    w6, [x7, x1]
        cmp     x8, x1
        ldrb    w9, [x2, x1]
        eor     w6, w6, w9
        strb    w6, [x7, x1]
        add     x1, x1, #0x1
        b.ne    L1038
        add     x6, x5, #0x190
        mov     x1, #0x0
        nop
L1060:
        ldrb    w2, [x6, x1]
        cmp     x8, x1
        ldrb    w7, [x3, x1]
        eor     w2, w2, w7
        strb    w2, [x6, x1]
        add     x1, x1, #0x1
        b.ne    L1060
        add     x5, x5, #0x258
        mov     x0, #0x0
        nop
L1088:
        ldrb    w2, [x5, x0]
        cmp     x8, x0
        ldrb    w3, [x4, x0]
        eor     w2, w2, w3
        strb    w2, [x5, x0]
        add     x0, x0, #0x1
        b.ne    L1088
        ret
        nop
        nop

// mlk_keccakf1600_permute_c (0x5d0 bytes)
L10b0:
        stp     x19, x20, [sp, #-192]!
        .inst   0x90000021  // adrp x1, 0x5000
        add     x1, x1, #0xd20
        add     x2, x1, #0x100
        add     x1, x1, #0x1c0
        ldp     x9, x4, [x0, #56]
        str     x2, [sp, #96]
        str     x1, [sp, #176]
        ldp     x1, x2, [x0]
        str     x1, [sp, #104]
        ldr     x1, [x0, #16]
        str     x4, [sp, #112]
        ldr     x4, [x0, #112]
        stp     x21, x22, [sp, #16]
        mov     x18, x9
        ldr     x3, [x0, #40]
        stp     x23, x24, [sp, #32]
        ldp     x7, x21, [x0, #72]
        stp     x25, x26, [sp, #48]
        ldp     x26, x23, [x0, #24]
        stp     x27, x28, [sp, #64]
        ldp     x20, x16, [x0, #88]
        str     x4, [sp, #120]
        ldr     x11, [x0, #104]
        str     x30, [sp, #80]
        str     x1, [sp, #136]
        mov     x28, x23
        ldr     x1, [x0, #48]
        mov     x14, x20
        ldp     x22, x12, [x0, #120]
        mov     x23, x21
        ldp     x4, x25, [x0, #184]
        mov     x27, x11
        ldp     x6, x5, [x0, #136]
        mov     x20, x2
        ldp     x13, x10, [x0, #152]
        mov     x30, x22
        ldp     x19, x15, [x0, #168]
        mov     x9, x25
        mov     x22, x7
        mov     x17, x12
        mov     x25, x3
        str     x26, [sp, #128]
        str     x0, [sp, #184]
L1160:
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
        b.ne    L1160
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

// mlk_keccak_absorb_once (0xe8 bytes)
L1680:
        movi    v0.4s, #0x0
        stp     x19, x20, [sp, #-64]!
        mov     x20, x0
        stp     x21, x22, [sp, #16]
        mov     w22, w1
        mov     x21, x2
        stp     x23, x24, [sp, #32]
        mov     x24, x22
        mov     x23, x3
        stp     x25, x30, [sp, #48]
        and     w25, w4, #0xff
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        stp     q0, q0, [x0, #64]
        stp     q0, q0, [x0, #96]
        stp     q0, q0, [x0, #128]
        stp     q0, q0, [x0, #160]
        str     xzr, [x0, #192]
        cmp     x3, x22
        b.cc    L1740
L16d0:
        mov     x19, #0x0
        nop
L16d8:
        ldrb    w4, [x20, x19]
        ldrb    w0, [x21, x19]
        eor     w4, w4, w0
        strb    w4, [x20, x19]
        add     x19, x19, #0x1
        cmp     x19, x22
        b.ne    L16d8
        mov     x0, x20
        sub     x23, x23, x19
        bl      L10b0
        add     x21, x21, x19
        cmp     x23, x19
        b.cs    L16d0
        cbnz    x23, L1740
L1710:
        ldrb    w0, [x20, x23]
        sub     w24, w24, #0x1
        eor     w25, w25, w0
        strb    w25, [x20, x23]
        ldrb    w0, [x20, w24, uxtw]
        eor     w0, w0, #0xffffff80
        strb    w0, [x20, w24, uxtw]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        ldp     x19, x20, [sp], #64
        ret
L1740:
        mov     w3, w23
        mov     x0, #0x0
L1748:
        ldrb    w1, [x20, x0]
        ldrb    w2, [x21, x0]
        eor     w1, w1, w2
        strb    w1, [x20, x0]
        add     x0, x0, #0x1
        cmp     x3, x0
        b.ne    L1748
        b       L1710
        nop
        nop

// mlk_polyvec_basemul_acc_montgomery_cached_c768 (0xc0 bytes)
L1770:
        mov     x10, x1
        mov     x11, x2
        mov     x14, x3
        add     x13, x1, #0x2
        mov     x15, x0
        add     x12, x2, #0x2
        add     x18, x3, #0x100
        mov     w17, #0xfffff301
        mov     w16, #0xfffff2ff
        nop
L1798:
        mov     x4, x14
        mov     x0, #0x0
        mov     w6, #0x0
        mov     w5, #0x0
L17a8:
        ldrsh   w8, [x13, x0]
        add     x4, x4, #0x100
        ldrsh   w7, [x10, x0]
        ldrsh   w1, [x11, x0]
        ldrsh   w2, [x12, x0]
        add     x0, x0, #0x200
        ldursh  w3, [x4, #-256]
        mul     w9, w7, w1
        mul     w1, w8, w1
        madd    w3, w3, w8, w9
        madd    w1, w2, w7, w1
        add     w5, w5, w3
        add     w6, w6, w1
        cmp     x0, #0x600
        b.ne    L17a8
        mul     w1, w5, w17
        add     x14, x14, #0x2
        mul     w0, w6, w17
        add     x13, x13, #0x4
        add     x10, x10, #0x4
        add     x11, x11, #0x4
        sxth    w1, w1
        add     x12, x12, #0x4
        sxth    w0, w0
        add     x15, x15, #0x4
        madd    w1, w1, w16, w5
        madd    w0, w0, w16, w6
        asr     w1, w1, #16
        sturh   w1, [x15, #-4]
        asr     w0, w0, #16
        sturh   w0, [x15, #-2]
        cmp     x18, x14
        b.ne    L1798
        ret

// mlk_polyvec_basemul_acc_montgomery_cached_c1024 (0xc0 bytes)
L1830:
        mov     x10, x1
        mov     x11, x2
        mov     x14, x3
        add     x13, x1, #0x2
        mov     x15, x0
        add     x12, x2, #0x2
        add     x18, x3, #0x100
        mov     w17, #0xfffff301
        mov     w16, #0xfffff2ff
        nop
L1858:
        mov     x4, x14
        mov     x0, #0x0
        mov     w8, #0x0
        mov     w7, #0x0
L1868:
        ldrsh   w6, [x13, x0]
        add     x4, x4, #0x100
        ldrsh   w5, [x10, x0]
        ldrsh   w1, [x11, x0]
        ldrsh   w2, [x12, x0]
        add     x0, x0, #0x200
        ldursh  w3, [x4, #-256]
        mul     w9, w5, w1
        mul     w1, w6, w1
        madd    w3, w3, w6, w9
        madd    w1, w2, w5, w1
        add     w7, w7, w3
        add     w8, w8, w1
        cmp     x0, #0x800
        b.ne    L1868
        mul     w1, w7, w17
        add     x14, x14, #0x2
        mul     w0, w8, w17
        add     x13, x13, #0x4
        add     x10, x10, #0x4
        add     x11, x11, #0x4
        sxth    w1, w1
        add     x12, x12, #0x4
        sxth    w0, w0
        add     x15, x15, #0x4
        madd    w1, w1, w16, w7
        madd    w0, w0, w16, w8
        asr     w1, w1, #16
        sturh   w1, [x15, #-4]
        asr     w0, w0, #16
        sturh   w0, [x15, #-2]
        cmp     x18, x14
        b.ne    L1858
        ret

// mlkem_sha3_512 (0xa0 bytes)
L18f0:
        stp     x19, x20, [sp, #-240]!
        mov     x3, x2
        mov     x2, x1
        .inst   0xd00000e5  // adrp x5, 0x1f000
        ldr     x5, [x5, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x20
        mov     w4, #0x6
        ldr     x6, [x5]
        str     x6, [sp, #232]
        mov     x6, #0x0
        mov     w1, #0x48
        mov     x20, x0
        mov     x0, x19
        bl      L1680
        movi    v0.4s, #0x0
        mov     x0, x19
        bl      L10b0
        str     xzr, [x19, #192]
        ldp     q3, q4, [x19]
        ldp     q1, q2, [x19, #32]
        stp     q0, q0, [x19]
        stp     q3, q4, [x20]
        stp     q1, q2, [x20, #32]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L198c
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #240
        ret
L198c:
        bl      L0830

// mlk_poly_ntt_c (0xdc bytes)
L1990:
        .inst   0x9000002d  // adrp x13, 0x5000
        mov     x14, x0
        add     x13, x13, #0xd20
        add     x15, x0, #0x2
        mov     w11, #0x0
        mov     w6, #0xfffffd0a
        mov     w17, #0x1
        mov     w18, #0x100
        mov     w8, #0xfffff301
        mov     w7, #0xfffff2ff
L19b8:
        add     w16, w11, #0x1
        mov     w9, #0x0
        lsl     w11, w17, w11
        lsr     w10, w18, w16
        lsl     w12, w10, #1
        nop
L19d0:
        add     w11, w11, #0x1
        cmp     w10, w9
        b.ls    L1a38
        sub     w5, w10, w9
        mov     w0, w9
        sub     w5, w5, #0x1
        mov     w4, w10
        add     x5, x5, x0
        sub     x4, x4, x0
        add     x1, x14, w9, uxtw #1
        add     x5, x15, x5, lsl #1
        nop
L1a00:
        ldrsh   w2, [x1, x4, lsl #1]
        ldrh    w3, [x1]
        mul     w2, w2, w6
        mul     w0, w2, w8
        sxth    w0, w0
        madd    w0, w0, w7, w2
        asr     w0, w0, #16
        sub     w2, w3, w0
        strh    w2, [x1, x4, lsl #1]
        ldrh    w2, [x1]
        add     w0, w0, w2
        strh    w0, [x1], #2
        cmp     x5, x1
        b.ne    L1a00
L1a38:
        add     w9, w9, w12
        add     w10, w10, w12
        cmp     w9, #0xff
        b.hi    L1a50
        ldrsh   w6, [x13, w11, uxtw #1]
        b       L19d0
L1a50:
        cmp     w16, #0x7
        b.eq    L1a68
        lsl     w0, w17, w16
        mov     w11, w16
        ldrsh   w6, [x13, x0, lsl #1]
        b       L19b8
L1a68:
        ret
        nop

// mlk_keccak_absorb_once_x4.constprop.0 (0xb0 bytes)
L1a70:
        .inst   0xd00000e7  // adrp x7, 0x1f000
        ldr     x7, [x7, #4088]
        str     x30, [sp, #-32]!
        mov     w12, w1
        mov     x1, x2
        mov     x2, x3
        mov     x3, x4
        mov     x4, x5
        ldr     x5, [x7]
        str     x5, [sp, #24]
        mov     x5, #0x0
        mov     w7, #0x1f
        add     x13, sp, #0x17
        mov     x11, x6
        mov     x10, x0
        strb    w7, [sp, #23]
        bl      L1000
        mov     w5, w11
        mov     x0, x10
        mov     x4, x13
        mov     x3, x13
        mov     x2, x13
        mov     x1, x13
        mov     w6, #0x1
        bl      L1000
        mov     w7, #0xffffff80
        mov     x0, x10
        mov     x2, x13
        mov     x1, x13
        sub     w5, w12, #0x1
        mov     x3, x13
        mov     w6, #0x1
        strb    w7, [sp, #23]
        bl      L1000
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #24]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L1b1c
        ldr     x30, [sp], #32
        ret
L1b1c:
        bl      L0830

// mlk_rej_uniform_c.constprop.0 (0x9c bytes)
L1b20:
        mov     x8, x0
        mov     w0, w1
        cmp     w1, #0xff
        b.hi    L1bb8
        mov     w9, #0x3
        mov     w11, #0xd00
        sub     w9, w9, w2
        mov     w10, #0xff
        b       L1b74
L1b44:
        cmp     w1, #0xd00
        mov     w5, w0
        ccmp    w0, w10, #0x2, le
        b.hi    L1b64
L1b54:
        add     w0, w5, #0x1
        strh    w1, [x8, w5, uxtw #1]
        cmp     w0, #0x100
        b.eq    L1bb8
L1b64:
        add     x2, x2, #0x3
        add     w1, w9, w2
        cmp     w3, w1
        b.cc    L1bb8
L1b74:
        ldrb    w4, [x2, #1]
        add     w5, w0, #0x1
        ldrb    w7, [x2]
        ldrb    w1, [x2, #2]
        lsr     w6, w4, #4
        orr     w4, w7, w4, lsl #8
        and     w4, w4, #0xfff
        orr     w1, w6, w1, lsl #4
        cmp     w4, #0xd00
        b.gt    L1b44
        strh    w4, [x8, w0, uxtw #1]
        cmp     w5, #0xff
        ccmp    w1, w11, #0x0, ls
        mov     w0, w5
        b.le    L1b54
        cmp     w0, #0x100
        b.ne    L1b64
L1bb8:
        ret
        nop

// mlk_keccak_squeezeblocks_x4 (0x10c bytes)
L1bc0:
        cbz     x4, L1cc8
        stp     x19, x20, [sp, #-96]!
        mov     x20, x1
        mov     x19, x0
        stp     x21, x22, [sp, #16]
        mov     x22, x3
        mov     x21, x2
        stp     x23, x24, [sp, #32]
        mov     x23, x5
        add     x24, x5, #0x258
        stp     x25, x26, [sp, #48]
        mov     w26, w6
        add     x25, x5, #0x190
        stp     x27, x28, [sp, #64]
        mov     x27, x4
        add     x28, x5, #0xc8
        str     x30, [sp, #80]
        nop
L1c08:
        mov     x0, x23
        bl      L10b0
        mov     x0, x28
        bl      L10b0
        mov     x0, x25
        bl      L10b0
        mov     x0, x24
        bl      L10b0
        mov     x0, #0x0
        nop
L1c30:
        ldrb    w1, [x23, x0]
        mov     x2, x0
        strb    w1, [x19, x0]
        add     x0, x0, #0x1
        cmp     x26, x0
        b.ne    L1c30
        mov     x1, #0x0
        nop
L1c50:
        ldrb    w6, [x28, x1]
        cmp     x2, x1
        strb    w6, [x20, x1]
        add     x1, x1, #0x1
        b.ne    L1c50
        mov     x1, #0x0
L1c68:
        ldrb    w6, [x25, x1]
        cmp     x2, x1
        strb    w6, [x21, x1]
        add     x1, x1, #0x1
        b.ne    L1c68
        mov     x1, #0x0
L1c80:
        ldrb    w6, [x24, x1]
        cmp     x2, x1
        strb    w6, [x22, x1]
        add     x1, x1, #0x1
        b.ne    L1c80
        add     x22, x22, x0
        add     x21, x21, x0
        add     x20, x20, x0
        add     x19, x19, x0
        subs    x27, x27, #0x1
        b.ne    L1c08
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        ldp     x19, x20, [sp], #96
        ret
L1cc8:
        ret
        nop

// mlkem_poly_rej_uniform_x4 (0x21c bytes)
L1cd0:
        sub     sp, sp, #0xbc0
        .inst   0xd00000e5  // adrp x5, 0x1f000
        ldr     x5, [x5, #4088]
        stp     x21, x22, [sp, #16]
        add     x22, sp, #0x9f
        and     x22, x22, #0xffffffffffffffe0
        stp     x19, x20, [sp]
        mov     x21, x1
        mov     x19, x4
        stp     x23, x24, [sp, #32]
        mov     x20, x0
        add     x23, x22, #0x600
        stp     x25, x26, [sp, #48]
        add     x26, x22, #0x800
        add     x24, x22, #0x400
        stp     x27, x28, [sp, #64]
        mov     x27, x3
        mov     x28, x2
        str     x30, [sp, #80]
        add     x25, x22, #0x200
        stp     x0, x1, [sp, #96]
        mov     x0, x26
        stp     x2, x3, [sp, #112]
        mov     x2, #0x320
        ldr     x1, [x5]
        str     x1, [sp, #3000]
        mov     x1, #0x0
        bl      L0840
        add     x5, x19, #0xc0
        add     x4, x19, #0x80
        add     x3, x19, #0x40
        mov     x2, x19
        mov     x0, x26
        mov     x6, #0x22
        mov     w1, #0xa8
        bl      L1a70
        mov     x5, x26
        mov     w6, #0xa8
        mov     x4, #0x3
        mov     x3, x23
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L1bc0
        mov     w3, #0x1f8
        mov     x2, x22
        mov     x0, x20
        mov     w1, #0x0
        bl      L1b20
        mov     w20, w0
        mov     x2, x25
        mov     x0, x21
        mov     w1, #0x0
        bl      L1b20
        mov     x2, x24
        mov     w21, w0
        mov     w1, #0x0
        mov     x0, x28
        bl      L1b20
        mov     w19, w0
        mov     w1, #0x0
        mov     x0, x27
        mov     x2, x23
        bl      L1b20
        cmp     w21, #0xff
        mov     w27, #0xff
        ccmp    w20, w27, #0x0, hi
        mov     w28, w0
        cset    w0, ls
        cmp     w19, w27
        ccmp    w28, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbz     w0, L1e8c
L1df8:
        mov     x5, x26
        mov     w6, #0xa8
        mov     x4, #0x1
        mov     x3, x23
        mov     x2, x24
        mov     x1, x25
        mov     x0, x22
        bl      L1bc0
        ldr     x0, [sp, #96]
        mov     w3, #0xa8
        mov     w1, w20
        mov     x2, x22
        bl      L1b20
        mov     w20, w0
        ldr     x0, [sp, #104]
        mov     w1, w21
        mov     x2, x25
        bl      L1b20
        mov     w21, w0
        ldr     x0, [sp, #112]
        mov     w1, w19
        mov     x2, x24
        bl      L1b20
        mov     w19, w0
        ldr     x0, [sp, #120]
        mov     w1, w28
        mov     x2, x23
        bl      L1b20
        mov     w28, w0
        cmp     w19, #0xff
        ccmp    w0, w27, #0x0, hi
        cset    w0, ls
        cmp     w21, #0xff
        ccmp    w20, w27, #0x0, hi
        cset    w1, ls
        orr     w0, w0, w1
        cbnz    w0, L1df8
L1e8c:
        mov     x0, x26
        mov     x2, #0x320
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x22
        mov     w1, #0x0
        bl      L0840
        .inst   0xd00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #3000]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L1ee8
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0xbc0
        ret
L1ee8:
        bl      L0830
        nop

// mlkem512_gen_matrix (0xc4 bytes)
L1ef0:
        stp     x19, x30, [sp, #-304]!
        .inst   0xd00000e5  // adrp x5, 0x1f000
        ldr     x5, [x5, #4088]
        add     x19, sp, #0x2f
        and     x19, x19, #0xffffffffffffffe0
        mov     x3, x19
        add     x4, x19, #0x100
        ldr     x6, [x5]
        str     x6, [sp, #296]
        mov     x6, #0x0
L1f18:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x3]
        add     x3, x3, #0x40
        cmp     x4, x3
        b.ne    L1f18
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
        bl      L1cd0
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
        ldr     x2, [sp, #296]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L1fb0
        ldp     x19, x30, [sp], #304
        ret
L1fb0:
        bl      L0830

// mlkem768_gen_matrix (0x274 bytes)
L1fb4:
        sub     sp, sp, #0x440
        add     x4, sp, #0x5f
        .inst   0xd00000e3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        stp     x21, x22, [sp, #16]
        and     x21, x4, #0xffffffffffffffe0
        add     x20, x21, #0x300
        stp     x23, x24, [sp, #32]
        add     x24, x21, #0x200
        stp     x25, x30, [sp, #48]
        mov     x25, x0
        mov     x0, x24
        ldr     x4, [x3]
        str     x4, [sp, #1080]
        mov     x4, #0x0
L1ff4:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x0]
        add     x0, x0, #0x40
        cmp     x20, x0
        b.ne    L1ff4
        strh    wzr, [x21, #544]
        cbnz    w2, L21e0
        mov     w7, #0x1
        mov     w6, #0x2
        mov     w5, #0x100
        mov     x4, x24
        add     x3, x25, #0x600
        add     x2, x25, #0x400
        add     x1, x25, #0x200
        mov     x0, x25
        strh    w7, [x21, #608]
        strh    w6, [x21, #672]
        strh    w5, [x21, #736]
        bl      L1cd0
        mov     w7, #0x2
        mov     w5, w7
        mov     w8, #0x0
        mov     w6, #0x1
L2050:
        mov     w9, #0x101
        mov     x4, x24
        add     x3, x25, #0xe00
        add     x2, x25, #0xc00
        add     x1, x25, #0xa00
        add     x0, x25, #0x800
        strb    w5, [x24, #96]
        add     x22, x21, #0xa8
        strb    w6, [x24, #97]
        mov     x23, #0x3
        strb    w8, [x24, #160]
        strb    w7, [x24, #161]
        strb    w6, [x24, #224]
        strb    w5, [x24, #225]
        strh    w9, [x21, #544]
        bl      L1cd0
        mov     w5, #0x202
        mov     x2, x24
        mov     x0, x20
        mov     w4, #0x1f
        mov     x3, #0x22
        mov     w1, #0xa8
        strh    w5, [x21, #544]
        bl      L1680
L20b0:
        mov     x0, x20
        bl      L10b0
        sub     x19, x22, #0xa8
        mov     x0, x20
L20c0:
        ldr     d0, [x0], #8
        str     d0, [x19], #8
        cmp     x19, x22
        b.ne    L20c0
        add     x22, x19, #0xa8
        subs    x23, x23, #0x1
        b.ne    L20b0
        add     x25, x25, #0x1, lsl #12
        mov     x2, x21
        mov     x0, x25
        mov     w3, #0x1f8
        mov     w1, #0x0
        bl      L1b20
        mov     w19, w0
        cmp     w0, #0xff
        b.hi    L2158
L2100:
        mov     x0, x20
        bl      L10b0
        ldp     q16, q17, [x20]
        mov     w1, w19
        ldp     q6, q7, [x20, #32]
        mov     x2, x21
        ldp     q4, q5, [x20, #64]
        mov     x0, x25
        ldp     q2, q3, [x20, #96]
        mov     w3, #0xa8
        ldp     q0, q1, [x20, #128]
        stp     q16, q17, [x21]
        ldr     x4, [x20, #160]
        stp     q6, q7, [x21, #32]
        stp     q4, q5, [x21, #64]
        stp     q2, q3, [x21, #96]
        stp     q0, q1, [x21, #128]
        str     x4, [x21, #160]
        bl      L1b20
        mov     w19, w0
        cmp     w0, #0xff
        b.ls    L2100
L2158:
        movi    v0.4s, #0x0
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        stp     q0, q0, [x20, #64]
        stp     q0, q0, [x20, #96]
        stp     q0, q0, [x20, #128]
        stp     q0, q0, [x20, #160]
        stp     q0, q0, [x20, #192]
        mov     x2, #0x1f8
        mov     x0, x21
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        stp     q0, q0, [x24]
        stp     q0, q0, [x24, #32]
        stp     q0, q0, [x24, #64]
        stp     q0, q0, [x24, #96]
        stp     q0, q0, [x24, #128]
        stp     q0, q0, [x24, #160]
        stp     q0, q0, [x24, #192]
        stp     q0, q0, [x24, #224]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1080]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L2224
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x30, [sp, #48]
        add     sp, sp, #0x440
        ret
L21e0:
        mov     w7, #0x100
        mov     w6, #0x200
        mov     w5, #0x1
        mov     x4, x24
        add     x3, x25, #0x600
        add     x2, x25, #0x400
        add     x1, x25, #0x200
        mov     x0, x25
        strh    w7, [x21, #608]
        strh    w6, [x21, #672]
        strh    w5, [x21, #736]
        bl      L1cd0
        mov     w8, #0x2
        mov     w7, #0x0
        mov     w6, w8
        mov     w5, #0x1
        b       L2050
L2224:
        bl      L0830
        nop
        nop

// mlkem1024_gen_matrix (0x14c bytes)
L2230:
        stp     x19, x20, [sp, #-368]!
        .inst   0xb00000e4  // adrp x4, 0x1f000
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
L2270:
        ldp     q0, q1, [x1]
        stp     q0, q1, [x3]
        add     x3, x3, #0x40
        cmp     x0, x3
        b.ne    L2270
        mov     w19, #0x4
        mov     w26, #0x800
        mov     x23, #0x600
        mov     x22, #0x400
        mov     x21, #0x200
L2298:
        sub     w0, w19, #0x4
        mov     x6, x20
        mov     w1, w0
L22a4:
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
        b.ne    L22a4
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
        bl      L1cd0
        cmp     w19, #0x14
        b.ne    L2298
        movi    v0.4s, #0x0
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        stp     q0, q0, [x20, #64]
        stp     q0, q0, [x20, #96]
        stp     q0, q0, [x20, #128]
        stp     q0, q0, [x20, #160]
        stp     q0, q0, [x20, #192]
        stp     q0, q0, [x20, #224]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #360]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L2378
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldr     x30, [sp, #64]
        ldp     x19, x20, [sp], #368
        ret
L2378:
        bl      L0830
        nop

// mlkem_shake256x4.constprop.0 (0x1f0 bytes)
L2380:
        sub     sp, sp, #0x5d0
        .inst   0xb00000e8  // adrp x8, 0x1f000
        ldr     x8, [x8, #4088]
        stp     x19, x20, [sp]
        mov     x19, #0xf0f0f0f0f0f0f0f0
        movk    x19, #0xf0f1
        stp     x21, x22, [sp, #16]
        mov     x20, x5
        umulh   x19, x4, x19
        ldr     x22, [sp, #1488]
        stp     x23, x24, [sp, #32]
        add     x23, sp, #0x8f
        stp     x25, x26, [sp, #48]
        and     x23, x23, #0xffffffffffffffe0
        mov     x25, x7
        stp     x27, x28, [sp, #64]
        mov     x24, x4
        mov     x21, x6
        str     x30, [sp, #80]
        mov     x28, x0
        str     x3, [sp, #104]
        mov     x27, x1
        mov     x26, x2
        mov     x0, x23
        ldr     x1, [x8]
        str     x1, [sp, #1480]
        mov     x1, #0x0
        mov     x2, #0x320
        bl      L0840
        lsr     x19, x19, #7
        mov     x4, x25
        mov     x3, x21
        mov     x2, x20
        mov     x5, x22
        mov     x0, x23
        mov     x6, #0x21
        mov     w1, #0x88
        bl      L1a70
        ldr     x3, [sp, #104]
        mov     x4, x19
        add     x19, x19, x19, lsl #4
        mov     x5, x23
        mov     x2, x26
        mov     x1, x27
        lsl     x25, x19, #3
        mov     x0, x28
        mov     w6, #0x88
        bl      L1bc0
        add     x19, sp, #0x540
        subs    x24, x24, x25
        b.ne    L24f8
        add     x20, sp, #0x4b8
        add     x21, sp, #0x430
        add     x22, sp, #0x3a8
L2458:
        mov     x0, x23
        mov     x2, #0x320
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        str     xzr, [x22, #128]
        stp     q0, q0, [x22]
        stp     q0, q0, [x22, #32]
        stp     q0, q0, [x22, #64]
        stp     q0, q0, [x22, #96]
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        stp     q0, q0, [x21, #64]
        stp     q0, q0, [x21, #96]
        str     xzr, [x21, #128]
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        stp     q0, q0, [x20, #64]
        stp     q0, q0, [x20, #96]
        str     xzr, [x20, #128]
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        str     xzr, [x19, #128]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1480]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L256c
        ldp     x19, x20, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, #0x5d0
        ret
L24f8:
        mov     x5, x23
        mov     x3, x19
        mov     w6, #0x88
        mov     x4, #0x1
        add     x20, sp, #0x4b8
        add     x21, sp, #0x430
        add     x22, sp, #0x3a8
        mov     x2, x20
        mov     x1, x21
        mov     x0, x22
        bl      L1bc0
        mov     x2, x24
        mov     x1, x22
        add     x0, x28, x25
        bl      L0810
        mov     x2, x24
        mov     x1, x21
        add     x0, x27, x25
        bl      L0810
        mov     x2, x24
        mov     x1, x20
        add     x0, x26, x25
        bl      L0810
        ldr     x0, [sp, #104]
        mov     x2, x24
        mov     x1, x19
        add     x0, x0, x25
        bl      L0810
        b       L2458
L256c:
        bl      L0830

// mlkem1024_poly_getnoise_eta1_4x (0x154 bytes)

// mlkem768_poly_getnoise_eta1_4x (0x154 bytes)
L2570:
        sub     sp, sp, #0x380
        .inst   0xb00000eb  // adrp x11, 0x1f000
        ldr     x11, [x11, #4088]
        stp     x19, x20, [sp, #16]
        add     x20, sp, #0x7f
        and     x20, x20, #0xffffffffffffffe0
        add     x19, x20, #0x200
        stp     x21, x22, [sp, #32]
        add     x9, x20, #0x240
        stp     x23, x24, [sp, #48]
        add     x8, x20, #0x280
        add     x10, x20, #0x2c0
        stp     x25, x26, [sp, #64]
        mov     x22, x2
        add     x25, x20, #0x100
        stp     x27, x30, [sp, #80]
        add     x27, x20, #0x180
        mov     x21, x3
        ldp     q0, q1, [x4]
        ldr     x2, [x11]
        str     x2, [sp, #888]
        mov     x2, #0x0
        strb    w5, [x19, #32]
        mov     x3, x27
        str     x10, [sp]
        mov     x2, x25
        ldrb    w11, [sp, #896]
        mov     x5, x19
        stp     q0, q1, [x9]
        mov     x4, #0x80
        add     x26, x20, x4
        stp     q0, q1, [x8]
        mov     x24, x0
        mov     x23, x1
        stp     q0, q1, [x10]
        mov     x1, x26
        mov     x0, x20
        strb    w6, [x19, #96]
        mov     x6, x9
        strb    w7, [x19, #160]
        mov     x7, x8
        strb    w11, [x19, #224]
        stp     q0, q1, [x19]
        bl      L2380
        mov     x1, x20
        mov     x0, x24
        bl      L0ee4
        mov     x1, x26
        mov     x0, x23
        bl      L0ee4
        mov     x1, x25
        mov     x0, x22
        bl      L0ee4
        cbz     x21, L2654
        mov     x1, x27
        mov     x0, x21
        bl      L0ee4
L2654:
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
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #888]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L26c0
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x30, [sp, #80]
        add     sp, sp, #0x380
        ret
L26c0:
        bl      L0830

// mlkem1024_indcpa_keypair_derand (0x3cc bytes)
L26c4:
        mov     x12, #0x3d40
        sub     sp, sp, x12
        mov     x3, #0x3c40
        mov     x4, #0x3c00
        mov     x5, #0x3800
        stp     x19, x20, [sp, #16]
        stp     x21, x22, [sp, #32]
        mov     w22, #0x4
        stp     x23, x24, [sp, #48]
        add     x23, sp, #0xcf
        and     x23, x23, #0xffffffffffffffe0
        stp     x25, x26, [sp, #64]
        add     x3, x23, x3
        add     x20, x23, #0x3, lsl #12
        stp     x27, x28, [sp, #80]
        add     x24, x23, x4
        add     x27, x23, x5
        str     x30, [sp, #96]
        add     x21, x23, #0x2, lsl #12
        stp     x0, x1, [sp, #112]
        mov     x1, x3
        add     x25, x24, #0x20
        ldp     q0, q1, [x2]
        str     x3, [sp, #136]
        .inst   0xb00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        add     x28, x20, #0x200
        mov     x26, x21
        ldr     x0, [x2]
        str     x0, [sp, #15672]
        mov     x0, #0x0
        stp     q0, q1, [x3]
        mov     x0, x24
        mov     x2, #0x21
        strb    w22, [x20, #3168]
        bl      L18f0
        mov     x1, x24
        mov     x0, x23
        mov     w2, #0x0
        bl      L2230
        add     x8, x20, #0x600
        add     x9, x21, #0x600
        add     x10, x21, #0x400
        add     x11, x21, #0x200
        mov     w0, #0x3
        strb    w0, [sp]
        mov     x19, x8
        mov     x3, x9
        mov     x2, x10
        mov     x1, x11
        mov     x4, x25
        mov     x0, x21
        mov     w7, #0x2
        mov     w6, #0x1
        mov     w5, #0x0
        stp     x11, x10, [sp, #152]
        str     x9, [sp, #168]
        bl      L2570
        add     x2, x20, #0x400
        mov     x4, x25
        mov     w5, w22
        mov     x3, x19
        mov     x1, x28
        mov     w0, #0x7
        strb    w0, [sp]
        mov     w7, #0x6
        mov     w6, #0x5
        mov     x0, x20
        str     x19, [sp, #128]
        mov     x22, x21
        str     x2, [sp, #144]
        bl      L2570
        mov     x0, x21
        bl      L1990
        ldr     x11, [sp, #152]
        add     x25, x27, #0x400
        mov     x19, x27
        mov     x0, x11
        bl      L1990
        ldr     x10, [sp, #160]
        mov     x0, x10
        bl      L1990
        ldr     x9, [sp, #168]
        mov     x0, x9
        bl      L1990
        mov     x0, x20
        bl      L1990
        mov     x0, x28
        bl      L1990
        ldr     x2, [sp, #144]
        mov     x0, x2
        bl      L1990
        ldr     x0, [sp, #128]
        bl      L1990
L283c:
        mov     x1, x26
        mov     x0, x19
        add     x19, x19, #0x100
        bl      L0c64
        add     x26, x26, #0x200
        cmp     x19, x25
        b.ne    L283c
        mov     x0, #0x2800
        add     x25, x23, x0
        mov     x28, x23
        mov     x26, x25
        mov     x19, x25
L286c:
        mov     x1, x28
        mov     x0, x19
        mov     x3, x27
        mov     x2, x21
        add     x19, x19, #0x200
        bl      L1830
        add     x28, x28, #0x800
        cmp     x19, x20
        b.ne    L286c
        .inst   0xf0000000  // adrp x0, 0x5000
        add     x8, x25, #0x200
        mvni    v3.8h, #0xd, lsl #8
        mov     x1, x8
        ldr     q4, [x0, #3312]
        .inst   0xf0000000  // adrp x0, 0x5000
        mov     w2, #0x4
        ldr     q5, [x0, #3200]
L28b0:
        sub     x0, x1, #0x200
        nop
L28b8:
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
        b.ne    L28b8
        add     x1, x0, #0x200
        subs    w2, w2, #0x1
        b.ne    L28b0
        mov     x2, x20
        mov     x1, x25
L28f8:
        mov     x0, #0x0
        nop
L2900:
        ldr     q0, [x1, x0]
        ldr     q1, [x2, x0]
        add     v0.8h, v0.8h, v1.8h
        str     q0, [x1, x0]
        add     x0, x0, #0x10
        cmp     x0, #0x200
        b.ne    L2900
        add     x1, x1, #0x200
        add     x2, x2, #0x200
        cmp     x1, x20
        b.ne    L28f8
        mov     x0, x25
        bl      L0c14
        add     x0, x25, #0x200
        bl      L0c14
        ldr     x19, [sp, #120]
        add     x0, x25, #0x400
        bl      L0c14
        add     x0, x25, #0x600
        bl      L0c14
        mov     x0, x21
        bl      L0c14
        add     x0, x21, #0x200
        bl      L0c14
        add     x0, x21, #0x400
        bl      L0c14
        add     x9, x19, #0x600
        add     x0, x21, #0x600
        bl      L0c14
L2974:
        mov     x1, x22
        mov     x0, x19
        add     x19, x19, #0x180
        bl      L0ad4
        add     x22, x22, #0x200
        cmp     x19, x9
        b.ne    L2974
        ldr     x5, [sp, #112]
        mov     x1, x26
        mov     x26, x8
        mov     x0, x5
        add     x6, x5, #0x600
        bl      L0ad4
        add     x5, x5, #0x180
        cmp     x6, x5
        b.eq    L29d4
L29b4:
        mov     x1, x26
        mov     x0, x5
        add     x8, x8, #0x200
        add     x5, x5, #0x180
        bl      L0ad4
        mov     x26, x8
        cmp     x6, x5
        b.ne    L29b4
L29d4:
        ldp     q0, q1, [x24]
        mov     x0, x27
        mov     x2, #0x400
        mov     w1, #0x0
        stp     q0, q1, [x6]
        bl      L0840
        mov     x2, #0x800
        mov     x0, x21
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x25
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x2000
        mov     x0, x23
        mov     w1, #0x0
        bl      L0840
        ldr     x0, [sp, #136]
        stp     xzr, xzr, [x0]
        stp     xzr, xzr, [x0, #16]
        strb    wzr, [x0, #32]
        movi    v0.4s, #0x0
        stp     q0, q0, [x24]
        stp     q0, q0, [x24, #32]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #15672]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L2a8c
        ldp     x19, x20, [sp, #16]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x3d40
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret
L2a8c:
        bl      L0830

// mlkem768_indcpa_keypair_derand (0x390 bytes)
L2a90:
        mov     x12, #0x2830
        sub     sp, sp, x12
        mov     x3, #0x2740
        mov     x4, #0x2700
        mov     x5, #0x1200
        mov     x6, #0x1e00
        stp     x19, x20, [sp, #16]
        add     x20, sp, #0xbf
        and     x20, x20, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        add     x22, x20, #0x2, lsl #12
        add     x21, x20, x4
        stp     x23, x24, [sp, #48]
        add     x19, x20, x5
        mov     w24, #0xffffffff
        stp     x25, x26, [sp, #64]
        add     x26, x20, x3
        mov     w25, #0x3
        stp     x27, x28, [sp, #80]
        add     x27, x20, x6
        add     x28, x19, #0x200
        str     x30, [sp, #96]
        add     x23, x21, #0x20
        stp     x0, x1, [sp, #128]
        mov     x1, x26
        ldp     q0, q1, [x2]
        .inst   0xb00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        ldr     x0, [x2]
        str     x0, [sp, #10280]
        mov     x0, #0x0
        stp     q0, q1, [x26]
        mov     x0, x21
        mov     x2, #0x21
        strb    w25, [x22, #1888]
        bl      L18f0
        mov     x1, x21
        mov     x0, x20
        mov     w2, #0x0
        bl      L1fb4
        strb    w24, [sp]
        add     x0, x19, #0x400
        mov     x4, x23
        mov     x2, x0
        mov     x1, x28
        mov     w7, #0x2
        mov     w6, #0x1
        mov     w5, #0x0
        mov     x3, #0x0
        stp     x0, x27, [sp, #112]
        mov     x0, x19
        bl      L2570
        strb    w24, [sp]
        mov     x4, x23
        mov     w5, w25
        mov     x8, #0x1800
        add     x2, x27, #0x400
        mov     x1, x22
        mov     x9, #0x2400
        mov     w7, #0x5
        mov     w6, #0x4
        mov     x3, #0x0
        add     x24, x20, x8
        add     x25, x20, x9
        mov     x0, x27
        str     x2, [sp, #152]
        bl      L2570
        mov     x0, x19
        bl      L1990
        mov     x0, x28
        str     x28, [sp, #144]
        bl      L1990
        mov     x23, x27
        ldr     x0, [sp, #112]
        mov     x27, x24
        mov     x28, x24
        bl      L1990
        mov     x0, x23
        bl      L1990
        mov     x0, x22
        bl      L1990
        ldr     x2, [sp, #152]
        mov     x23, x20
        mov     w22, #0x3
        mov     x0, x2
        bl      L1990
        mov     x1, x19
        mov     x0, x25
        bl      L0c64
        ldr     x1, [sp, #144]
        add     x0, x25, #0x100
        bl      L0c64
        ldr     x1, [sp, #112]
        add     x0, x25, #0x200
        bl      L0c64
L2c0c:
        mov     x1, x23
        mov     x0, x27
        mov     x3, x25
        mov     x2, x19
        bl      L1770
        add     x23, x23, #0x600
        add     x27, x27, #0x200
        subs    w22, w22, #0x1
        b.ne    L2c0c
        .inst   0xf0000000  // adrp x0, 0x5000
        add     x3, x24, #0x200
        mvni    v3.8h, #0xd, lsl #8
        mov     x1, x3
        ldr     q4, [x0, #3312]
        .inst   0xf0000000  // adrp x0, 0x5000
        mov     w2, #0x3
        ldr     q5, [x0, #3200]
L2c50:
        sub     x0, x1, #0x200
        nop
L2c58:
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
        b.ne    L2c58
        add     x1, x0, #0x200
        subs    w2, w2, #0x1
        b.ne    L2c50
        ldr     x1, [sp, #120]
L2c94:
        mov     x0, #0x0
L2c98:
        ldr     q0, [x28, x0]
        ldr     q1, [x1, x0]
        add     v0.8h, v0.8h, v1.8h
        str     q0, [x28, x0]
        add     x0, x0, #0x10
        cmp     x0, #0x200
        b.ne    L2c98
        add     w2, w2, #0x1
        add     x1, x1, #0x200
        mov     x28, x3
        cmp     w2, #0x3
        b.eq    L2cd0
        add     x3, x3, #0x200
        b       L2c94
L2cd0:
        add     x9, x24, #0x200
        mov     x0, x24
        bl      L0c14
        add     x8, x24, #0x400
        mov     x0, x9
        bl      L0c14
        mov     x0, x8
        bl      L0c14
        add     x11, x19, #0x200
        mov     x0, x19
        bl      L0c14
        add     x10, x19, #0x400
        mov     x0, x11
        bl      L0c14
        mov     x0, x10
        bl      L0c14
        ldr     x5, [sp, #136]
        mov     x1, x19
        mov     x0, x5
        bl      L0ad4
        mov     x1, x11
        add     x0, x5, #0x180
        bl      L0ad4
        mov     x1, x10
        add     x0, x5, #0x300
        bl      L0ad4
        ldr     x5, [sp, #128]
        mov     x1, x24
        mov     x0, x5
        bl      L0ad4
        mov     x1, x9
        add     x0, x5, #0x180
        bl      L0ad4
        add     x23, x5, #0x480
        mov     x1, x8
        add     x0, x5, #0x300
        bl      L0ad4
        ldp     q0, q1, [x21]
        mov     x0, x25
        mov     x2, #0x300
        mov     w1, #0x0
        stp     q0, q1, [x23]
        bl      L0840
        mov     x2, #0x600
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x600
        mov     x0, x24
        mov     w1, #0x0
        bl      L0840
        ldr     x19, [sp, #120]
        mov     x2, #0x600
        mov     w1, #0x0
        mov     x0, x19
        bl      L0840
        mov     x2, #0x1200
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        stp     xzr, xzr, [x26]
        stp     xzr, xzr, [x26, #16]
        strb    wzr, [x26, #32]
        movi    v0.4s, #0x0
        stp     q0, q0, [x21]
        stp     q0, q0, [x21, #32]
        .inst   0xb00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #10280]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L2e1c
        ldp     x19, x20, [sp, #16]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x2830
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret
L2e1c:
        bl      L0830

// mlkem512_indcpa_keypair_derand (0x3c0 bytes)
L2e20:
        mov     x12, #0x1720
        sub     sp, sp, x12
        mov     x3, #0x1640
        mov     x4, #0x1600
        mov     x5, #0x1400
        stp     x19, x20, [sp, #16]
        add     x19, sp, #0xaf
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        mov     x21, x0
        mov     w20, #0x2
        stp     x23, x24, [sp, #48]
        add     x23, x19, x3
        add     x24, x19, x5
        stp     x25, x26, [sp, #64]
        add     x26, x19, #0xc00
        add     x22, x19, #0xa00
        stp     x27, x28, [sp, #80]
        add     x27, x19, #0x1, lsl #12
        add     x28, x19, x4
        str     x30, [sp, #96]
        add     x25, x27, #0x200
        str     x1, [sp, #112]
        mov     x1, x23
        ldp     q0, q1, [x2]
        .inst   0xb00000e2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        ldr     x0, [x2]
        str     x0, [sp, #5912]
        mov     x0, #0x0
        stp     q0, q1, [x23]
        mov     x0, x28
        mov     x2, #0x21
        strb    w20, [x27, #1632]
        bl      L18f0
        mov     x1, x28
        mov     x0, x19
        mov     w2, #0x0
        bl      L1ef0
        ldp     q0, q1, [x28, #32]
        add     x6, x24, #0x40
        add     x7, x24, #0x80
        add     x0, x24, #0xc0
        add     x8, x19, #0xcc0
        add     x3, x19, #0xe40
        stp     q0, q1, [x24]
        mov     x5, x24
        add     x2, x19, #0xd80
        stp     q0, q1, [x6]
        mov     w10, #0x3
        mov     x4, #0xc0
        stp     q0, q1, [x7]
        mov     x1, x8
        str     x0, [sp]
        stp     x8, x2, [sp, #120]
        stp     q0, q1, [x0]
        mov     w0, #0x1
        strb    wzr, [x24, #32]
        strb    w0, [x24, #96]
        mov     x0, x26
        strb    w20, [x24, #160]
        add     x20, x19, #0x800
        strb    w10, [x24, #224]
        str     x3, [sp, #136]
        bl      L2380
        mov     x1, x26
        mov     x0, x20
        bl      L0f70
        ldr     x8, [sp, #120]
        mov     x0, x22
        mov     x1, x8
        bl      L0f70
        ldr     x2, [sp, #128]
        mov     x0, x27
        mov     x1, x2
        bl      L0f70
        ldr     x3, [sp, #136]
        mov     x0, x25
        mov     x1, x3
        bl      L0f70
        mov     x0, x26
        mov     x2, #0x300
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        stp     q0, q0, [x24]
        stp     q0, q0, [x24, #32]
        stp     q0, q0, [x24, #64]
        stp     q0, q0, [x24, #96]
        stp     q0, q0, [x24, #128]
        stp     q0, q0, [x24, #160]
        stp     q0, q0, [x24, #192]
        stp     q0, q0, [x24, #224]
        mvni    v3.8h, #0xd, lsl #8
        mov     x0, x20
        bl      L1990
        mov     x0, x22
        bl      L1990
        mov     x0, x27
        bl      L1990
        mov     x0, x25
        bl      L1990
        mov     x1, x20
        mov     x0, x24
        bl      L0c64
        add     x25, x19, #0xe00
        mov     x1, x22
        add     x0, x24, #0x100
        bl      L0c64
        mov     x3, x24
        mov     x2, x20
        mov     x1, x19
        mov     x0, x26
        bl      L0e30
        mov     x0, x25
        mov     x3, x24
        mov     x2, x20
        add     x1, x19, #0x400
        bl      L0e30
        .inst   0xf0000000  // adrp x0, 0x5000
        mov     x3, x26
        mov     x2, x26
        ldr     q4, [x0, #3312]
        .inst   0xd0000000  // adrp x0, 0x5000
        ldr     q5, [x0, #3200]
        nop
L3018:
        ldr     q0, [x2]
        smull   v1.4s, v0.4h, v4.4h
        smull2  v0.4s, v0.8h, v4.8h
        uzp1    v2.8h, v1.8h, v0.8h
        mul     v2.8h, v2.8h, v5.8h
        smlal   v1.4s, v2.4h, v3.4h
        smlal2  v0.4s, v2.8h, v3.8h
        uzp2    v1.8h, v1.8h, v0.8h
        str     q1, [x2], #16
        cmp     x2, x25
        b.ne    L3018
        .inst   0xd0000000  // adrp x0, 0x5000
        mov     x2, x25
        mvni    v3.8h, #0xd, lsl #8
        ldr     q4, [x0, #3312]
        .inst   0xd0000000  // adrp x0, 0x5000
        ldr     q5, [x0, #3200]
        add     x0, x26, #0x400
L3060:
        ldr     q0, [x2]
        smull   v1.4s, v0.4h, v4.4h
        smull2  v0.4s, v0.8h, v4.8h
        uzp1    v2.8h, v1.8h, v0.8h
        mul     v2.8h, v2.8h, v5.8h
        smlal   v1.4s, v2.4h, v3.4h
        smlal2  v0.4s, v2.8h, v3.8h
        uzp2    v1.8h, v1.8h, v0.8h
        str     q1, [x2], #16
        cmp     x2, x0
        b.ne    L3060
        mov     x0, x27
L3090:
        ldr     q1, [x0], #16
        ldr     q0, [x3]
        add     v0.8h, v0.8h, v1.8h
        str     q0, [x3], #16
        cmp     x3, x25
        b.ne    L3090
        mov     x8, #0x0
        nop
L30b0:
        add     x2, x26, x8
        add     x0, x27, x8
        add     x8, x8, #0x10
        ldr     q1, [x2, #512]
        ldr     q0, [x0, #512]
        add     v0.8h, v0.8h, v1.8h
        str     q0, [x2, #512]
        cmp     x8, #0x200
        b.ne    L30b0
        mov     x0, x26
        bl      L0c14
        mov     x0, x25
        bl      L0c14
        mov     x0, x20
        bl      L0c14
        mov     x0, x22
        bl      L0c14
        ldr     x5, [sp, #112]
        mov     x1, x20
        mov     x0, x5
        bl      L0ad4
        add     x0, x5, #0x180
        mov     x1, x22
        bl      L0ad4
        mov     x1, x26
        mov     x0, x21
        bl      L0ad4
        mov     x1, x25
        add     x0, x21, #0x180
        bl      L0ad4
        ldp     q0, q1, [x28]
        mov     x2, x8
        mov     x0, x24
        mov     w1, #0x0
        stp     q0, q1, [x21, #768]
        bl      L0840
        mov     x2, #0x400
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x400
        mov     x0, x26
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x400
        mov     x0, x27
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        stp     xzr, xzr, [x23]
        stp     xzr, xzr, [x23, #16]
        strb    wzr, [x23, #32]
        movi    v0.4s, #0x0
        stp     q0, q0, [x28]
        stp     q0, q0, [x28, #32]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #5912]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L31dc
        ldp     x19, x20, [sp, #16]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x1720
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret
L31dc:
        bl      L0830

// mlkem768_indcpa_enc (0x3c8 bytes)
L31e0:
        mov     x12, #0x33e0
        sub     sp, sp, x12
        .inst   0x900000e4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        add     x5, sp, #0xbf
        stp     x19, x20, [sp, #16]
        mov     x7, x2
        and     x19, x5, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        mov     x2, #0x1e00
        mov     x5, #0x2400
        stp     x23, x24, [sp, #48]
        mov     x6, #0x1800
        mov     x21, x3
        stp     x25, x26, [sp, #64]
        add     x26, x19, x2
        mov     x3, #0x2f00
        stp     x27, x28, [sp, #80]
        add     x20, x19, x5
        add     x9, x19, x3
        str     x30, [sp, #96]
        add     x24, x19, x6
        str     x0, [sp, #128]
        mov     x8, x1
        mov     x0, x26
        mov     x1, x7
        ldr     x2, [x4]
        str     x2, [sp, #13272]
        mov     x2, #0x0
        mov     x10, #0x3300
        add     x23, x20, #0x400
        add     x25, x20, #0x200
        mov     w27, #0x3
        bl      L0b10
        add     x1, x7, #0x180
        add     x0, x19, #0x2, lsl #12
        bl      L0b10
        str     x9, [sp, #112]
        add     x1, x7, #0x300
        add     x0, x26, #0x400
        bl      L0b10
        ldr     q0, [x7, #1152]
        add     x2, x19, x10
        ldr     q1, [x7, #1168]
        mov     x0, x9
        mov     x9, x2
        mov     x1, x8
        str     x2, [sp, #152]
        stp     q0, q1, [x2]
        bl      L0b50
        mov     x1, x9
        mov     x0, x19
        mov     w2, #0x1
        bl      L1fb4
        mov     x11, #0x2d00
        add     x8, x19, x11
        mov     w0, #0xffffffff
        strb    w0, [sp]
        mov     x22, x8
        mov     x2, x23
        mov     x1, x25
        mov     x4, x21
        mov     x0, x20
        mov     w7, #0x2
        mov     w6, #0x1
        mov     w5, #0x0
        mov     x3, #0x0
        str     x8, [sp, #120]
        bl      L2570
        mov     x4, x21
        mov     x3, x22
        add     x2, x24, #0x400
        add     x1, x24, #0x200
        mov     x12, #0x1200
        mov     x13, #0x2a00
        mov     w0, #0x6
        strb    w0, [sp]
        mov     w7, #0x5
        mov     w6, #0x4
        mov     w5, #0x3
        add     x22, x19, x13
        add     x21, x19, x12
        mov     x0, x24
        bl      L2570
        mov     x28, x21
        mov     x0, x20
        bl      L1990
        mov     x0, x25
        str     x25, [sp, #144]
        bl      L1990
        str     x23, [sp, #136]
        mov     x0, x23
        bl      L1990
        mov     x1, x20
        mov     x0, x22
        bl      L0c64
        mov     x25, x21
        ldr     x1, [sp, #144]
        add     x0, x22, #0x100
        mov     x23, x19
        bl      L0c64
        ldr     x1, [sp, #136]
        add     x0, x22, #0x200
        bl      L0c64
L3380:
        mov     x1, x23
        mov     x0, x25
        mov     x3, x22
        mov     x2, x20
        bl      L1770
        add     x23, x23, #0x600
        add     x25, x25, #0x200
        subs    w27, w27, #0x1
        b.ne    L3380
        mov     x1, x26
        mov     x3, x22
        mov     x2, x20
        mov     x0, #0x3100
        add     x23, x19, x0
        mov     x0, x23
        bl      L1770
        mov     x0, x21
        bl      L0ce0
        add     x0, x21, #0x200
        bl      L0ce0
        add     x0, x21, #0x400
        bl      L0ce0
        mov     x0, x23
        bl      L0ce0
        mov     x1, x24
L33e4:
        mov     x0, #0x0
L33e8:
        ldr     q0, [x28, x0]
        ldr     q1, [x1, x0]
        add     v0.8h, v0.8h, v1.8h
        str     q0, [x28, x0]
        add     x0, x0, #0x10
        cmp     x0, #0x200
        b.ne    L33e8
        add     w27, w27, #0x1
        add     x28, x28, #0x200
        add     x1, x1, #0x200
        cmp     w27, #0x3
        b.ne    L33e4
        ldr     x3, [sp, #120]
        mov     x0, x23
        add     x2, x23, #0x200
        mov     x1, x23
L3428:
        ldr     q1, [x3], #16
        ldr     q0, [x1]
        add     v0.8h, v0.8h, v1.8h
        str     q0, [x1], #16
        cmp     x1, x2
        b.ne    L3428
        ldr     x1, [sp, #112]
        nop
L3448:
        ldr     q1, [x1], #16
        ldr     q0, [x0]
        add     v0.8h, v0.8h, v1.8h
        str     q0, [x0], #16
        cmp     x2, x0
        b.ne    L3448
        mov     x0, x21
        add     x28, x21, #0x200
        bl      L0c14
        add     x27, x21, #0x400
        mov     x0, x28
        bl      L0c14
        mov     x0, x27
        bl      L0c14
        mov     x0, x23
        bl      L0c14
        ldr     x25, [sp, #128]
        mov     x1, x21
        mov     x0, x25
        bl      L0934
        mov     x1, x28
        add     x0, x25, #0x140
        bl      L0934
        mov     x1, x27
        add     x0, x25, #0x280
        bl      L0934
        mov     x1, x23
        add     x0, x25, #0x3c0
        bl      L0850
        mov     x0, x22
        mov     x2, #0x300
        mov     w1, #0x0
        bl      L0840
        ldr     x22, [sp, #120]
        mov     x2, #0x200
        mov     w1, #0x0
        mov     x0, x22
        bl      L0840
        ldr     x22, [sp, #112]
        mov     x2, #0x200
        mov     w1, #0x0
        mov     x0, x22
        bl      L0840
        mov     x2, #0x200
        mov     x0, x23
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x600
        mov     x0, x21
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
        mov     x2, #0x600
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x1200
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        ldr     x0, [sp, #152]
        stp     xzr, xzr, [x0]
        stp     xzr, xzr, [x0, #16]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #13272]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L35a4
        ldp     x19, x20, [sp, #16]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x33e0
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret
L35a4:
        bl      L0830
        nop
        nop

// mlkem_shake256 (0xd4 bytes)
L35b0:
        stp     x19, x20, [sp, #-320]!
        mov     x20, x1
        .inst   0x900000e4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        stp     x21, x22, [sp, #16]
        add     x21, sp, #0x5f
        stp     x23, x24, [sp, #32]
        and     x21, x21, #0xffffffffffffffe0
        mov     x22, x0
        str     x30, [sp, #48]
        mov     x0, x21
        mov     x24, #0x88
        mov     x23, #0x1
        ldr     x1, [x4]
        str     x1, [sp, #312]
        mov     x1, #0x0
        mov     w4, #0x1f
        mov     w1, #0x88
        bl      L1680
        nop
L3600:
        mov     x0, x21
        bl      L10b0
        cmp     x20, #0x88
        mov     x0, x22
        csel    x19, x20, x24, ls
        mov     x1, x21
        cmp     w19, #0x0
        add     x22, x22, x19
        csel    x2, x19, x23, ne
        bl      L0810
        subs    x20, x20, x19
        b.ne    L3600
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
        ldr     x2, [sp, #312]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3680
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #320
        ret
L3680:
        bl      L0830

// mlkem1024_poly_getnoise_eta2 (0xa4 bytes)

// mlkem512_poly_getnoise_eta2 (0xa4 bytes)
L3684:
        stp     x19, x20, [sp, #-240]!
        mov     x3, #0x21
        add     x19, sp, #0x3f
        stp     x21, x30, [sp, #16]
        and     x19, x19, #0xffffffffffffffe0
        .inst   0x900000e4  // adrp x4, 0x1f000
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
        bl      L35b0
        mov     x1, x19
        mov     x0, x21
        bl      L0ee4
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     xzr, xzr, [x19, #128]
        stp     xzr, xzr, [x20, #16]
        strb    wzr, [x20, #32]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3724
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #240
        ret
L3724:
        bl      L0830
        nop
        nop

// mlkem1024_indcpa_enc (0x5b0 bytes)
L3730:
        mov     x12, #0x4af0
        sub     sp, sp, x12
        add     x5, sp, #0xbf
        mov     x7, x2
        .inst   0x900000e4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        stp     x19, x20, [sp, #16]
        and     x20, x5, #0xffffffffffffffe0
        add     x8, x20, #0x3, lsl #12
        stp     x21, x22, [sp, #32]
        mov     x9, x1
        stp     x23, x24, [sp, #48]
        add     x10, x2, #0x600
        stp     x25, x26, [sp, #64]
        stp     x27, x28, [sp, #80]
        mov     x27, x3
        str     x30, [sp, #96]
        str     x0, [sp, #120]
        str     x8, [sp, #136]
        ldr     x0, [x4]
        str     x0, [sp, #19176]
        mov     x0, #0x0
L3788:
        mov     x1, x7
        mov     x0, x8
        add     x7, x7, #0x180
        bl      L0b10
        add     x8, x8, #0x200
        cmp     x7, x10
        b.ne    L3788
        ldp     q0, q1, [x7]
        mov     x28, #0x4a00
        add     x2, x20, x28
        mov     x30, #0x4600
        mov     x3, #0x2800
        mov     x24, x2
        add     x0, x20, x30
        mov     x1, x9
        stp     q0, q1, [x2]
        mov     x2, #0x3800
        add     x23, x20, x3
        add     x21, x20, x2
        str     x0, [sp, #128]
        bl      L0b50
        add     x25, x21, #0x400
        mov     x1, x24
        mov     x0, x20
        mov     w2, #0x1
        bl      L2230
        add     x8, x21, #0x600
        mov     w0, #0x3
        strb    w0, [sp]
        add     x26, x21, #0x200
        mov     x3, x8
        mov     x4, x27
        mov     x2, x25
        mov     x1, x26
        mov     x0, x21
        mov     w7, #0x2
        mov     w6, #0x1
        mov     w5, #0x0
        str     x8, [sp, #152]
        bl      L2570
        mov     w0, #0x7
        strb    w0, [sp]
        add     x3, x23, #0x600
        mov     w7, #0x6
        mov     w6, #0x5
        mov     w5, #0x4
        mov     x4, x27
        add     x2, x23, #0x400
        add     x1, x23, #0x200
        mov     x0, x23
        bl      L2570
        add     x22, x20, #0x4, lsl #12
        mov     x1, x27
        mov     x4, #0x4400
        mov     w2, #0x8
        add     x0, x20, x4
        str     x0, [sp, #144]
        bl      L3684
        mov     x0, x21
        bl      L1990
        mov     x0, x26
        bl      L1990
        mov     x0, x25
        bl      L1990
        ldr     x8, [sp, #152]
        mov     x19, x21
        add     x28, x22, #0x400
        mov     x27, x22
        mov     x0, x8
        bl      L1990
L38a0:
        mov     x1, x19
        mov     x0, x27
        add     x27, x27, #0x100
        bl      L0c64
        add     x19, x19, #0x200
        cmp     x27, x28
        b.ne    L38a0
        add     x25, x20, #0x2, lsl #12
        mov     x27, x20
        mov     x19, x25
        add     x28, x25, #0x800
        mov     x26, x25
L38d0:
        mov     x1, x27
        mov     x0, x26
        mov     x3, x22
        mov     x2, x21
        add     x26, x26, #0x200
        bl      L1830
        add     x27, x27, #0x800
        cmp     x26, x28
        b.ne    L38d0
        ldr     x1, [sp, #136]
        mov     x3, x22
        mov     x2, x21
        mov     x26, #0x4800
        add     x26, x20, x26
        mov     x0, x26
        bl      L1830
        mov     x0, x25
        bl      L0ce0
        add     x0, x25, #0x200
        bl      L0ce0
        add     x0, x25, #0x400
        bl      L0ce0
        add     x0, x25, #0x600
        bl      L0ce0
        mov     x0, x26
        bl      L0ce0
        mov     x1, x23
L393c:
        mov     x0, #0x0
L3940:
        ldr     q0, [x19, x0]
        ldr     q1, [x1, x0]
        add     v0.8h, v0.8h, v1.8h
        str     q0, [x19, x0]
        add     x0, x0, #0x10
        cmp     x0, #0x200
        b.ne    L3940
        add     x19, x19, #0x200
        add     x1, x1, #0x200
        cmp     x19, x28
        b.ne    L393c
        ldr     x3, [sp, #144]
        mov     x0, x26
        add     x2, x26, #0x200
        mov     x1, x26
        nop
L3980:
        ldr     q1, [x3], #16
        ldr     q0, [x1]
        add     v0.8h, v0.8h, v1.8h
        str     q0, [x1], #16
        cmp     x2, x1
        b.ne    L3980
        ldr     x1, [sp, #128]
        nop
L39a0:
        ldr     q1, [x1], #16
        ldr     q0, [x0]
        add     v0.8h, v0.8h, v1.8h
        str     q0, [x0], #16
        cmp     x2, x0
        b.ne    L39a0
        mov     x0, x25
        bl      L0c14
        add     x0, x25, #0x200
        bl      L0c14
        add     x0, x25, #0x400
        bl      L0c14
        add     x0, x25, #0x600
        bl      L0c14
        mov     x0, x26
        mov     x8, #0x7800
        bl      L0c14
        mov     x19, #0x4ad0
        ldr     x12, [sp, #120]
        movk    x8, #0x3afb, lsl #16
        add     x10, sp, x19
        mov     w11, #0x0
        movk    x8, #0x1, lsl #32
        mov     x7, #0x100000000
L3a00:
        mov     x9, x12
        ubfiz   x6, x11, #8, #32
        mov     w3, #0x8
        nop
L3a10:
        sub     w1, w3, #0x8
        mov     x2, x10
L3a18:
        add     x0, x6, w1, uxtw
        add     w1, w1, #0x1
        ldrsh   x0, [x25, x0, lsl #1]
        madd    x0, x0, x8, x7
        ubfx    x0, x0, #33, #11
        strh    w0, [x2], #2
        cmp     w3, w1
        b.ne    L3a18
        mov     x13, #0x4030
        add     x0, sp, x13
        mov     x16, #0x4030
        add     x1, sp, x16
        mov     x17, #0x4030
        mov     x18, #0x4030
        ldrh    w15, [x0, #2722]
        add     w3, w3, #0x8
        ldrh    w2, [x0, #2724]
        add     x9, x9, #0xb
        ldrh    w14, [x0, #2720]
        fmov    s0, w2
        lsl     w0, w15, #3
        ldrh    w13, [x1, #2726]
        ushr    v2.2s, v0.2s, #2
        fmov    d0, x14
        orr     w0, w0, w14, lsr #8
        lsl     w16, w2, #6
        orr     w16, w16, w15, lsr #5
        lsl     w15, w13, #1
        mov     v0.b[1], w0
        orr     w14, w15, w2, lsr #10
        ldrh    w1, [x1, #2728]
        add     x0, sp, x17
        mov     v0.b[2], w16
        lsl     w2, w1, #4
        ldrh    w0, [x0, #2730]
        orr     w15, w2, w13, lsr #7
        fmov    s1, w0
        add     x2, sp, x18
        mov     v0.b[3], v2.b[0]
        lsl     w16, w0, #7
        orr     w1, w16, w1, lsr #4
        ushr    v1.2s, v1.2s, #1
        ldrh    w13, [x2, #2732]
        ldrh    w2, [x2, #2734]
        mov     v0.b[4], w14
        lsl     w17, w13, #2
        lsl     w16, w2, #5
        orr     w0, w17, w0, lsr #9
        orr     w13, w16, w13, lsr #6
        lsr     w2, w2, #3
        mov     v0.b[5], w15
        sturb   w0, [x9, #-3]
        sturb   w13, [x9, #-2]
        sturb   w2, [x9, #-1]
        mov     v0.b[6], w1
        mov     v0.b[7], v1.b[0]
        stur    d0, [x9, #-11]
        cmp     w3, #0x108
        b.ne    L3a10
        add     w11, w11, #0x1
        add     x12, x12, #0x160
        cmp     w11, #0x4
        b.ne    L3a00
        ldr     x0, [sp, #120]
        mov     x5, #0x4ae0
        mov     w7, #0xafc0
        add     x8, sp, x5
        add     x19, x0, #0x580
        mov     w9, #0x0
        movk    w7, #0x13, lsl #16
        mov     w6, #0x4000000
        nop
L3b38:
        sub     w3, w9, #0x1
        mov     x1, #0x1
        str     xzr, [sp, #19168]
        nop
L3b48:
        add     w0, w3, w1
        add     x2, x8, x1
        add     x1, x1, #0x1
        ldrsh   w0, [x26, x0, lsl #1]
        madd    w0, w0, w7, w6
        lsr     w0, w0, #27
        sturb   w0, [x2, #-1]
        cmp     x1, #0x9
        b.ne    L3b48
        mov     x0, #0x4030
        add     x0, sp, x0
        mov     x1, #0x4030
        mov     x4, #0x4030
        add     x1, sp, x1
        add     x4, sp, x4
        ldrb    w2, [x0, #2739]
        add     w9, w9, #0x8
        ldrb    w10, [x0, #2742]
        add     x19, x19, #0x5
        ldrb    w0, [x0, #2738]
        lsl     w3, w2, #7
        ldrb    w1, [x1, #2740]
        ldrb    w12, [x4, #2741]
        lsl     w15, w10, #6
        orr     w0, w3, w0, lsl #2
        ldrb    w13, [x4, #2736]
        ldrb    w3, [x4, #2737]
        lsl     w14, w1, #4
        ldrb    w11, [x4, #2743]
        lsr     w10, w10, #2
        orr     w12, w15, w12, lsl #1
        orr     w2, w14, w2, lsr #1
        orr     w0, w0, w3, lsr #3
        orr     w1, w12, w1, lsr #4
        orr     w10, w10, w11, lsl #3
        orr     w3, w13, w3, lsl #5
        sturb   w3, [x19, #-5]
        sturb   w0, [x19, #-4]
        sturb   w2, [x19, #-3]
        sturb   w1, [x19, #-2]
        sturb   w10, [x19, #-1]
        cmp     w9, #0x100
        b.ne    L3b38
        mov     x0, x22
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0840
        ldr     x19, [sp, #144]
        mov     x2, #0x200
        mov     w1, #0x0
        mov     x0, x19
        bl      L0840
        ldr     x19, [sp, #128]
        mov     x2, #0x200
        mov     w1, #0x0
        mov     x0, x19
        bl      L0840
        mov     x2, #0x200
        mov     x0, x26
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x25
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x23
        mov     w1, #0x0
        bl      L0840
        ldr     x19, [sp, #136]
        mov     x2, #0x800
        mov     w1, #0x0
        mov     x0, x19
        bl      L0840
        mov     x2, #0x800
        mov     x0, x21
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x2000
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        stp     xzr, xzr, [x24]
        stp     xzr, xzr, [x24, #16]
        .inst   0x900000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #19176]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L3cdc
        ldp     x19, x20, [sp, #16]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x4af0
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret
L3cdc:
        bl      L0830

// mlkem512_indcpa_enc (0x3e0 bytes)
L3ce0:
        mov     x12, #0x20d0
        sub     sp, sp, x12
        .inst   0x900000e4  // adrp x4, 0x1f000
        ldr     x4, [x4, #4088]
        mov     x8, x1
        stp     x19, x20, [sp, #16]
        add     x20, sp, #0xaf
        and     x20, x20, #0xffffffffffffffe0
        stp     x21, x22, [sp, #32]
        mov     x7, x2
        mov     x1, x2
        stp     x23, x24, [sp, #48]
        mov     x2, #0x1800
        mov     x19, x3
        stp     x25, x26, [sp, #64]
        mov     x3, #0x1400
        add     x23, x20, #0x1, lsl #12
        stp     x27, x28, [sp, #80]
        add     x27, x20, x2
        add     x21, x20, x3
        str     x30, [sp, #96]
        add     x28, x20, #0x2, lsl #12
        str     x0, [sp, #136]
        mov     x0, x23
        add     x26, x20, #0xa40
        add     x25, x20, #0x800
        ldr     x2, [x4]
        str     x2, [sp, #8392]
        mov     x2, #0x0
        add     x24, x20, #0x8c0
        add     x22, x21, #0x200
        bl      L0b10
        add     x1, x7, #0x180
        add     x0, x23, #0x200
        bl      L0b10
        ldp     q0, q1, [x7, #768]
        mov     x4, #0x1c00
        mov     x1, x8
        add     x0, x20, x4
        str     x0, [sp, #120]
        stp     q0, q1, [x28]
        bl      L0b50
        mov     x1, x28
        mov     x0, x20
        mov     w2, #0x1
        bl      L1ef0
        ldp     q0, q1, [x19]
        add     x6, x27, #0x40
        add     x7, x27, #0x80
        add     x0, x27, #0xc0
        mov     x5, x27
        mov     x3, x26
        stp     q0, q1, [x27]
        add     x2, x20, #0x980
        mov     w11, #0x2
        stp     q0, q1, [x6]
        mov     w10, #0x3
        mov     w1, #0x1
        stp     q0, q1, [x7]
        mov     x4, #0xc0
        str     x0, [sp]
        str     x2, [sp, #128]
        stp     q0, q1, [x0]
        mov     x0, x25
        strb    wzr, [x27, #32]
        strb    w1, [x27, #96]
        mov     x1, x24
        strb    w11, [x27, #160]
        strb    w10, [x27, #224]
        bl      L2380
        mov     x1, x25
        mov     x0, x21
        bl      L0f70
        mov     x1, x24
        mov     x0, x22
        bl      L0f70
        add     x24, x20, #0xc00
        ldr     x2, [sp, #128]
        mov     x0, x24
        mov     x1, x2
        bl      L0ee4
        mov     x1, x26
        add     x0, x20, #0xe00
        bl      L0ee4
        mov     x0, x25
        mov     x2, #0x300
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        stp     q0, q0, [x27]
        stp     q0, q0, [x27, #32]
        stp     q0, q0, [x27, #64]
        stp     q0, q0, [x27, #96]
        stp     q0, q0, [x27, #128]
        stp     q0, q0, [x27, #160]
        stp     q0, q0, [x27, #192]
        stp     q0, q0, [x27, #224]
        mov     x5, #0x1a00
        mov     x1, x19
        mov     w2, #0x4
        add     x0, x20, x5
        str     x0, [sp, #128]
        bl      L3684
        mov     x0, x21
        bl      L1990
        mov     x0, x22
        bl      L1990
        mov     x1, x21
        mov     x0, x27
        bl      L0c64
        add     x26, x20, #0xa00
        mov     x1, x22
        add     x0, x27, #0x100
        bl      L0c64
        mov     x3, x27
        mov     x2, x21
        mov     x1, x20
        mov     x0, x25
        bl      L0e30
        mov     x6, #0x1e00
        mov     x0, x26
        add     x22, x20, x6
        mov     x3, x27
        mov     x2, x21
        add     x1, x20, #0x400
        bl      L0e30
        mov     x1, x23
        mov     x3, x27
        mov     x2, x21
        mov     x0, x22
        bl      L0e30
        mov     x0, x25
        bl      L0ce0
        mov     x0, x26
        bl      L0ce0
        mov     x0, x22
        bl      L0ce0
        mov     x1, x25
        mov     x0, x24
        nop
L3f10:
        ldr     q1, [x0], #16
        ldr     q0, [x1]
        add     v0.8h, v0.8h, v1.8h
        str     q0, [x1], #16
        cmp     x1, x26
        b.ne    L3f10
        mov     x1, #0x0
        nop
L3f30:
        add     x0, x25, x1
        add     x2, x24, x1
        add     x1, x1, #0x10
        ldr     q1, [x0, #512]
        ldr     q0, [x2, #512]
        add     v0.8h, v0.8h, v1.8h
        str     q0, [x0, #512]
        cmp     x1, #0x200
        b.ne    L3f30
        ldr     x1, [sp, #128]
        mov     x19, x22
        mov     x0, x22
L3f60:
        ldr     q1, [x1], #16
        ldr     q0, [x0]
        add     v0.8h, v0.8h, v1.8h
        str     q0, [x0], #16
        cmp     x0, x28
        b.ne    L3f60
        ldr     x0, [sp, #120]
        nop
L3f80:
        ldr     q1, [x0], #16
        ldr     q0, [x19]
        add     v0.8h, v0.8h, v1.8h
        str     q0, [x19], #16
        cmp     x19, x28
        b.ne    L3f80
        mov     x0, x25
        bl      L0c14
        mov     x0, x26
        bl      L0c14
        mov     x0, x22
        bl      L0c14
        ldr     x28, [sp, #136]
        mov     x1, x25
        mov     x0, x28
        bl      L0934
        mov     x1, x26
        add     x0, x28, #0x140
        bl      L0934
        mov     x1, x22
        add     x0, x28, #0x280
        bl      L0850
        mov     x0, x27
        mov     x2, #0x200
        mov     w1, #0x0
        bl      L0840
        ldr     x26, [sp, #128]
        mov     x2, #0x200
        mov     w1, #0x0
        mov     x0, x26
        bl      L0840
        ldr     x26, [sp, #120]
        mov     x2, #0x200
        mov     w1, #0x0
        mov     x0, x26
        bl      L0840
        mov     x2, #0x200
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
        mov     x0, x23
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x400
        mov     x0, x21
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x20
        mov     w1, #0x0
        bl      L0840
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #8392]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L40bc
        ldp     x19, x20, [sp, #16]
        mov     w0, #0x0
        ldp     x21, x22, [sp, #32]
        mov     x12, #0x20d0
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldr     x30, [sp, #96]
        add     sp, sp, x12
        ret
L40bc:
        bl      L0830

// mlkem_sha3_256 (0x98 bytes)
L40c0:
        stp     x19, x20, [sp, #-240]!
        mov     x3, x2
        mov     x2, x1
        .inst   0xf00000c5  // adrp x5, 0x1f000
        ldr     x5, [x5, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x20
        mov     w4, #0x6
        ldr     x6, [x5]
        str     x6, [sp, #232]
        mov     x6, #0x0
        mov     w1, #0x88
        mov     x20, x0
        mov     x0, x19
        bl      L1680
        movi    v0.4s, #0x0
        mov     x0, x19
        bl      L10b0
        str     xzr, [x19, #192]
        ldp     q1, q2, [x19]
        stp     q0, q0, [x19]
        stp     q1, q2, [x20]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x19, #64]
        stp     q0, q0, [x19, #96]
        stp     q0, q0, [x19, #128]
        stp     q0, q0, [x19, #160]
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4154
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #240
        ret
L4154:
        bl      L0830
        nop
        nop

// mlkem512_check_pk (0x158 bytes)
L4160:
        sub     sp, sp, #0x740
        mov     x8, x0
        .inst   0xf00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        mov     x1, x0
        stp     x19, x20, [sp]
        add     x19, sp, #0x3f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x30, [sp, #16]
        mov     x0, x19
        add     x9, x19, #0x200
        ldr     x3, [x2]
        str     x3, [sp, #1848]
        mov     x3, #0x0
        add     x20, x19, #0x400
        movi    v2.4s, #0x0
        bl      L0b10
        add     x1, x8, #0x180
        mov     x0, x9
        mov     v3.16b, v2.16b
        bl      L0b10
        mov     x0, x19
        bl      L0c14
        mov     x0, x9
        bl      L0c14
        mov     x0, x20
        mov     x1, x19
        bl      L0ad4
        mov     x1, x9
        add     x0, x19, #0x580
        bl      L0ad4
        mov     x0, x8
        mov     x2, x20
        add     x1, x19, #0x700
L41e8:
        ldr     q0, [x0], #16
        ldr     q1, [x2], #16
        eor     v0.16b, v0.16b, v1.16b
        orr     v3.16b, v3.16b, v0.16b
        eor     v2.16b, v2.16b, v0.16b
        cmp     x1, x2
        b.ne    L41e8
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
        mov     x0, x20
        mov     w1, #0x0
        mov     w21, #0xfffffffc
        csel    w21, wzr, w21, eq
        bl      L0840
        mov     x2, #0x400
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #1848]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L42b4
        ldp     x19, x20, [sp]
        mov     w0, w21
        ldp     x21, x30, [sp, #16]
        add     sp, sp, #0x740
        ret
L42b4:
        bl      L0830
        nop
        nop

// mlkem512_check_sk (0xe8 bytes)
L42c0:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        add     x1, x0, #0x300
        .inst   0xf00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x3f
        mov     x2, #0x320
        ldr     x4, [x3]
        str     x4, [sp, #88]
        mov     x4, #0x0
        and     x19, x19, #0xffffffffffffffe0
        mov     x0, x19
        bl      L40c0
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
        .inst   0xf00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #88]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L43a4
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #96
        ret
L43a4:
        bl      L0830
        nop
        nop

// mlkem512_keypair_derand (0x94 bytes)
L43b0:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        mov     x21, x0
        str     x30, [sp, #32]
        bl      L2e20
        mov     x2, #0x320
        mov     w20, w0
        cbnz    w0, L4414
        mov     x1, x21
        add     x0, x19, #0x300
        bl      L0810
        mov     x1, x21
        add     x0, x19, #0x620
        mov     x2, #0x320
        bl      L40c0
        ldp     q0, q1, [x22, #32]
        add     x19, x19, #0x640
        mov     w0, w20
        stp     q0, q1, [x19]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L4414:
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
L4444:
        stp     x19, x20, [sp, #-128]!
        mov     x20, x0
        .inst   0xf00000c2  // adrp x2, 0x1f000
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
        cbnz    w0, L44c4
        mov     x1, x21
        mov     x0, x20
        mov     x2, x19
        bl      L43b0
L4490:
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xf00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #120]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L44cc
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #128
        ret
L44c4:
        mov     w0, #0xfffffffd
        b       L4490
L44cc:
        bl      L0830

// mlkem512_enc_derand (0xe0 bytes)
L44d0:
        stp     x19, x20, [sp, #-224]!
        .inst   0xf00000c4  // adrp x4, 0x1f000
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
        bl      L4160
        cbz     w0, L4560
L451c:
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        .inst   0xf00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #216]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L45ac
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #224
        ret
L4560:
        ldp     q0, q1, [x22]
        mov     x1, x21
        add     x0, x19, #0x60
        mov     x2, #0x320
        stp     q0, q1, [x20]
        bl      L40c0
        mov     x1, x20
        mov     x0, x19
        mov     x2, #0x40
        bl      L18f0
        mov     x2, x21
        mov     x0, x24
        add     x3, x19, #0x20
        mov     x1, x20
        bl      L3ce0
        cbnz    w0, L451c
        ldp     q0, q1, [x19]
        stp     q0, q1, [x23]
        b       L451c
L45ac:
        bl      L0830

// mlkem512_enc (0x98 bytes)
L45b0:
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
        bl      L0820
        cbnz    w0, L463c
        mov     x2, x22
        mov     x1, x21
        mov     x0, x20
        mov     x3, x19
        bl      L44d0
L4608:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xf00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #104]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L4644
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret
L463c:
        mov     w0, #0xfffffffd
        b       L4608
L4644:
        bl      L0830
        nop
        nop

// mlkem512_dec (0x334 bytes)
L4650:
        mov     x12, #0x1210
        sub     sp, sp, x12
        .inst   0xf00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x6f
        mov     x20, x2
        stp     x21, x22, [sp, #16]
        mov     x22, x1
        mov     x21, x0
        stp     x23, x24, [sp, #32]
        mov     x0, x2
        and     x19, x19, #0xffffffffffffffe0
        stp     x25, x26, [sp, #48]
        stp     x27, x30, [sp, #64]
        ldr     x1, [x3]
        str     x1, [sp, #4616]
        mov     x1, #0x0
        bl      L42c0
        cbz     w0, L471c
        mov     x3, #0x1160
        mov     x4, #0x1120
        mov     w24, w0
        add     x27, x19, x3
        add     x23, x19, x4
        add     x25, x19, #0x800
L46b8:
        mov     x0, x25
        mov     x2, #0x320
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        stp     q0, q0, [x23]
        stp     q0, q0, [x23, #32]
        stp     q0, q0, [x27]
        stp     q0, q0, [x27, #32]
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #4616]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4980
        ldp     x19, x20, [sp]
        mov     w0, w24
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x1210
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x30, [sp, #64]
        add     sp, sp, x12
        ret
L471c:
        add     x24, x19, #0x400
        add     x27, x19, #0x600
        mov     x1, x22
        mov     x0, x24
        bl      L0a50
        add     x23, x19, #0xf20
        mov     x0, x27
        add     x1, x22, #0x140
        bl      L0a50
        add     x26, x19, #0xb20
        mov     x0, x23
        add     x1, x22, #0x280
        bl      L0a04
        add     x25, x19, #0xd20
        mov     x1, x20
        mov     x0, x19
        bl      L0b10
        add     x1, x20, #0x180
        add     x0, x19, #0x200
        bl      L0b10
        mov     x0, x24
        bl      L1990
        mov     x0, x27
        bl      L1990
        mov     x1, x24
        mov     x0, x26
        bl      L0c64
        mov     x1, x27
        add     x0, x19, #0xc20
        bl      L0c64
        mov     x3, x26
        mov     x2, x24
        mov     x1, x19
        mov     x0, x25
        bl      L0e30
        mov     x0, x25
        bl      L0ce0
        mov     x3, x23
        mov     x4, x25
        add     x0, x23, #0x200
        nop
L47c0:
        ldr     q1, [x4], #16
        ldr     q0, [x3]
        sub     v0.8h, v0.8h, v1.8h
        str     q0, [x3], #16
        cmp     x3, x0
        b.ne    L47c0
        mov     x1, #0x1160
        mov     x0, x23
        add     x27, x19, x1
        bl      L0c14
        mov     x0, x27
        mov     x1, x23
        bl      L0bb0
        mov     x0, x26
        mov     x2, #0x200
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x25
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x23
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x400
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x400
        mov     x0, x24
        mov     w1, #0x0
        bl      L0840
        ldr     q0, [x20, #1568]
        mov     x2, #0x1120
        ldr     q1, [x20, #1584]
        add     x23, x19, x2
        mov     x0, x23
        mov     x1, x27
        mov     x2, #0x40
        add     x25, x19, #0x800
        stp     q0, q1, [x27, #32]
        bl      L18f0
        add     x3, x23, #0x20
        mov     x0, x25
        add     x2, x20, #0x300
        mov     x1, x27
        bl      L3ce0
        mov     w24, w0
        cbnz    w0, L46b8
        movi    v1.4s, #0x0
        mov     x0, x25
        mov     x1, x22
        add     x2, x19, #0xb00
        mov     v2.16b, v1.16b
L489c:
        ldr     q0, [x1], #16
        ldr     q3, [x0], #16
        eor     v0.16b, v0.16b, v3.16b
        orr     v2.16b, v2.16b, v0.16b
        eor     v1.16b, v1.16b, v0.16b
        cmp     x2, x0
        b.ne    L489c
        movi    v3.4s, #0x0
        ext     v4.16b, v2.16b, v3.16b, #8
        ext     v0.16b, v1.16b, v3.16b, #8
        orr     v4.16b, v4.16b, v2.16b
        eor     v2.16b, v0.16b, v1.16b
        ext     v1.16b, v4.16b, v3.16b, #4
        ext     v0.16b, v2.16b, v3.16b, #4
        orr     v1.16b, v1.16b, v4.16b
        eor     v0.16b, v0.16b, v2.16b
        ext     v4.16b, v1.16b, v3.16b, #2
        ext     v2.16b, v0.16b, v3.16b, #2
        orr     v4.16b, v4.16b, v1.16b
        eor     v2.16b, v2.16b, v0.16b
        ext     v0.16b, v4.16b, v3.16b, #1
        ext     v1.16b, v2.16b, v3.16b, #1
        orr     v0.16b, v0.16b, v4.16b
        eor     v1.16b, v1.16b, v2.16b
        umov    w0, v0.b[0]
        umov    w1, v1.b[0]
        neg     w0, w0
        eor     w0, w1, w0, asr #16
        ldr     q0, [x20, #1600]
        and     w0, w0, #0xff
        ldr     q1, [x20, #1616]
        mov     x2, #0x300
        eor     w20, w0, w1
        mov     x1, x22
        add     x0, x19, #0x820
        stp     q0, q1, [x25]
        bl      L0810
        mov     x0, x21
        mov     x2, x25
        mov     x3, #0x320
        mov     x1, #0x20
        bl      L35b0
        neg     w4, w20
        sub     x21, x21, #0x1
        mov     x0, #0x1
L4950:
        add     x2, x0, x23
        mov     w1, w4
        ldurb   w2, [x2, #-1]
        ldrb    w3, [x21, x0]
        eor     w3, w2, w3
        and     w1, w3, w1, asr #16
        eor     w2, w2, w1
        strb    w2, [x21, x0]
        add     x0, x0, #0x1
        cmp     x0, #0x21
        b.ne    L4950
        b       L46b8
L4980:
        bl      L0830

// mlkem768_check_pk (0x17c bytes)
L4984:
        sub     sp, sp, #0xac0
        mov     x8, x0
        .inst   0xf00000c2  // adrp x2, 0x1f000
        ldr     x2, [x2, #4088]
        mov     x1, x0
        stp     x19, x20, [sp]
        add     x19, sp, #0x3f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x30, [sp, #16]
        add     x10, x19, #0x200
        mov     x0, x19
        ldr     x3, [x2]
        str     x3, [sp, #2744]
        mov     x3, #0x0
        add     x9, x19, #0x400
        movi    v2.4s, #0x0
        add     x20, x19, #0x600
        bl      L0b10
        mov     x0, x10
        add     x1, x8, #0x180
        mov     v3.16b, v2.16b
        bl      L0b10
        add     x1, x8, #0x300
        mov     x0, x9
        bl      L0b10
        mov     x0, x19
        bl      L0c14
        mov     x0, x10
        bl      L0c14
        mov     x0, x9
        bl      L0c14
        mov     x0, x20
        mov     x1, x19
        bl      L0ad4
        mov     x1, x10
        add     x0, x19, #0x780
        bl      L0ad4
        mov     x1, x9
        add     x0, x19, #0x900
        bl      L0ad4
        mov     x0, x8
        mov     x1, x20
        add     x2, x19, #0xa80
L4a30:
        ldr     q0, [x0], #16
        ldr     q1, [x1], #16
        eor     v0.16b, v0.16b, v1.16b
        orr     v3.16b, v3.16b, v0.16b
        eor     v2.16b, v2.16b, v0.16b
        cmp     x2, x1
        b.ne    L4a30
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
        mov     x0, x20
        mov     w1, #0x0
        mov     w21, #0xfffffffc
        csel    w21, wzr, w21, eq
        bl      L0840
        mov     x2, #0x600
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #2744]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L4afc
        ldp     x19, x20, [sp]
        mov     w0, w21
        ldp     x21, x30, [sp, #16]
        add     sp, sp, #0xac0
        ret
L4afc:
        bl      L0830

// mlkem768_check_sk (0xe8 bytes)
L4b00:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        add     x1, x0, #0x480
        .inst   0xf00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x3f
        mov     x2, #0x4a0
        ldr     x4, [x3]
        str     x4, [sp, #88]
        mov     x4, #0x0
        and     x19, x19, #0xffffffffffffffe0
        mov     x0, x19
        bl      L40c0
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
        .inst   0xf00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #88]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L4be4
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #96
        ret
L4be4:
        bl      L0830
        nop
        nop

// mlkem768_keypair_derand (0x94 bytes)
L4bf0:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        mov     x21, x0
        str     x30, [sp, #32]
        bl      L2a90
        mov     x2, #0x4a0
        mov     w20, w0
        cbnz    w0, L4c54
        mov     x1, x21
        add     x0, x19, #0x480
        bl      L0810
        mov     x1, x21
        add     x0, x19, #0x920
        mov     x2, #0x4a0
        bl      L40c0
        ldp     q0, q1, [x22, #32]
        add     x19, x19, #0x940
        mov     w0, w20
        stp     q0, q1, [x19]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L4c54:
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
L4c84:
        stp     x19, x20, [sp, #-128]!
        mov     x20, x0
        .inst   0xf00000c2  // adrp x2, 0x1f000
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
        cbnz    w0, L4d04
        mov     x1, x21
        mov     x0, x20
        mov     x2, x19
        bl      L4bf0
L4cd0:
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xf00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #120]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L4d0c
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #128
        ret
L4d04:
        mov     w0, #0xfffffffd
        b       L4cd0
L4d0c:
        bl      L0830

// mlkem768_enc_derand (0xe0 bytes)
L4d10:
        stp     x19, x20, [sp, #-224]!
        .inst   0xf00000c4  // adrp x4, 0x1f000
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
        bl      L4984
        cbz     w0, L4da0
L4d5c:
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        .inst   0xf00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #216]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L4dec
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #224
        ret
L4da0:
        ldp     q0, q1, [x22]
        mov     x1, x21
        add     x0, x19, #0x60
        mov     x2, #0x4a0
        stp     q0, q1, [x20]
        bl      L40c0
        mov     x1, x20
        mov     x0, x19
        mov     x2, #0x40
        bl      L18f0
        mov     x2, x21
        mov     x0, x24
        add     x3, x19, #0x20
        mov     x1, x20
        bl      L31e0
        cbnz    w0, L4d5c
        ldp     q0, q1, [x19]
        stp     q0, q1, [x23]
        b       L4d5c
L4dec:
        bl      L0830

// mlkem768_enc (0x98 bytes)
L4df0:
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
        bl      L0820
        cbnz    w0, L4e7c
        mov     x2, x22
        mov     x1, x21
        mov     x0, x20
        mov     x3, x19
        bl      L4d10
L4e48:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xf00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #104]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L4e84
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret
L4e7c:
        mov     w0, #0xfffffffd
        b       L4e48
L4e84:
        bl      L0830
        nop
        nop

// mlkem768_dec (0x374 bytes)
L4e90:
        mov     x12, #0x1860
        sub     sp, sp, x12
        .inst   0xf00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        add     x19, sp, #0x7f
        mov     x20, x2
        stp     x21, x22, [sp, #16]
        mov     x21, x1
        mov     x22, x0
        stp     x23, x24, [sp, #32]
        mov     x0, x2
        and     x19, x19, #0xffffffffffffffe0
        stp     x25, x26, [sp, #48]
        stp     x27, x28, [sp, #64]
        str     x30, [sp, #80]
        ldr     x1, [x3]
        str     x1, [sp, #6232]
        mov     x1, #0x0
        bl      L4b00
        cbz     w0, L4f64
        mov     x6, #0x17a0
        mov     x7, #0x1760
        mov     w24, w0
        add     x27, x19, x6
        add     x23, x19, x7
        add     x25, x19, #0xc00
L4efc:
        mov     x0, x25
        mov     x2, #0x460
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        stp     q0, q0, [x23]
        stp     q0, q0, [x23, #32]
        stp     q0, q0, [x27]
        stp     q0, q0, [x27, #32]
        .inst   0xf00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #6232]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L5200
        ldp     x19, x20, [sp]
        mov     w0, w24
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x1860
        ldp     x23, x24, [sp, #32]
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret
L4f64:
        add     x24, x19, #0x600
        add     x28, x19, #0x800
        mov     x1, x21
        mov     x0, x24
        bl      L0a50
        add     x27, x19, #0xa00
        mov     x0, x28
        add     x1, x21, #0x140
        bl      L0a50
        mov     x3, #0x1560
        mov     x0, x27
        add     x23, x19, x3
        add     x1, x21, #0x280
        bl      L0a50
        mov     x4, #0x1060
        mov     x0, x23
        add     x25, x19, x4
        add     x1, x21, #0x3c0
        bl      L0a04
        mov     x1, x20
        mov     x0, x19
        bl      L0b10
        add     x1, x20, #0x180
        add     x0, x19, #0x200
        bl      L0b10
        mov     x5, #0x1360
        add     x1, x20, #0x300
        add     x26, x19, x5
        add     x0, x19, #0x400
        bl      L0b10
        mov     x0, x24
        bl      L1990
        mov     x0, x28
        bl      L1990
        mov     x0, x27
        bl      L1990
        mov     x1, x24
        mov     x0, x25
        bl      L0c64
        mov     x1, x28
        add     x0, x25, #0x100
        bl      L0c64
        mov     x1, x27
        add     x0, x25, #0x200
        bl      L0c64
        mov     x3, x25
        mov     x2, x24
        mov     x1, x19
        mov     x0, x26
        bl      L1770
        mov     x0, x26
        bl      L0ce0
        mov     x3, x23
        mov     x4, x26
        add     x0, x23, #0x200
L5040:
        ldr     q1, [x4], #16
        ldr     q0, [x3]
        sub     v0.8h, v0.8h, v1.8h
        str     q0, [x3], #16
        cmp     x3, x0
        b.ne    L5040
        mov     x1, #0x17a0
        mov     x0, x23
        add     x27, x19, x1
        bl      L0c14
        mov     x0, x27
        mov     x1, x23
        bl      L0bb0
        mov     x0, x25
        mov     x2, #0x300
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x26
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x23
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x600
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x600
        mov     x0, x24
        mov     w1, #0x0
        bl      L0840
        ldr     q0, [x20, #2336]
        mov     x2, #0x1760
        ldr     q1, [x20, #2352]
        add     x23, x19, x2
        mov     x0, x23
        mov     x1, x27
        mov     x2, #0x40
        add     x25, x19, #0xc00
        stp     q0, q1, [x27, #32]
        bl      L18f0
        add     x3, x23, #0x20
        mov     x0, x25
        add     x2, x20, #0x480
        mov     x1, x27
        bl      L31e0
        mov     w24, w0
        cbnz    w0, L4efc
        movi    v1.4s, #0x0
        mov     x0, x25
        mov     x1, x21
        add     x2, x25, #0x440
        mov     v2.16b, v1.16b
L511c:
        ldr     q0, [x1], #16
        ldr     q3, [x0], #16
        eor     v0.16b, v0.16b, v3.16b
        orr     v2.16b, v2.16b, v0.16b
        eor     v1.16b, v1.16b, v0.16b
        cmp     x2, x0
        b.ne    L511c
        movi    v3.4s, #0x0
        ext     v4.16b, v2.16b, v3.16b, #8
        ext     v0.16b, v1.16b, v3.16b, #8
        orr     v4.16b, v4.16b, v2.16b
        eor     v2.16b, v0.16b, v1.16b
        ext     v1.16b, v4.16b, v3.16b, #4
        ext     v0.16b, v2.16b, v3.16b, #4
        orr     v1.16b, v1.16b, v4.16b
        eor     v0.16b, v0.16b, v2.16b
        ext     v4.16b, v1.16b, v3.16b, #2
        ext     v2.16b, v0.16b, v3.16b, #2
        orr     v4.16b, v4.16b, v1.16b
        eor     v2.16b, v2.16b, v0.16b
        ext     v0.16b, v4.16b, v3.16b, #1
        ext     v1.16b, v2.16b, v3.16b, #1
        orr     v0.16b, v0.16b, v4.16b
        eor     v1.16b, v1.16b, v2.16b
        umov    w0, v0.b[0]
        umov    w1, v1.b[0]
        neg     w0, w0
        eor     w0, w1, w0, asr #16
        ldr     q0, [x20, #2368]
        and     w0, w0, #0xff
        ldr     q1, [x20, #2384]
        mov     x2, #0x440
        eor     w20, w0, w1
        mov     x1, x21
        add     x0, x19, #0xc20
        stp     q0, q1, [x25]
        bl      L0810
        mov     x0, x22
        mov     x2, x25
        mov     x3, #0x460
        mov     x1, #0x20
        bl      L35b0
        neg     w4, w20
        sub     x22, x22, #0x1
        mov     x0, #0x1
L51d0:
        add     x2, x0, x23
        mov     w1, w4
        ldurb   w2, [x2, #-1]
        ldrb    w3, [x22, x0]
        eor     w3, w2, w3
        and     w1, w3, w1, asr #16
        eor     w2, w2, w1
        strb    w2, [x22, x0]
        add     x0, x0, #0x1
        cmp     x0, #0x21
        b.ne    L51d0
        b       L4efc
L5200:
        bl      L0830

// mlkem1024_check_pk (0x17c bytes)
L5204:
        sub     sp, sp, #0xe40
        mov     x10, x0
        .inst   0xd00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        add     x9, x0, #0x600
        stp     x19, x20, [sp]
        add     x19, sp, #0x3f
        and     x19, x19, #0xffffffffffffffe0
        stp     x21, x30, [sp, #16]
        mov     x7, x0
        mov     x11, x19
        mov     x8, x19
        ldr     x0, [x1]
        str     x0, [sp, #3640]
        mov     x0, #0x0
L5240:
        mov     x1, x7
        mov     x0, x8
        add     x7, x7, #0x180
        bl      L0b10
        add     x8, x8, #0x200
        cmp     x9, x7
        b.ne    L5240
        mov     x0, x19
        bl      L0c14
        add     x0, x19, #0x200
        bl      L0c14
        add     x20, x19, #0x800
        add     x0, x19, #0x400
        bl      L0c14
        mov     x9, x20
        mov     x8, x20
        add     x12, x19, #0xe00
        add     x0, x19, #0x600
        bl      L0c14
L528c:
        mov     x1, x11
        mov     x0, x8
        add     x8, x8, #0x180
        bl      L0ad4
        add     x11, x11, #0x200
        cmp     x12, x8
        b.ne    L528c
        movi    v2.4s, #0x0
        mov     v3.16b, v2.16b
L52b0:
        ldr     q0, [x10], #16
        ldr     q1, [x9], #16
        eor     v0.16b, v0.16b, v1.16b
        orr     v3.16b, v3.16b, v0.16b
        eor     v2.16b, v2.16b, v0.16b
        cmp     x12, x9
        b.ne    L52b0
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
        mov     x0, x20
        mov     w1, #0x0
        mov     w21, #0xfffffffc
        csel    w21, wzr, w21, eq
        bl      L0840
        mov     x2, #0x800
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #3640]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L537c
        ldp     x19, x20, [sp]
        mov     w0, w21
        ldp     x21, x30, [sp, #16]
        add     sp, sp, #0xe40
        ret
L537c:
        bl      L0830

// mlkem1024_check_sk (0xe8 bytes)
L5380:
        stp     x19, x20, [sp, #-96]!
        mov     x20, x0
        add     x1, x0, #0x600
        .inst   0xd00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        str     x30, [sp, #16]
        add     x19, sp, #0x3f
        mov     x2, #0x620
        ldr     x4, [x3]
        str     x4, [sp, #88]
        mov     x4, #0x0
        and     x19, x19, #0xffffffffffffffe0
        mov     x0, x19
        bl      L40c0
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
        .inst   0xd00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #88]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L5464
        ldr     x30, [sp, #16]
        ldp     x19, x20, [sp], #96
        ret
L5464:
        bl      L0830
        nop
        nop

// mlkem1024_keypair_derand (0x94 bytes)
L5470:
        stp     x19, x20, [sp, #-48]!
        mov     x19, x1
        stp     x21, x22, [sp, #16]
        mov     x22, x2
        mov     x21, x0
        str     x30, [sp, #32]
        bl      L26c4
        mov     x2, #0x620
        mov     w20, w0
        cbnz    w0, L54d4
        mov     x1, x21
        add     x0, x19, #0x600
        bl      L0810
        mov     x1, x21
        add     x0, x19, #0xc20
        mov     x2, #0x620
        bl      L40c0
        ldp     q0, q1, [x22, #32]
        add     x19, x19, #0xc40
        mov     w0, w20
        stp     q0, q1, [x19]
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #48
        ret
L54d4:
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
L5504:
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
        cbnz    w0, L5584
        mov     x1, x21
        mov     x0, x20
        mov     x2, x19
        bl      L5470
L5550:
        movi    v0.4s, #0x0
        stp     q0, q0, [x19]
        stp     q0, q0, [x19, #32]
        .inst   0xd00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #120]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L558c
        ldp     x21, x30, [sp, #16]
        ldp     x19, x20, [sp], #128
        ret
L5584:
        mov     w0, #0xfffffffd
        b       L5550
L558c:
        bl      L0830

// mlkem1024_enc_derand (0xe0 bytes)
L5590:
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
        bl      L5204
        cbz     w0, L5620
L55dc:
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
        b.ne    L566c
        ldp     x21, x22, [sp, #16]
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #48]
        ldp     x19, x20, [sp], #224
        ret
L5620:
        ldp     q0, q1, [x22]
        mov     x1, x21
        add     x0, x19, #0x60
        mov     x2, #0x620
        stp     q0, q1, [x20]
        bl      L40c0
        mov     x1, x20
        mov     x0, x19
        mov     x2, #0x40
        bl      L18f0
        mov     x2, x21
        mov     x0, x24
        add     x3, x19, #0x20
        mov     x1, x20
        bl      L3730
        cbnz    w0, L55dc
        ldp     q0, q1, [x19]
        stp     q0, q1, [x23]
        b       L55dc
L566c:
        bl      L0830

// mlkem1024_enc (0x98 bytes)
L5670:
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
        cbnz    w0, L56fc
        mov     x2, x22
        mov     x1, x21
        mov     x0, x20
        mov     x3, x19
        bl      L5590
L56c8:
        stp     xzr, xzr, [x19]
        stp     xzr, xzr, [x19, #16]
        .inst   0xd00000c1  // adrp x1, 0x1f000
        ldr     x1, [x1, #4088]
        ldr     x3, [sp, #104]
        ldr     x2, [x1]
        subs    x3, x3, x2
        mov     x2, #0x0
        b.ne    L5704
        ldp     x21, x22, [sp, #16]
        ldr     x30, [sp, #32]
        ldp     x19, x20, [sp], #112
        ret
L56fc:
        mov     w0, #0xfffffffd
        b       L56c8
L5704:
        bl      L0830
        nop
        nop

// mlkem1024_dec (0x534 bytes)
L5710:
        mov     x12, #0x1f60
        sub     sp, sp, x12
        .inst   0xd00000c3  // adrp x3, 0x1f000
        ldr     x3, [x3, #4088]
        stp     x19, x20, [sp]
        stp     x21, x22, [sp, #16]
        mov     x21, x2
        add     x2, sp, #0x9f
        stp     x23, x24, [sp, #32]
        and     x19, x2, #0xffffffffffffffe0
        str     x30, [sp, #80]
        str     x1, [sp, #104]
        str     x0, [sp, #120]
        mov     x0, x21
        ldr     x1, [x3]
        str     x1, [sp, #8024]
        mov     x1, #0x0
        bl      L5380
        cbz     w0, L57d4
        mov     x7, #0x1e80
        mov     x8, #0x1e40
        add     x20, x19, x7
        add     x22, x19, x8
        mov     w24, w0
        add     x19, x19, #0x1, lsl #12
L5774:
        mov     x0, x19
        mov     x2, #0x640
        mov     w1, #0x0
        bl      L0840
        movi    v0.4s, #0x0
        stp     q0, q0, [x22]
        stp     q0, q0, [x22, #32]
        stp     q0, q0, [x20]
        stp     q0, q0, [x20, #32]
        .inst   0xd00000c0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ldr     x2, [sp, #8024]
        ldr     x1, [x0]
        subs    x2, x2, x1
        mov     x1, #0x0
        b.ne    L5c38
        ldp     x19, x20, [sp]
        mov     w0, w24
        ldp     x21, x22, [sp, #16]
        mov     x12, #0x1f60
        ldp     x23, x24, [sp, #32]
        ldr     x30, [sp, #80]
        add     sp, sp, x12
        ret
L57d4:
        ldr     x0, [sp, #104]
        .inst   0x90000001  // adrp x1, 0x5000
        add     x24, x19, #0x800
        mov     x9, #0x0
        ldr     q3, [x1, #3328]
        mov     x20, x24
        movi    v2.4s, #0x4, lsl #8
        mov     x10, x24
        add     x8, x0, #0x160
        stp     x25, x26, [sp, #48]
        stp     x27, x28, [sp, #64]
        str     x0, [sp, #112]
L5804:
        sub     x1, x8, #0x160
        mov     x7, x10
        nop
L5810:
        ldrb    w5, [x1, #2]
        add     x1, x1, #0xb
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
        ldurb   w11, [x1, #-4]
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
        lsl     w12, w0, #9
        mov     v4.16b, v2.16b
        orr     w4, w12, w11, lsl #1
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
        str     q0, [x7], #16
        cmp     x1, x8
        b.ne    L5810
        add     x9, x9, #0x20
        add     x10, x10, #0x200
        add     x8, x1, #0x160
        cmp     x9, #0x80
        b.ne    L5804
        ldr     x0, [sp, #104]
        mov     x6, #0x1c40
        movi    v2.4s, #0x10
        add     x22, x19, x6
        add     x2, x0, #0x580
        .inst   0x90000000  // adrp x0, 0x5000
        mov     x23, x22
        add     x27, x22, #0x200
        ldr     q3, [x0, #3328]
        mov     x8, x22
        nop
L5920:
        ldrb    w0, [x2, #1]
        add     x2, x2, #0x5
        ldurb   w1, [x2, #-5]
        ldurb   w3, [x2, #-3]
        lsl     w6, w0, #3
        and     w4, w1, #0x1f
        orr     w1, w6, w1, lsr #5
        fmov    s0, w4
        and     w6, w1, #0x1f
        ubfx    x9, x0, #2, #5
        lsl     w1, w3, #1
        ldurb   w7, [x2, #-1]
        mov     v0.b[1], w6
        orr     w1, w1, w0, lsr #7
        ldurb   w0, [x2, #-2]
        and     w1, w1, #0x1f
        fmov    s1, w7
        mov     v4.16b, v2.16b
        mov     v0.b[2], w9
        lsl     w10, w0, #4
        orr     w3, w10, w3, lsr #4
        ubfx    x6, x0, #1, #5
        and     w3, w3, #0x1f
        lsl     w10, w7, #2
        orr     w0, w10, w0, lsr #6
        ushr    v1.2s, v1.2s, #3
        mov     v0.b[3], w1
        and     w0, w0, #0x1f
        mov     v0.b[4], w3
        mov     v0.b[5], w6
        mov     v0.b[6], w0
        mov     v0.b[7], v1.b[0]
        mov     v1.16b, v2.16b
        uxtl    v0.8h, v0.8b
        umlal   v1.4s, v0.4h, v3.4h
        umlal2  v4.4s, v0.8h, v3.8h
        shrn    v0.4h, v1.4s, #5
        shrn2   v0.8h, v4.4s, #5
        str     q0, [x8], #16
        cmp     x27, x8
        b.ne    L5920
        mov     x8, x19
        mov     x7, x21
        add     x26, x21, #0x600
L59d0:
        mov     x1, x7
        mov     x0, x8
        add     x7, x7, #0x180
        bl      L0b10
        add     x8, x8, #0x200
        cmp     x26, x7
        b.ne    L59d0
        mov     x5, #0x1640
        mov     x0, x24
        add     x25, x19, x5
        bl      L1990
        mov     x28, x25
        add     x0, x25, #0x400
        str     x0, [sp, #96]
        add     x0, x19, #0xa00
        bl      L1990
        add     x0, x19, #0xc00
        bl      L1990
        add     x0, x19, #0xe00
        bl      L1990
L5a20:
        mov     x0, x28
        mov     x1, x20
        bl      L0c64
        add     x28, x28, #0x100
        ldr     x0, [sp, #96]
        add     x20, x20, #0x200
        cmp     x0, x28
        b.ne    L5a20
        mov     x4, #0x1a40
        mov     x3, x25
        mov     x2, x24
        mov     x1, x19
        add     x28, x19, x4
        mov     x0, x28
        bl      L1830
        mov     x0, x28
        bl      L0ce0
        mov     x0, x28
L5a68:
        ldr     q1, [x0], #16
        ldr     q0, [x23]
        sub     v0.8h, v0.8h, v1.8h
        str     q0, [x23], #16
        cmp     x27, x23
        b.ne    L5a68
        mov     x1, #0x1e80
        mov     x0, x22
        add     x20, x19, x1
        bl      L0c14
        mov     x0, x20
        mov     x1, x22
        bl      L0bb0
        mov     x0, x25
        mov     x2, #0x400
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x28
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x200
        mov     x0, x22
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x19
        mov     w1, #0x0
        bl      L0840
        mov     x2, #0x800
        mov     x0, x24
        mov     w1, #0x0
        bl      L0840
        ldr     q0, [x21, #3104]
        mov     x2, #0x1e40
        ldr     q1, [x21, #3120]
        add     x22, x19, x2
        mov     x0, x22
        mov     x1, x20
        mov     x2, #0x40
        add     x19, x19, #0x1, lsl #12
        stp     q0, q1, [x20, #32]
        bl      L18f0
        mov     x2, x26
        add     x3, x22, #0x20
        mov     x0, x19
        mov     x1, x20
        bl      L3730
        mov     w24, w0
        cbnz    w0, L5c2c
        movi    v0.4s, #0x0
        mov     x0, x19
        add     x1, x19, #0x620
        mov     v4.16b, v0.16b
L5b40:
        ldr     x2, [sp, #112]
        ldr     q2, [x0], #16
        ldr     q1, [x2], #16
        eor     v1.16b, v1.16b, v2.16b
        str     x2, [sp, #112]
        orr     v4.16b, v4.16b, v1.16b
        eor     v0.16b, v0.16b, v1.16b
        cmp     x1, x0
        b.ne    L5b40
        movi    v1.4s, #0x0
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
        umov    w0, v0.b[0]
        umov    w1, v1.b[0]
        neg     w0, w0
        eor     w0, w1, w0, asr #16
        and     w0, w0, #0xff
        mov     x2, #0x620
        ldr     q0, [x21, #3136]
        ldr     q1, [x21, #3152]
        eor     w21, w0, w1
        ldr     x1, [sp, #104]
        add     x0, x19, #0x20
        stp     q0, q1, [x19]
        neg     w21, w21
        bl      L0810
        ldr     x23, [sp, #120]
        mov     x1, #0x20
        mov     x2, x19
        mov     x3, #0x640
        mov     x0, x23
        bl      L35b0
        sub     x1, x23, #0x1
        mov     x0, #0x1
L5c00:
        add     x3, x0, x22
        mov     w2, w21
        ldurb   w3, [x3, #-1]
        ldrb    w4, [x1, x0]
        eor     w4, w3, w4
        and     w2, w4, w2, asr #16
        eor     w3, w3, w2
        strb    w3, [x1, x0]
        add     x0, x0, #0x1
        cmp     x0, #0x21
        b.ne    L5c00
L5c2c:
        ldp     x25, x26, [sp, #48]
        ldp     x27, x28, [sp, #64]
        b       L5774
L5c38:
        stp     x25, x26, [sp, #48]
        stp     x27, x28, [sp, #64]
        bl      L0830

// Padding (0x5c44 to 0x5c60)

        .long   0x00000000
        .long   0x00000000
        .long   0x00000000
        .long   0x00000000
        .long   0x00000000
        .long   0x00000000
        .long   0x00000000

// The read-only data (0x5c60 to 0x5ee0)

        .quad   0x00000d0100000d01
        .quad   0x00000d0100000d01
        .quad   0x05a105a105a105a1
        .quad   0x05a105a105a105a1
        .quad   0xf301f301f301f301
        .quad   0xf301f301f301f301
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
        .quad   0x0549054905490549
        .quad   0x0549054905490549
        .quad   0x0d010d010d010d01
        .quad   0x0d010d010d010d01
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

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
