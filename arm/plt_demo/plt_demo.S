// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// The image of the test library libplt_demo.so
//
// This is a transcription of libplt_demo.so built by plt_demo/build.sh, as
// loaded at an address that is a multiple of 4096: the start of its first
// segment, from address 0 up to the end of .text (0x394). It is generated
// by tools/elf_transcribe.py. The ELF header and dynamic linking
// information at the start are given as data, as are the padding and the
// read-only data, while the executable sections (.plt, .text) are given as
// instructions. The ADR and ADRP instructions, which compute addresses
// relative to that of the instruction, are given as words, with the
// disassembly as a comment. The labels are named after the addresses in the
// binary.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(plt_demo)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(plt_demo)
        .text
        .balign 4

S2N_BN_SYMBOL(plt_demo):

// ELF header and dynamic linking information (0x0 to 0x2f0)

        .quad   0x00010102464c457f
        .quad   0x0000000000000000
        .quad   0x0000000100b70003
        .quad   0x0000000000000000
        .quad   0x0000000000000040
        .quad   0x0000000000010350
        .quad   0x0038004000000000
        .quad   0x000e000f00400004
        .quad   0x0000000500000001
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000394
        .quad   0x0000000000000394
        .quad   0x0000000000010000
        .quad   0x0000000600000001
        .quad   0x000000000000fe38
        .quad   0x000000000001fe38
        .quad   0x000000000001fe38
        .quad   0x00000000000001c8
        .quad   0x00000000000001c8
        .quad   0x0000000000010000
        .quad   0x0000000600000002
        .quad   0x000000000000fe58
        .quad   0x000000000001fe58
        .quad   0x000000000001fe58
        .quad   0x0000000000000170
        .quad   0x0000000000000170
        .quad   0x0000000000000008
        .quad   0x000000046474e552
        .quad   0x000000000000fe38
        .quad   0x000000000001fe38
        .quad   0x000000000001fe38
        .quad   0x00000000000001c8
        .quad   0x00000000000001c8
        .quad   0x0000000000000001
        .quad   0x0000000700000003
        .quad   0x0000000000000006
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000300000002
        .quad   0x0000000500000004
        .quad   0x0000000400000003
        .quad   0x0000000600000001
        .quad   0x0200400020200005
        .quad   0x0000000000000000
        .quad   0x9cfbbb9400000004
        .quad   0x0135301dffa4ae42
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0008000300000000
        .quad   0x0000000000000330
        .quad   0x0000000000000000
        .quad   0x000000100000000c
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0000001000000014
        .quad   0x0000000000000000
        .quad   0x0000000000000000
        .quad   0x0008001200000025
        .quad   0x0000000000000388
        .quad   0x000000000000000c
        .quad   0x000800120000001b
        .quad   0x0000000000000378
        .quad   0x0000000000000010
        .quad   0x0008001200000001
        .quad   0x0000000000000330
        .quad   0x0000000000000040
        .quad   0x635f746669687300
        .quad   0x6d6d656d0079706f
        .quad   0x636d656d0065766f
        .quad   0x5f6c6c6163007970
        .quad   0x6d656d00746f6c73
        .quad   0x726464615f797063
        .quad   0x7062696c00737365
        .quad   0x2e6f6d65645f746c
        .quad   0x0000000000006f73
        .quad   0x000000000001fe48
        .quad   0x0000000000000403
        .quad   0x0000000000000370
        .quad   0x000000000001fe50
        .quad   0x0000000200000101
        .quad   0x0000000000000008
        .quad   0x000000000001fff8
        .quad   0x0000000300000401
        .quad   0x0000000000000000
        .quad   0x000000000001ffe0
        .quad   0x0000000200000402
        .quad   0x0000000000000000
        .quad   0x000000000001ffe8
        .quad   0x0000000300000402
        .quad   0x0000000000000000
        .quad   0x0000000000000000

// .plt (0x2f0 to 0x330)
        stp     x16, x30, [sp, #-16]!
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4056]
        add     x16, x16, #0xfd8
        br      x17
        nop
        nop
        nop
L0310:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4064]
        add     x16, x16, #0xfe0
        br      x17
L0320:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        ldr     x17, [x16, #4072]
        add     x16, x16, #0xfe8
        br      x17

// .text (0x330 to 0x394)

// shift_copy (0x40 bytes)
L0330:
        stp     x29, x30, [sp, #-48]!
        mov     x29, sp
        stp     x19, x20, [sp, #16]
        str     x21, [sp, #32]
        mov     x19, x0
        mov     x20, x1
        mov     x21, x2
        add     x1, x0, #0x8
        bl      L0310
        mov     x2, x21
        mov     x1, x19
        mov     x0, x20
        ldp     x19, x20, [sp, #16]
        ldr     x21, [sp, #32]
        ldp     x29, x30, [sp], #48
        b       L0320

// answer (0x8 bytes)
L0370:
        mov     x0, #0x2a
        ret

// call_slot (0x10 bytes)
L0378:
        .inst   0xf00000f0  // adrp x16, 0x1f000
        add     x16, x16, #0xe38
        ldr     x16, [x16, #16]
        br      x16

// memcpy_address (0xc bytes)
L0388:
        .inst   0xf00000e0  // adrp x0, 0x1f000
        ldr     x0, [x0, #4088]
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
