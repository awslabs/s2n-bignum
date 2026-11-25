// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Small programs for the regression tests of bstep in
// arm/proofs/bstep_tests.ml: a call and a tail call of a function after a
// block, and ADRP within a block. The code is loaded at a 4096-aligned pc,
// and the two ADRP are written as words, so that the object has no
// relocations: adrp x16, <page + 2> and adrp x2, <page>.
// ----------------------------------------------------------------------------

        .text
        .balign 4

// 0x00: x0 + 1, by a tail call of bstep_f with x1 = x0.

bstep_tail:
        mov     x1, x0
        b       bstep_f

// 0x08: x0 + 3, by a call of bstep_f with x1 = x0, then adding 2; the
// return address is kept in x19.

bstep_call:
        mov     x1, x0
        mov     x19, x30
        bl      bstep_f
        add     x0, x0, #2
        br      x19
        nop

// 0x20: x1 + 1.

bstep_f:
        add     x0, x1, #1
        ret

// 0x28: the 8 bytes at pc + 0x2008, by ADRP and LDR, and a branch to an
// address computed by ADRP and ADD (0x44).

bstep_adrp:
        .inst   0xd0000010              // adrp x16, <page of pc + 0x2000>
        ldr     x17, [x16, #8]
        add     x16, x16, #8
        .inst   0x90000002              // adrp x2, <page of pc>
        add     x2, x2, #0x44
        br      x2
        nop
        mov     x0, x17
        ret
