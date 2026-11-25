// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// A client of an allocator, for the demonstration of the heap model of
// arm/proofs/heap.ml (arm/heap/heap_demo.ml): it allocates 16 bytes,
// stores x and x + 1 in them, reads them back, frees the block and returns
// their sum 2 * x + 1. The calls are adr x30 / br, which is blr.
//
//    uint64_t heap_demo(uint64_t x, void *(*alloc)(size_t),
//                       void (*release)(void *));
//
// Standard ARM ABI: X0 = x, X1 = alloc, X2 = release, returns X0
// ----------------------------------------------------------------------------

        .text
        .balign 4

        .globl  heap_demo

heap_demo:
        stp     x29, x30, [sp, #-32]!
        stp     x19, x20, [sp, #16]
        mov     x19, x0
        mov     x20, x2
        mov     x0, #16
        adr     x30, .Lret1
        br      x1
.Lret1:
        str     x19, [x0]
        add     x1, x19, #1
        str     x1, [x0, #8]
        ldr     x1, [x0]
        ldr     x2, [x0, #8]
        add     x19, x1, x2
        adr     x30, .Lret2
        br      x20
.Lret2:
        mov     x0, x19
        ldp     x19, x20, [sp, #16]
        ldp     x29, x30, [sp], #32
        ret
