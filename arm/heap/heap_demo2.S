// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// A client of an allocator with two live blocks, for the heap model of
// arm/proofs/heap.ml (arm/heap/heap_demo2.ml): a = alloc(16); a[0] = x;
// b = alloc(16); b[0] = a[0] + 1; release(a); r = b[0]; release(b);
// return r. The value in a crosses the second allocation and the value in
// b crosses the release of a. The calls are adr x30 / br, which is blr.
//
//    uint64_t heap_demo2(uint64_t x, void *(*alloc)(size_t),
//                        void (*release)(void *));
//
// Standard ARM ABI: X0 = x, X1 = alloc, X2 = release, returns X0
// ----------------------------------------------------------------------------

        .text
        .balign 4

        .globl  heap_demo2

heap_demo2:
        stp     x29, x30, [sp, #-48]!
        stp     x19, x20, [sp, #16]
        stp     x21, x22, [sp, #32]
        mov     x19, x0
        mov     x20, x1
        mov     x21, x2
        mov     x0, #16
        adr     x30, .Lret1
        br      x20
.Lret1:
        mov     x22, x0
        str     x19, [x22]
        mov     x0, #16
        adr     x30, .Lret2
        br      x20
.Lret2:
        mov     x20, x0
        ldr     x1, [x22]
        add     x1, x1, #1
        str     x1, [x20]
        mov     x0, x22
        adr     x30, .Lret3
        br      x21
.Lret3:
        ldr     x19, [x20]
        mov     x0, x20
        adr     x30, .Lret4
        br      x21
.Lret4:
        mov     x0, x19
        ldp     x21, x22, [sp, #32]
        ldp     x19, x20, [sp, #16]
        ldp     x29, x30, [sp], #48
        ret
