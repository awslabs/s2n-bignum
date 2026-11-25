// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// A small allocator: 64 slots of 64 bytes and a bitmap of the slots in use;
// new takes the free slot of highest index (63 - clz of the complement).
// It is the witness that the hypothesis heap_model of arm/proofs/heap.ml can
// be met by real code (arm/heap/heap_slab.ml): heap_slab_new is operator new
// for sizes up to 64, heap_slab_delete is operator delete.
//
// Its data are at fixed offsets from the start of the code, at the address
// pc: the bitmap at pc + 0x100 (bit i set iff slot i is in use) and the
// slots at pc + 0x200 + 64 * i, i < 64; the code uses no stack.
//
//    void *heap_slab_new(size_t n);     // n <= 64 and a free slot
//    void heap_slab_delete(void *p);    // p from heap_slab_new, or NULL
//
// Standard ARM ABI: X0 = n or p, returns X0 = the slot for new
// ----------------------------------------------------------------------------

        .text
        .balign 4

        .globl  heap_slab_new
        .globl  heap_slab_delete

heap_slab_new:
.Lbase:
        adr     x9, .Lbase
        ldr     x10, [x9, #0x100]
        mvn     x11, x10
        clz     x11, x11
        mov     x12, #63
        sub     x11, x12, x11
        mov     x12, #1
        lsl     x12, x12, x11
        orr     x10, x10, x12
        str     x10, [x9, #0x100]
        add     x0, x9, #0x200
        add     x0, x0, x11, lsl #6
        ret

heap_slab_delete:
        cbz     x0, .Lnull
        adr     x9, .Lbase
        ldr     x10, [x9, #0x100]
        sub     x11, x0, x9
        sub     x11, x11, #0x200
        lsr     x11, x11, #6
        mov     x12, #1
        lsl     x12, x12, x11
        bic     x10, x10, x12
        str     x10, [x9, #0x100]
.Lnull:
        ret
