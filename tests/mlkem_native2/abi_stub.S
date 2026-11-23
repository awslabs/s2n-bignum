// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// Call a function under test with a random register state and its own
// stack, and record the register state after it returns.
//
// uint64_t abi_call(void *fn, const uint64_t args[8],
//                   const uint64_t in[96], uint64_t out[96],
//                   void *stack_top)
//
// in and out hold x0..x30 at indices 0..30 and q0..q31 as pairs of words
// at indices 32..95. Before the call, x8..x29 and q0..q31 are loaded from
// in (so the callee sees random values there, including in x18) and
// x0..x7 from args; sp is set to stack_top. After the call, out gets x0,
// x18..x29, q8..q15 and, at index 31, the value of sp.

        .text
        .balign 4
        .globl  abi_call
        .type   abi_call, %function
abi_call:
        stp     x29, x30, [sp, #-176]!
        mov     x29, sp
        stp     x19, x20, [sp, #16]
        stp     x21, x22, [sp, #32]
        stp     x23, x24, [sp, #48]
        stp     x25, x26, [sp, #64]
        stp     x27, x28, [sp, #80]
        stp     d8, d9, [sp, #96]
        stp     d10, d11, [sp, #112]
        stp     d12, d13, [sp, #128]
        stp     d14, d15, [sp, #144]
        stp     x18, x3, [sp, #160]
        adrp    x5, saved_sp
        mov     x6, sp
        str     x6, [x5, :lo12:saved_sp]
        mov     sp, x4
        mov     x16, x0
        mov     x17, x1
        add     x5, x2, #256
        ldp     q0, q1, [x5, #0]
        ldp     q2, q3, [x5, #32]
        ldp     q4, q5, [x5, #64]
        ldp     q6, q7, [x5, #96]
        ldp     q8, q9, [x5, #128]
        ldp     q10, q11, [x5, #160]
        ldp     q12, q13, [x5, #192]
        ldp     q14, q15, [x5, #224]
        ldp     q16, q17, [x5, #256]
        ldp     q18, q19, [x5, #288]
        ldp     q20, q21, [x5, #320]
        ldp     q22, q23, [x5, #352]
        ldp     q24, q25, [x5, #384]
        ldp     q26, q27, [x5, #416]
        ldp     q28, q29, [x5, #448]
        ldp     q30, q31, [x5, #480]
        ldp     x8, x9, [x2, #64]
        ldp     x10, x11, [x2, #80]
        ldp     x12, x13, [x2, #96]
        ldp     x14, x15, [x2, #112]
        ldp     x18, x19, [x2, #144]
        ldp     x20, x21, [x2, #160]
        ldp     x22, x23, [x2, #176]
        ldp     x24, x25, [x2, #192]
        ldp     x26, x27, [x2, #208]
        ldp     x28, x29, [x2, #224]
        ldp     x0, x1, [x17, #0]
        ldp     x2, x3, [x17, #16]
        ldp     x4, x5, [x17, #32]
        ldp     x6, x7, [x17, #48]
        blr     x16
        adrp    x16, saved_sp
        ldr     x16, [x16, :lo12:saved_sp]
        ldr     x17, [x16, #168]
        str     x0, [x17, #0]
        stp     x18, x19, [x17, #144]
        stp     x20, x21, [x17, #160]
        stp     x22, x23, [x17, #176]
        stp     x24, x25, [x17, #192]
        stp     x26, x27, [x17, #208]
        stp     x28, x29, [x17, #224]
        mov     x1, sp
        str     x1, [x17, #248]
        add     x1, x17, #256
        stp     q8, q9, [x1, #128]
        stp     q10, q11, [x1, #160]
        stp     q12, q13, [x1, #192]
        stp     q14, q15, [x1, #224]
        mov     sp, x16
        ldp     x19, x20, [sp, #16]
        ldp     x21, x22, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x25, x26, [sp, #64]
        ldp     x27, x28, [sp, #80]
        ldp     d8, d9, [sp, #96]
        ldp     d10, d11, [sp, #112]
        ldp     d12, d13, [sp, #128]
        ldp     d14, d15, [sp, #144]
        ldr     x18, [sp, #160]
        ldp     x29, x30, [sp], #176
        ret
        .size   abi_call, .-abi_call

        .bss
        .balign 8
saved_sp:
        .skip   8

        .section .note.GNU-stack,"",%progbits
