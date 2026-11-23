// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// Call a function under test with a random register state and its own
// stack, and record the register state after it returns (x86_64).
//
// uint64_t abi_call(void *fn, const uint64_t args[8],
//                   const uint64_t in[96], uint64_t out[96],
//                   void *stack_top)
// uint64_t abi_call_ms(...)   (the same, calling fn with the Microsoft x64
//                              calling convention)
//
// in and out hold the general registers at indices 0..15 (rax, rbx, rcx,
// rdx, rsi, rdi, rbp, rsp, r8..r15) and ymm0..ymm15 as four words each at
// indices 16..79. Before the call, every register except rsp is loaded
// from in (so the callee sees random values there), then the argument
// registers from args (rdi, rsi, rdx, rcx, r8, r9 for System V; rcx, rdx,
// r8, r9 for Microsoft x64, with 32 bytes of shadow space above the
// return address), and rsp is set to stack_top. After the call, out gets
// all the general registers (rsp at index 7) and the vector registers.

        .intel_syntax noprefix
        .text

        .macro  stub name, ms
        .balign 16
        .globl  \name
        .type   \name, @function
\name:
        endbr64
        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15
        mov     [rip+saved_sp], rsp
        mov     [rip+saved_out], rcx
        mov     [rip+saved_fn], rdi
        mov     [rip+saved_args], rsi
        mov     rsp, r8
        .if \ms
        sub     rsp, 32
        .endif
        mov     rax, rdx
        vmovdqu ymm0, [rax+128]
        vmovdqu ymm1, [rax+160]
        vmovdqu ymm2, [rax+192]
        vmovdqu ymm3, [rax+224]
        vmovdqu ymm4, [rax+256]
        vmovdqu ymm5, [rax+288]
        vmovdqu ymm6, [rax+320]
        vmovdqu ymm7, [rax+352]
        vmovdqu ymm8, [rax+384]
        vmovdqu ymm9, [rax+416]
        vmovdqu ymm10, [rax+448]
        vmovdqu ymm11, [rax+480]
        vmovdqu ymm12, [rax+512]
        vmovdqu ymm13, [rax+544]
        vmovdqu ymm14, [rax+576]
        vmovdqu ymm15, [rax+608]
        mov     rbx, [rax+8]
        mov     rbp, [rax+48]
        mov     r10, [rax+80]
        mov     r11, [rax+88]
        mov     r12, [rax+96]
        mov     r13, [rax+104]
        mov     r14, [rax+112]
        mov     r15, [rax+120]
        .if \ms
        mov     rsi, [rax+32]
        mov     rdi, [rax+40]
        mov     r10, [rip+saved_args]
        mov     rcx, [r10]
        mov     rdx, [r10+8]
        mov     r8, [r10+16]
        mov     r9, [r10+24]
        mov     r10, [rax+80]
        .else
        mov     r10, [rip+saved_args]
        mov     rdi, [r10]
        mov     rsi, [r10+8]
        mov     rdx, [r10+16]
        mov     rcx, [r10+24]
        mov     r8, [r10+32]
        mov     r9, [r10+40]
        mov     r10, [rax+80]
        .endif
        mov     rax, [rax]
        call    [rip+saved_fn]
        .if \ms
        add     rsp, 32
        .endif
        push    rax
        mov     rax, [rip+saved_out]
        pop     QWORD PTR [rax]
        mov     [rax+8], rbx
        mov     [rax+16], rcx
        mov     [rax+24], rdx
        mov     [rax+32], rsi
        mov     [rax+40], rdi
        mov     [rax+48], rbp
        mov     [rax+56], rsp
        mov     [rax+64], r8
        mov     [rax+72], r9
        mov     [rax+80], r10
        mov     [rax+88], r11
        mov     [rax+96], r12
        mov     [rax+104], r13
        mov     [rax+112], r14
        mov     [rax+120], r15
        vmovdqu [rax+128], ymm0
        vmovdqu [rax+160], ymm1
        vmovdqu [rax+192], ymm2
        vmovdqu [rax+224], ymm3
        vmovdqu [rax+256], ymm4
        vmovdqu [rax+288], ymm5
        vmovdqu [rax+320], ymm6
        vmovdqu [rax+352], ymm7
        vmovdqu [rax+384], ymm8
        vmovdqu [rax+416], ymm9
        vmovdqu [rax+448], ymm10
        vmovdqu [rax+480], ymm11
        vmovdqu [rax+512], ymm12
        vmovdqu [rax+544], ymm13
        vmovdqu [rax+576], ymm14
        vmovdqu [rax+608], ymm15
        mov     rsp, [rip+saved_sp]
        mov     rax, [rax]
        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx
        vzeroupper
        ret
        .size   \name, .-\name
        .endm

        stub    abi_call, 0
        stub    abi_call_ms, 1

        .data
        .balign 8
saved_sp:
        .quad   0
saved_out:
        .quad   0
saved_fn:
        .quad   0
saved_args:
        .quad   0

        .section .note.GNU-stack,"",@progbits
