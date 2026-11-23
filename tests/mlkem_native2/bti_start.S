// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// An entry point with a BTI landing pad, for test programs linked with
// -z force-bti so that the kernel enforces BTI even when the C library's
// start files have no landing pads (as on distributions that build glibc
// without branch protection, e.g. Ubuntu 24.04, whose Scrt1.o starts
// _start with a nop, while ld.so enters it with an indirect branch). Use
// with -Wl,-e,bti_start and with -Wl,-init,bti_init -Wl,-fini,bti_init,
// since crti.o's _init and _fini have no landing pads either.

        .text
        .globl  bti_start
        .type   bti_start, %function
bti_start:
        bti     jc
        b       _start

        .globl  bti_init
        .type   bti_init, %function
bti_init:
        bti     c
        ret

        .pushsection .note.gnu.property, "a"
        .balign 8
        .long   4, 0x10, 0x5
        .asciz  "GNU"
        .long   0xc0000000, 4, 1, 0
        .popsection

        .section .note.GNU-stack, "", %progbits
