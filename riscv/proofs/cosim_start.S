/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/*
 * Startup and trap glue for the freestanding RV32IM cosimulation monitor.
 *
 * `_start` initializes the monitor itself and enters `main`. `rv32_run`
 * installs a temporary machine-mode trap handler, loads one transported
 * machine state plus the private scratch-backed SP, and enters the injected
 * test code with `mret`.
 *
 * This is deliberately not a normal function call. The injected code is not
 * expected to preserve call-clobbered registers, maintain a valid return
 * address, or `ret` back to the monitor. Instead, `rv32_run` programs `mepc`
 * with the start of the injected code slot, programs `mtvec` with a private
 * trap handler, and then uses `mret` as an architectural "resume execution at
 * `mepc`" mechanism.
 *
 * `cosim_runner.c` appends one synthetic terminating `ebreak` after the last
 * injected instruction. Reaching that `ebreak` traps back through `mtvec`,
 * just like any unexpected fault would. The trap handler snapshots the
 * post-state back into the transport buffer, checks whether the trap was the
 * expected terminating breakpoint at the appended `ebreak`, restores the
 * monitor context, and returns control to `cosim_runner.c`.
 */

        .option norvc

        .equ MONCTX_RA,   0
        .equ MONCTX_SP,   4
        .equ MONCTX_GP,   8
        .equ MONCTX_TP,   12
        .equ MONCTX_S0,   16
        .equ MONCTX_S1,   20
        .equ MONCTX_S2,   24
        .equ MONCTX_S3,   28
        .equ MONCTX_S4,   32
        .equ MONCTX_S5,   36
        .equ MONCTX_S6,   40
        .equ MONCTX_S7,   44
        .equ MONCTX_S8,   48
        .equ MONCTX_S9,   52
        .equ MONCTX_S10,  56
        .equ MONCTX_S11,  60

        .equ STATE_X0,    0
        .equ STATE_RA,    4
        .equ STATE_GP,    8
        .equ STATE_TP,    12
        .equ STATE_T0,    16
        .equ STATE_T1,    20
        .equ STATE_T2,    24
        .equ STATE_S0,    28
        .equ STATE_S1,    32
        .equ STATE_A0,    36
        .equ STATE_A1,    40
        .equ STATE_A2,    44
        .equ STATE_A3,    48
        .equ STATE_A4,    52
        .equ STATE_A5,    56
        .equ STATE_A6,    60
        .equ STATE_A7,    64
        .equ STATE_S2,    68
        .equ STATE_S3,    72
        .equ STATE_S4,    76
        .equ STATE_S5,    80
        .equ STATE_S6,    84
        .equ STATE_S7,    88
        .equ STATE_S8,    92
        .equ STATE_S9,    96
        .equ STATE_S10,   100
        .equ STATE_S11,   104
        .equ STATE_T3,    108
        .equ STATE_T4,    112
        .equ STATE_T5,    116
        .equ STATE_T6,    120

        /* Save exactly the monitor-side register state that must survive one
           `rv32_run` call back into C: the return/stack/runtime context
           (`ra`, `sp`, `gp`, `tp`) plus the callee-saved integer registers.
           Caller-saved `a*`/`t*` registers are intentionally excluded. */
        .macro SAVE_MONITOR_CONTEXT base
        sw      ra,MONCTX_RA(\base)
        sw      sp,MONCTX_SP(\base)
        sw      gp,MONCTX_GP(\base)
        sw      tp,MONCTX_TP(\base)
        sw      s0,MONCTX_S0(\base)
        sw      s1,MONCTX_S1(\base)
        sw      s2,MONCTX_S2(\base)
        sw      s3,MONCTX_S3(\base)
        sw      s4,MONCTX_S4(\base)
        sw      s5,MONCTX_S5(\base)
        sw      s6,MONCTX_S6(\base)
        sw      s7,MONCTX_S7(\base)
        sw      s8,MONCTX_S8(\base)
        sw      s9,MONCTX_S9(\base)
        sw      s10,MONCTX_S10(\base)
        sw      s11,MONCTX_S11(\base)
        .endm

        .macro RESTORE_MONITOR_CONTEXT base
        lw      ra,MONCTX_RA(\base)
        lw      gp,MONCTX_GP(\base)
        lw      tp,MONCTX_TP(\base)
        lw      s0,MONCTX_S0(\base)
        lw      s1,MONCTX_S1(\base)
        lw      s2,MONCTX_S2(\base)
        lw      s3,MONCTX_S3(\base)
        lw      s4,MONCTX_S4(\base)
        lw      s5,MONCTX_S5(\base)
        lw      s6,MONCTX_S6(\base)
        lw      s7,MONCTX_S7(\base)
        lw      s8,MONCTX_S8(\base)
        lw      s9,MONCTX_S9(\base)
        lw      s10,MONCTX_S10(\base)
        lw      s11,MONCTX_S11(\base)
        lw      sp,MONCTX_SP(\base)
        .endm

        .macro LOAD_TRANSPORT_STATE base
        lw      ra,STATE_RA(\base)
        lw      gp,STATE_GP(\base)
        lw      tp,STATE_TP(\base)
        lw      t1,STATE_T1(\base)
        lw      t2,STATE_T2(\base)
        lw      s0,STATE_S0(\base)
        lw      s1,STATE_S1(\base)
        lw      a0,STATE_A0(\base)
        lw      a1,STATE_A1(\base)
        lw      a2,STATE_A2(\base)
        lw      a3,STATE_A3(\base)
        lw      a4,STATE_A4(\base)
        lw      a5,STATE_A5(\base)
        lw      a6,STATE_A6(\base)
        lw      a7,STATE_A7(\base)
        lw      s2,STATE_S2(\base)
        lw      s3,STATE_S3(\base)
        lw      s4,STATE_S4(\base)
        lw      s5,STATE_S5(\base)
        lw      s6,STATE_S6(\base)
        lw      s7,STATE_S7(\base)
        lw      s8,STATE_S8(\base)
        lw      s9,STATE_S9(\base)
        lw      s10,STATE_S10(\base)
        lw      s11,STATE_S11(\base)
        lw      t3,STATE_T3(\base)
        lw      t4,STATE_T4(\base)
        lw      t5,STATE_T5(\base)
        lw      t6,STATE_T6(\base)
        lw      t0,STATE_T0(\base)
        .endm

        .macro SAVE_TRANSPORT_STATE base
        sw      zero,STATE_X0(\base)
        sw      ra,STATE_RA(\base)
        sw      gp,STATE_GP(\base)
        sw      tp,STATE_TP(\base)
        sw      s0,STATE_S0(\base)
        sw      s1,STATE_S1(\base)
        sw      a0,STATE_A0(\base)
        sw      a1,STATE_A1(\base)
        sw      a2,STATE_A2(\base)
        sw      a3,STATE_A3(\base)
        sw      a4,STATE_A4(\base)
        sw      a5,STATE_A5(\base)
        sw      a6,STATE_A6(\base)
        sw      a7,STATE_A7(\base)
        sw      s2,STATE_S2(\base)
        sw      s3,STATE_S3(\base)
        sw      s4,STATE_S4(\base)
        sw      s5,STATE_S5(\base)
        sw      s6,STATE_S6(\base)
        sw      s7,STATE_S7(\base)
        sw      s8,STATE_S8(\base)
        sw      s9,STATE_S9(\base)
        sw      s10,STATE_S10(\base)
        sw      s11,STATE_S11(\base)
        sw      t3,STATE_T3(\base)
        sw      t4,STATE_T4(\base)
        sw      t5,STATE_T5(\base)
        sw      t6,STATE_T6(\base)
        .endm

        .section .init,"ax",@progbits
        .globl _start
        .type _start,@function
_start:
        /* Initialize `gp` in the standard non-relaxed way expected by the
           freestanding monitor runtime. */
        .option push
        .option norelax
        la      gp,__global_pointer$
        .option pop
        /* Use a dedicated monitor stack rather than the cosimulation scratch
           buffer used for test execution. */
        la      sp,rv32_monitor_stack_top

        /* Zero `.bss` before entering C code. */
        la      t0,__bss_start
        la      t1,__bss_end
1:      bgeu    t0,t1,2f
        sw      zero,0(t0)
        addi    t0,t0,4
        j       1b
2:      call    main
        /* `main` exits through semihosting; if it ever returns, just sleep. */
3:      wfi
        j       3b
        .size _start,.-_start

        .text
        .balign 4
        .globl rv32_run
        .type rv32_run,@function
        .extern rv32_scratch
rv32_run:
        /* Save the monitor's own execution environment before entering code
           that is not expected to follow the normal call/return discipline.
           This overlaps with callee-saved ABI state, but the purpose here is
           broader: recover the C monitor context after an arbitrary trap-based
           execution, not just preserve registers across a normal function. */
        la      t0,rv32_monitor_context
        SAVE_MONITOR_CONTEXT t0

        /* Tell the trap handler where the transported state lives, and set up
           the trap entry point plus private trap stack for test execution. */
        la      t0,rv32_current_state
        sw      a0,0(t0)
        la      t0,rv32_trap_handler
        csrw    mtvec,t0
        la      t0,rv32_trap_stack_top
        csrw    mscratch,t0

        /* Force M-mode execution with interrupts masked for the short test
           sequence, so `mret` resumes under the monitor's trap regime and the
           private trap handler regains control directly on any exception. */
        csrr    t0,mstatus
        li      t1,0x1888
        not     t1,t1
        and     t0,t0,t1
        li      t1,0x1800
        or      t0,t0,t1
        csrw    mstatus,t0

        /* Start executing at the injected code slot by programming `mepc`.
           The `mret` below will enter the test code via the architectural
           trap-return path rather than a normal call/return sequence. */
        la      t0,rv32_current_state
        lw      t0,0(t0)
        la      t1,rv32_code_slot
        csrw    mepc,t1

        /* Load the transported architectural state. x0 is implicit zero and
           SP is rebound to the private scratch buffer below. */
        LOAD_TRANSPORT_STATE t0
        /* Test loads/stores address this scratch window through SP. */
        la      sp,rv32_scratch
        mret
        .size rv32_run,.-rv32_run

        .balign 4
        .type rv32_trap_handler,@function
rv32_trap_handler:
        /* Swap onto the private trap stack while preserving the interrupted
           SP in `mscratch` for later restoration. */
        csrrw   sp,mscratch,sp
        addi    sp,sp,-16
        sw      t0,0(sp)
        sw      t1,4(sp)
        sw      t2,8(sp)

        /* Snapshot the post-state back into the transport buffer. */
        la      t0,rv32_current_state
        lw      t0,0(t0)
        lw      t1,0(sp)
        sw      t1,STATE_T0(t0)
        lw      t1,4(sp)
        sw      t1,STATE_T1(t0)
        lw      t1,8(sp)
        sw      t1,STATE_T2(t0)
        SAVE_TRANSPORT_STATE t0

        /* Record trap metadata for the C-side protocol response. */
        csrr    t3,mepc
        csrr    t1,mcause
        la      t2,rv32_trap_cause
        sw      t1,0(t2)
        csrr    t2,mtval
        la      t4,rv32_trap_value
        sw      t2,0(t4)

        /* The expected clean exit is a breakpoint exception (`mcause = 3`)
           exactly at the synthetic terminating `ebreak` appended after the
           injected instruction bytes. Anything else is treated as an
           unexpected trap from the test sequence itself. */
        li      t5,1
        li      t2,3
        bne     t1,t2,4f
        la      t2,rv32_expected_break0
        lw      t2,0(t2)
        bne     t3,t2,4f
5:      li      t5,0
4:      la      t2,rv32_trap_status
        sw      t5,0(t2)

        /* Restore the monitor context and return the trap classification in
           `a0` to `cosim_runner.c`. */
        la      t0,rv32_monitor_context
        RESTORE_MONITOR_CONTEXT t0
        lw      a0,rv32_trap_status
        ret
        .size rv32_trap_handler,.-rv32_trap_handler

        .section .bss,"aw",@nobits
        .balign 16
/* Saved monitor registers used across one `rv32_run` call. */
rv32_monitor_context:
        .space 64

        .section .cosim_code,"awx",@progbits
        .balign 4096
/* Executable slot filled with the next injected test sequence. */
        .globl rv32_code_slot
rv32_code_slot:
        .space 512,0
        .globl rv32_code_slot_end
rv32_code_slot_end:

#if defined(__linux__) && defined(__ELF__)
        .section .note.GNU-stack,"",%progbits
#endif
