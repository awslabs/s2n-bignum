/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

        .option norvc

        .section .init,"ax",@progbits
        .globl _start
        .type _start,@function
_start:
        .option push
        .option norelax
        la      gp,__global_pointer$
        .option pop
        la      sp,rv32_monitor_stack_top

        la      t0,__bss_start
        la      t1,__bss_end
1:      bgeu    t0,t1,2f
        sw      zero,0(t0)
        addi    t0,t0,4
        j       1b
2:      call    main
3:      wfi
        j       3b
        .size _start,.-_start

        .text
        .balign 4
        .globl rv32_run
        .type rv32_run,@function
        .extern rv32_scratch
rv32_run:
        la      t0,rv32_monitor_context
        sw      ra,0(t0)
        sw      sp,4(t0)
        sw      gp,8(t0)
        sw      tp,12(t0)
        sw      s0,16(t0)
        sw      s1,20(t0)
        sw      s2,24(t0)
        sw      s3,28(t0)
        sw      s4,32(t0)
        sw      s5,36(t0)
        sw      s6,40(t0)
        sw      s7,44(t0)
        sw      s8,48(t0)
        sw      s9,52(t0)
        sw      s10,56(t0)
        sw      s11,60(t0)

        la      t0,rv32_current_state
        sw      a0,0(t0)
        la      t0,rv32_trap_handler
        csrw    mtvec,t0
        la      t0,rv32_trap_stack_top
        csrw    mscratch,t0

        csrr    t0,mstatus
        li      t1,0x1888
        not     t1,t1
        and     t0,t0,t1
        li      t1,0x1800
        or      t0,t0,t1
        csrw    mstatus,t0

        la      t0,rv32_current_state
        lw      t0,0(t0)
        la      t1,rv32_code_slot
        csrw    mepc,t1

        lw      ra,4(t0)
        lw      gp,8(t0)
        lw      tp,12(t0)
        lw      t1,20(t0)
        lw      t2,24(t0)
        lw      s0,28(t0)
        lw      s1,32(t0)
        lw      a0,36(t0)
        lw      a1,40(t0)
        lw      a2,44(t0)
        lw      a3,48(t0)
        lw      a4,52(t0)
        lw      a5,56(t0)
        lw      a6,60(t0)
        lw      a7,64(t0)
        lw      s2,68(t0)
        lw      s3,72(t0)
        lw      s4,76(t0)
        lw      s5,80(t0)
        lw      s6,84(t0)
        lw      s7,88(t0)
        lw      s8,92(t0)
        lw      s9,96(t0)
        lw      s10,100(t0)
        lw      s11,104(t0)
        lw      t3,108(t0)
        lw      t4,112(t0)
        lw      t5,116(t0)
        lw      t6,120(t0)
        lw      t0,16(t0)
        la      sp,rv32_scratch
        mret
        .size rv32_run,.-rv32_run

        .balign 4
        .type rv32_trap_handler,@function
rv32_trap_handler:
        csrrw   sp,mscratch,sp
        addi    sp,sp,-16
        sw      t0,0(sp)
        sw      t1,4(sp)
        sw      t2,8(sp)

        la      t0,rv32_current_state
        lw      t0,0(t0)
        sw      zero,0(t0)
        sw      ra,4(t0)
        sw      gp,8(t0)
        sw      tp,12(t0)
        lw      t1,0(sp)
        sw      t1,16(t0)
        lw      t1,4(sp)
        sw      t1,20(t0)
        lw      t1,8(sp)
        sw      t1,24(t0)
        sw      s0,28(t0)
        sw      s1,32(t0)
        sw      a0,36(t0)
        sw      a1,40(t0)
        sw      a2,44(t0)
        sw      a3,48(t0)
        sw      a4,52(t0)
        sw      a5,56(t0)
        sw      a6,60(t0)
        sw      a7,64(t0)
        sw      s2,68(t0)
        sw      s3,72(t0)
        sw      s4,76(t0)
        sw      s5,80(t0)
        sw      s6,84(t0)
        sw      s7,88(t0)
        sw      s8,92(t0)
        sw      s9,96(t0)
        sw      s10,100(t0)
        sw      s11,104(t0)
        sw      t3,108(t0)
        sw      t4,112(t0)
        sw      t5,116(t0)
        sw      t6,120(t0)

        csrr    t3,mepc
        csrr    t1,mcause
        la      t2,rv32_trap_cause
        sw      t1,0(t2)
        csrr    t2,mtval
        la      t4,rv32_trap_value
        sw      t2,0(t4)

        li      t5,1
        li      t2,3
        bne     t1,t2,4f
        la      t2,rv32_expected_break0
        lw      t2,0(t2)
        bne     t3,t2,4f
5:      li      t5,0
4:      la      t2,rv32_trap_status
        sw      t5,0(t2)

        la      t0,rv32_monitor_context
        lw      ra,0(t0)
        lw      gp,8(t0)
        lw      tp,12(t0)
        lw      s0,16(t0)
        lw      s1,20(t0)
        lw      s2,24(t0)
        lw      s3,28(t0)
        lw      s4,32(t0)
        lw      s5,36(t0)
        lw      s6,40(t0)
        lw      s7,44(t0)
        lw      s8,48(t0)
        lw      s9,52(t0)
        lw      s10,56(t0)
        lw      s11,60(t0)
        lw      a0,rv32_trap_status
        lw      sp,4(t0)
        ret
        .size rv32_trap_handler,.-rv32_trap_handler

        .section .bss,"aw",@nobits
        .balign 16
rv32_monitor_context:
        .space 64

        .section .cosim_code,"awx",@progbits
        .balign 4096
        .globl rv32_code_slot
rv32_code_slot:
        .space 512,0
        .globl rv32_code_slot_end
rv32_code_slot_end:

#if defined(__linux__) && defined(__ELF__)
        .section .note.GNU-stack,"",%progbits
#endif
