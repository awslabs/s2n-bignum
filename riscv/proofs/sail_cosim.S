/*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/*
 * Bare-metal template for the Sail-backed RV32IM cosimulation executor
 * (riscv/proofs/sail-cosim-runner).
 *
 * Unlike the persistent QEMU monitor, this program runs exactly one test
 * case and exits. The runner patches the `.cosim` section of the linked ELF
 * with the instruction bytes, the input registers and the input scratch
 * words, runs it on the Sail RISC-V model, and reads the result back from
 * the signature region that the Sail simulator dumps on exit.
 *
 * Layout of `.cosim` (offsets are fixed and shared with the runner):
 *
 *   0x000  code_slot   256 bytes  test instructions, then one `ebreak`
 *   0x100  regs_in     32 words   input x0, x1, x3..x31 (x0 slot unused)
 *   0x180  regs_out    32 words   output registers, same order
 *   0x200  scratch     64 words   the scratch buffer SP points at
 *   0x300  meta         4 words   mcause, mtval, mepc, SP at trap
 *
 * The signature region runs from `regs_out` to the end of `meta`.
 */

        .section .text.init, "ax", @progbits
        .globl  _start
_start:
        la      t0, trap_handler
        csrw    mtvec, t0
        la      sp, regs_in
        lw      x1, 4(sp)
        lw      x3, 8(sp)
        lw      x4, 12(sp)
        lw      x5, 16(sp)
        lw      x6, 20(sp)
        lw      x7, 24(sp)
        lw      x8, 28(sp)
        lw      x9, 32(sp)
        lw      x10, 36(sp)
        lw      x11, 40(sp)
        lw      x12, 44(sp)
        lw      x13, 48(sp)
        lw      x14, 52(sp)
        lw      x15, 56(sp)
        lw      x16, 60(sp)
        lw      x17, 64(sp)
        lw      x18, 68(sp)
        lw      x19, 72(sp)
        lw      x20, 76(sp)
        lw      x21, 80(sp)
        lw      x22, 84(sp)
        lw      x23, 88(sp)
        lw      x24, 92(sp)
        lw      x25, 96(sp)
        lw      x26, 100(sp)
        lw      x27, 104(sp)
        lw      x28, 108(sp)
        lw      x29, 112(sp)
        lw      x30, 116(sp)
        lw      x31, 120(sp)
        la      sp, scratch
        j       code_slot

        .balign 4
trap_handler:
        csrw    mscratch, sp
        la      sp, regs_out
        sw      x1, 4(sp)
        sw      x3, 8(sp)
        sw      x4, 12(sp)
        sw      x5, 16(sp)
        sw      x6, 20(sp)
        sw      x7, 24(sp)
        sw      x8, 28(sp)
        sw      x9, 32(sp)
        sw      x10, 36(sp)
        sw      x11, 40(sp)
        sw      x12, 44(sp)
        sw      x13, 48(sp)
        sw      x14, 52(sp)
        sw      x15, 56(sp)
        sw      x16, 60(sp)
        sw      x17, 64(sp)
        sw      x18, 68(sp)
        sw      x19, 72(sp)
        sw      x20, 76(sp)
        sw      x21, 80(sp)
        sw      x22, 84(sp)
        sw      x23, 88(sp)
        sw      x24, 92(sp)
        sw      x25, 96(sp)
        sw      x26, 100(sp)
        sw      x27, 104(sp)
        sw      x28, 108(sp)
        sw      x29, 112(sp)
        sw      x30, 116(sp)
        sw      x31, 120(sp)
        la      t0, meta
        csrr    t1, mcause
        sw      t1, 0(t0)
        csrr    t1, mtval
        sw      t1, 4(t0)
        csrr    t1, mepc
        sw      t1, 8(t0)
        csrr    t1, mscratch
        sw      t1, 12(t0)
        la      t0, tohost
        li      t1, 1
        sw      t1, 0(t0)
        sw      zero, 4(t0)
1:      j       1b

        .section .cosim, "awx", @progbits
        .globl  code_slot, regs_in, begin_signature, end_signature
code_slot:
        .fill   64, 4, 0x00100073       /* ebreak */
regs_in:
        .fill   32, 4, 0
begin_signature:
regs_out:
        .fill   32, 4, 0
scratch:
        .fill   64, 4, 0
meta:
        .fill   4, 4, 0
end_signature:

        .section .tohost, "aw", @progbits
        .balign 8
        .globl  tohost, fromhost
tohost:
        .dword  0
fromhost:
        .dword  0
