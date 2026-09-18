/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [NeonNTT_Autoformalised]
 *   Neon NTT - (Auto)formalised
 *   Hanno Becker
 *   https://eprint.iacr.org/2026/1223
 */

/*
 * RV32-IM ML-DSA forward NTT, fast-multiplier variant.
 *
 * Thin wrapper: the kernel body is shared via mldsa_ntt_rv32im_asm.i, which
 * computes the Barrett low(t*q) reduction with a single multiply by q here.
 * The slow-multiplier variant lives in mldsa_ntt_rv32im_slowmul_asm.S.
 * Exactly one is selected by MLD_USE_NATIVE_RV32IM_SLOW_MULTIPLIER.
 * The coarse Barrett output bound used by the shared kernel is proved in
 * @[NeonNTT_Autoformalised, Section 13.2].
 */

/*yaml
  Name: ntt_rv32im_asm
  Description: RV32IM ML-DSA forward NTT
  Signature: void mld_ntt_rv32im_asm(int32_t r[256], const int32_t zetas[510])
  ABI:
    Architecture: riscv32
    CallingConvention: ILP32
    Features: [RV32M]
    a0:
      type: buffer
      size_bytes: 1024
      permissions: read/write
      c_parameter: int32_t r[256]
      description: Input/output polynomial (256 x int32_t)
    a1:
      type: buffer
      size_bytes: 2040
      permissions: read-only
      c_parameter: const int32_t zetas[510]
      description: Twiddle table (255 Barrett pairs)
*/

#include "../../../common.h"
#if defined(MLD_ARITH_BACKEND_RV32IM) && \
    !defined(MLD_CONFIG_MULTILEVEL_NO_SHARED) && \
    !defined(MLD_USE_NATIVE_RV32IM_SLOW_MULTIPLIER)

/*
 * WARNING: This file is auto-derived from the mldsa-native source file
 *   dev/riscv32/src/mldsa_ntt_rv32im_asm.S using scripts/simpasm. Do not modify it directly.
 */

.text
.balign 4
.global MLD_ASM_NAMESPACE(ntt_rv32im_asm)
MLD_ASM_FN_SYMBOL(ntt_rv32im_asm)

        .cfi_startproc
        addi sp, sp, -0x20
        .cfi_adjust_cfa_offset 0x20
        sw s0, 0x0(sp)
        .cfi_rel_offset s0, 0x0
        sw s1, 0x4(sp)
        .cfi_rel_offset s1, 0x4
        sw s2, 0x8(sp)
        .cfi_rel_offset s2, 0x8
        sw s3, 0xc(sp)
        .cfi_rel_offset s3, 0xc
        sw s4, 0x10(sp)
        .cfi_rel_offset s4, 0x10
        sw s5, 0x14(sp)
        .cfi_rel_offset s5, 0x14
        lui t0, 0x7fe
        addi t0, t0, 0x1
        lw s0, 0x0(a1)
        lw s1, 0x4(a1)
        lw s2, 0x8(a1)
        lw s3, 0xc(a1)
        lw s4, 0x10(a1)
        lw s5, 0x14(a1)
        addi a1, a1, 0x18
        mv t2, a0
        addi t4, a0, 0x100

Lmld_ntt_rv32im_p1_loop:
        lw a2, 0x0(t2)
        lw a3, 0x100(t2)
        lw a4, 0x200(t2)
        lw a5, 0x300(t2)
        mulh a7, a4, s1
        mul a6, a4, s0
        mul a7, a7, t0
        sub a6, a6, a7
        sub a4, a2, a6
        add a2, a2, a6
        mulh a7, a5, s1
        mul a6, a5, s0
        mul a7, a7, t0
        sub a6, a6, a7
        sub a5, a3, a6
        add a3, a3, a6
        mulh a7, a3, s3
        mul a6, a3, s2
        mul a7, a7, t0
        sub a6, a6, a7
        sub a3, a2, a6
        add a2, a2, a6
        mulh a7, a5, s5
        mul a6, a5, s4
        mul a7, a7, t0
        sub a6, a6, a7
        sub a5, a4, a6
        add a4, a4, a6
        sw a2, 0x0(t2)
        sw a3, 0x100(t2)
        sw a4, 0x200(t2)
        sw a5, 0x300(t2)
        addi t2, t2, 0x4
        bne t2, t4, Lmld_ntt_rv32im_p1_loop
        mv t2, a0
        addi t3, a0, 0x400

Lmld_ntt_rv32im_p2_outer:
        lw s0, 0x0(a1)
        lw s1, 0x4(a1)
        lw s2, 0x8(a1)
        lw s3, 0xc(a1)
        lw s4, 0x10(a1)
        lw s5, 0x14(a1)
        addi a1, a1, 0x18
        addi t4, t2, 0x40

Lmld_ntt_rv32im_p2_inner:
        lw a2, 0x0(t2)
        lw a3, 0x40(t2)
        lw a4, 0x80(t2)
        lw a5, 0xc0(t2)
        mulh a7, a4, s1
        mul a6, a4, s0
        mul a7, a7, t0
        sub a6, a6, a7
        sub a4, a2, a6
        add a2, a2, a6
        mulh a7, a5, s1
        mul a6, a5, s0
        mul a7, a7, t0
        sub a6, a6, a7
        sub a5, a3, a6
        add a3, a3, a6
        mulh a7, a3, s3
        mul a6, a3, s2
        mul a7, a7, t0
        sub a6, a6, a7
        sub a3, a2, a6
        add a2, a2, a6
        mulh a7, a5, s5
        mul a6, a5, s4
        mul a7, a7, t0
        sub a6, a6, a7
        sub a5, a4, a6
        add a4, a4, a6
        sw a2, 0x0(t2)
        sw a3, 0x40(t2)
        sw a4, 0x80(t2)
        sw a5, 0xc0(t2)
        addi t2, t2, 0x4
        bne t2, t4, Lmld_ntt_rv32im_p2_inner
        addi t2, t2, 0xc0
        bne t2, t3, Lmld_ntt_rv32im_p2_outer
        mv t2, a0
        addi t3, a0, 0x400

Lmld_ntt_rv32im_p3_outer:
        lw s0, 0x0(a1)
        lw s1, 0x4(a1)
        lw s2, 0x8(a1)
        lw s3, 0xc(a1)
        lw s4, 0x10(a1)
        lw s5, 0x14(a1)
        addi a1, a1, 0x18
        addi t4, t2, 0x10

Lmld_ntt_rv32im_p3_inner:
        lw a2, 0x0(t2)
        lw a3, 0x10(t2)
        lw a4, 0x20(t2)
        lw a5, 0x30(t2)
        mulh a7, a4, s1
        mul a6, a4, s0
        mul a7, a7, t0
        sub a6, a6, a7
        sub a4, a2, a6
        add a2, a2, a6
        mulh a7, a5, s1
        mul a6, a5, s0
        mul a7, a7, t0
        sub a6, a6, a7
        sub a5, a3, a6
        add a3, a3, a6
        mulh a7, a3, s3
        mul a6, a3, s2
        mul a7, a7, t0
        sub a6, a6, a7
        sub a3, a2, a6
        add a2, a2, a6
        mulh a7, a5, s5
        mul a6, a5, s4
        mul a7, a7, t0
        sub a6, a6, a7
        sub a5, a4, a6
        add a4, a4, a6
        sw a2, 0x0(t2)
        sw a3, 0x10(t2)
        sw a4, 0x20(t2)
        sw a5, 0x30(t2)
        addi t2, t2, 0x4
        bne t2, t4, Lmld_ntt_rv32im_p3_inner
        addi t2, t2, 0x30
        bne t2, t3, Lmld_ntt_rv32im_p3_outer
        mv t2, a0
        addi t3, a0, 0x400

Lmld_ntt_rv32im_p4_outer:
        lw s0, 0x0(a1)
        lw s1, 0x4(a1)
        lw s2, 0x8(a1)
        lw s3, 0xc(a1)
        lw s4, 0x10(a1)
        lw s5, 0x14(a1)
        addi a1, a1, 0x18
        lw a2, 0x0(t2)
        lw a3, 0x4(t2)
        lw a4, 0x8(t2)
        lw a5, 0xc(t2)
        mulh a7, a4, s1
        mul a6, a4, s0
        mul a7, a7, t0
        sub a6, a6, a7
        sub a4, a2, a6
        add a2, a2, a6
        mulh a7, a5, s1
        mul a6, a5, s0
        mul a7, a7, t0
        sub a6, a6, a7
        sub a5, a3, a6
        add a3, a3, a6
        mulh a7, a3, s3
        mul a6, a3, s2
        mul a7, a7, t0
        sub a6, a6, a7
        sub a3, a2, a6
        add a2, a2, a6
        mulh a7, a5, s5
        mul a6, a5, s4
        mul a7, a7, t0
        sub a6, a6, a7
        sub a5, a4, a6
        add a4, a4, a6
        sw a2, 0x0(t2)
        sw a3, 0x4(t2)
        sw a4, 0x8(t2)
        sw a5, 0xc(t2)
        addi t2, t2, 0x10
        bne t2, t3, Lmld_ntt_rv32im_p4_outer
        lw s0, 0x0(sp)
        .cfi_restore s0
        lw s1, 0x4(sp)
        .cfi_restore s1
        lw s2, 0x8(sp)
        .cfi_restore s2
        lw s3, 0xc(sp)
        .cfi_restore s3
        lw s4, 0x10(sp)
        .cfi_restore s4
        lw s5, 0x14(sp)
        .cfi_restore s5
        addi sp, sp, 0x20
        .cfi_adjust_cfa_offset -0x20
        ret
        .cfi_endproc

MLD_ASM_FN_SIZE(ntt_rv32im_asm)

#endif /* MLD_ARITH_BACKEND_RV32IM && !MLD_CONFIG_MULTILEVEL_NO_SHARED && \
          !MLD_USE_NATIVE_RV32IM_SLOW_MULTIPLIER */

#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
