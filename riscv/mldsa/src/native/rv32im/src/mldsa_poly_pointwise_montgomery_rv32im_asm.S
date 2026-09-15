/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * RV32-IM ML-DSA pointwise polynomial multiplication with Montgomery
 * reduction. Computes
 *
 *     a[i] = (a[i] * b[i]) * R^-1  mod q,    R = 2^32, |result| < q,
 *
 * for 0 <= i < 256, in-place in a.
 *
 * Modular arithmetic: signed Montgomery reduction. Write R = 2^32 and
 * QINV = q^-1 mod R = 58728449. Unlike the NTT, neither operand is constant,
 * so a twisted constant cannot be precomputed. For p = a*b, the kernel uses
 * four multiplications:
 *
 *     plo = low(p)
 *     phi = high(p)
 *     m   = low(plo * QINV), interpreted as signed
 *     mhi = high(m * q)
 *     r   = phi - mhi = (p - m*q) / R.
 *
 * The low words of p and m*q agree because m*q == plo (mod R), so p-m*q
 * is divisible by R and the high-word subtraction computes its quotient.
 * Consequently r == a*b*R^-1 (mod q).
 *
 * MLD_NTT_BOUND is the exclusive postcondition of the generic C and native
 * forward-NTT interfaces and the exclusive input precondition of pointwise
 * Montgomery multiplication. It is therefore the full input range exposed
 * to this routine by the C/CBMC-facing interface, not an additional
 * assembly-specific assumption.
 *
 * Inputs satisfy
 *
 *   |a|, |b| < MLD_NTT_BOUND = 94279698,
 *   |p| < 94279698^2 = 8888661454971204
 *       < q*R/2 = 17996808470921216.
 *
 * Signed Montgomery reduction then gives |r| < |p|/R + q/2 < q. In
 * particular, `phi-mhi` is in signed int32 range and cannot overflow. The
 * q-bound is also the pointwise postcondition and the inverse-NTT input
 * precondition, so the forward NTT, pointwise product, and inverse NTT
 * compose under the shared contracts.
 */

/*yaml
  Name: poly_pointwise_montgomery_rv32im_asm
  Description: RV32IM pointwise Montgomery multiplication of two polynomials
  Signature: void mld_poly_pointwise_montgomery_rv32im_asm(int32_t a[256], const int32_t b[256])
  ABI:
    Architecture: riscv32
    CallingConvention: ILP32
    Features: [RV32M]
    a0:
      type: buffer
      size_bytes: 1024
      permissions: read/write
      c_parameter: int32_t a[256]
      description: Input/output polynomial (256 x int32_t)
    a1:
      type: buffer
      size_bytes: 1024
      permissions: read-only
      c_parameter: const int32_t b[256]
      description: Input polynomial (256 x int32_t)
*/

#include "../../../common.h"
#if defined(MLD_ARITH_BACKEND_RV32IM) &&                                      \
    (!defined(MLD_CONFIG_NO_SIGN_API) || !defined(MLD_CONFIG_NO_VERIFY_API) || \
     defined(MLD_CONFIG_REDUCE_RAM) || defined(MLD_UNIT_TEST)) &&              \
    !defined(MLD_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mldsa-native source file
 *   dev/riscv32/src/mldsa_poly_pointwise_montgomery_rv32im_asm.S using scripts/simpasm. Do not modify it directly.
 */

.text
.balign 4
.global MLD_ASM_NAMESPACE(poly_pointwise_montgomery_rv32im_asm)
MLD_ASM_FN_SYMBOL(poly_pointwise_montgomery_rv32im_asm)

        .cfi_startproc
        addi sp, sp, -0x10
        .cfi_adjust_cfa_offset 0x10
        sw s0, 0x0(sp)
        .cfi_rel_offset s0, 0x0
        sw s1, 0x4(sp)
        .cfi_rel_offset s1, 0x4
        lui s0, 0x7fe
        addi s0, s0, 0x1
        lui s1, 0x3802
        addi s1, s1, 0x1
        addi t0, a0, 0x400

Lmld_poly_pointwise_montgomery_rv32im_loop:
        lw a2, 0x0(a0)
        lw a3, 0x0(a1)
        mul a4, a2, a3
        mulh a5, a2, a3
        mul a6, a4, s1
        mulh a7, a6, s0
        sub a2, a5, a7
        sw a2, 0x0(a0)
        addi a0, a0, 0x4
        addi a1, a1, 0x4
        bne a0, t0, Lmld_poly_pointwise_montgomery_rv32im_loop
        lw s0, 0x0(sp)
        .cfi_restore s0
        lw s1, 0x4(sp)
        .cfi_restore s1
        addi sp, sp, 0x10
        .cfi_adjust_cfa_offset -0x10
        ret
        .cfi_endproc

MLD_ASM_FN_SIZE(poly_pointwise_montgomery_rv32im_asm)

#endif /* MLD_ARITH_BACKEND_RV32IM && (!MLD_CONFIG_NO_SIGN_API || \
          !MLD_CONFIG_NO_VERIFY_API || MLD_CONFIG_REDUCE_RAM || MLD_UNIT_TEST) \
          && !MLD_CONFIG_MULTILEVEL_NO_SHARED */

#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
