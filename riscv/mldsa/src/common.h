/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

#ifndef S2N_BIGNUM_RISCV_MLDSA_COMMON_H
#define S2N_BIGNUM_RISCV_MLDSA_COMMON_H

/*
 * Minimal build adapter for the generated mldsa-native assembly. Keep the
 * namespacing equal to a fixed-level ML-DSA-44 build so that the resulting
 * objects agree with the upstream proof inputs.
 */

#define MLD_CONCAT_(x1, x2) x1##x2
#define MLD_CONCAT(x1, x2) MLD_CONCAT_(x1, x2)

#define MLD_CONFIG_NAMESPACE_PREFIX PQCP_MLDSA_NATIVE_MLDSA44
#define MLD_NAMESPACE_PREFIX MLD_CONCAT(MLD_CONFIG_NAMESPACE_PREFIX, _)
#define MLD_NAMESPACE(sym) MLD_CONCAT(MLD_NAMESPACE_PREFIX, sym)

#if !defined(__APPLE__)
#define MLD_ASM_NAMESPACE(sym) MLD_NAMESPACE(sym)
#else
#define MLD_ASM_NAMESPACE(sym) MLD_CONCAT(_, MLD_NAMESPACE(sym))
#endif

#define MLD_ASM_FN_SYMBOL(sym) MLD_ASM_NAMESPACE(sym):

#if defined(__ELF__)
#define MLD_ASM_FN_SIZE(sym) \
  .size MLD_ASM_NAMESPACE(sym), .- MLD_ASM_NAMESPACE(sym)
#else
#define MLD_ASM_FN_SIZE(sym)
#endif

#if defined(MLD_CONFIG_USE_NATIVE_BACKEND_ARITH)
#include MLD_CONFIG_ARITH_BACKEND_FILE
#endif

#endif /* S2N_BIGNUM_RISCV_MLDSA_COMMON_H */
