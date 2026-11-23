/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *
 * Layout of the constants block of the x86 mlkem_native2 functions,
 * defined in mlkem_native2_constants.S. The MLKEM_C_* byte offsets
 * are used by the asm, the struct type by C code. Every field is
 * 32-byte aligned (the block itself 64-byte aligned).
 */
#ifndef MLKEM_NATIVE2_CONSTS_H
#define MLKEM_NATIVE2_CONSTS_H

#define MLKEM_C_RC 0
#define MLKEM_C_KECCAK_RHO8 192
#define MLKEM_C_KECCAK_RHO56 224
#define MLKEM_C_QDATA 256
#define MLKEM_C_COMPRESS_D4_DATA 1504
#define MLKEM_C_DECOMPRESS_D4_DATA 1536
#define MLKEM_C_COMPRESS_D5_DATA 1568
#define MLKEM_C_DECOMPRESS_D5_DATA 1600
#define MLKEM_C_COMPRESS_D10_DATA 1696
#define MLKEM_C_DECOMPRESS_D10_DATA 1728
#define MLKEM_C_COMPRESS_D11_DATA 1760
#define MLKEM_C_DECOMPRESS_D11_DATA 1824
#define MLKEM_C_REJ_UNIFORM_TABLE 1952
#define MLKEM_C_SIZE 6048

#ifndef __ASSEMBLER__
#include <stdint.h>
typedef struct
{
  uint64_t rc[24];
  uint64_t keccak_rho8[4];
  uint64_t keccak_rho56[4];
  int16_t qdata[624];
  uint8_t compress_d4_data[32];
  uint8_t decompress_d4_data[32];
  uint8_t compress_d5_data[32];
  uint8_t decompress_d5_data[96];
  uint8_t compress_d10_data[32];
  uint8_t decompress_d10_data[32];
  uint8_t compress_d11_data[64];
  uint8_t decompress_d11_data[128];
  uint8_t rej_uniform_table[4096];
} mlkem_native2_consts;
extern const mlkem_native2_consts mlkem_native2_constants;
#endif

#endif
