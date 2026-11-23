/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *
 * Layout of the constants block of the mlkem_native2 functions, defined in
 * mlkem_native2_constants.S. The MLKEM_C_* byte offsets are used by the
 * asm, the struct type by C code.
 */
#ifndef MLKEM_NATIVE2_CONSTS_H
#define MLKEM_NATIVE2_CONSTS_H

#define MLKEM_C_RC 0
#define MLKEM_C_NTT_ZETAS_12345 192
#define MLKEM_C_NTT_ZETAS_67 352
#define MLKEM_C_INTT_ZETAS_12345 1120
#define MLKEM_C_INTT_ZETAS_67 1280
#define MLKEM_C_MULCACHE_ZETAS 2048
#define MLKEM_C_MULCACHE_ZETAS_TWISTED 2304
#define MLKEM_C_REJ_UNIFORM_TABLE 2560
#define MLKEM_C_SIZE 6656

#ifndef __ASSEMBLER__
#include <stdint.h>
typedef struct
{
  uint64_t rc[24];
  int16_t ntt_zetas_12345[80];
  int16_t ntt_zetas_67[384];
  int16_t intt_zetas_12345[80];
  int16_t intt_zetas_67[384];
  int16_t mulcache_zetas[128];
  int16_t mulcache_zetas_twisted[128];
  uint8_t rej_uniform_table[4096];
} mlkem_native2_consts;
extern const mlkem_native2_consts mlkem_native2_constants;
#endif

#endif
