/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *
 * The randomized functions of mlkem-native's API, in C: randombytes for
 * the coins, then the deterministic function in asm. As in mlkem-native,
 * the coins are zeroed afterwards and a failure of randombytes gives -3
 * (MLK_ERR_RNG_FAIL).
 */
#include <stddef.h>
#include <stdint.h>

int randombytes(uint8_t *out, size_t outlen);

static void zeroize(void *p, size_t n)
{
  volatile uint8_t *q = (volatile uint8_t *)p;
  while (n--) *q++ = 0;
}

#define RANDOMIZED(L)                                                       \
  int mlkem##L##_keypair_derand(uint8_t *pk, uint8_t *sk,                 \
                                const uint8_t *coins);                    \
  int mlkem##L##_enc_derand(uint8_t *ct, uint8_t *ss, const uint8_t *pk,  \
                            const uint8_t *coins);                        \
  int mlkem##L##_keypair(uint8_t *pk, uint8_t *sk);                       \
  int mlkem##L##_enc(uint8_t *ct, uint8_t *ss, const uint8_t *pk);        \
  int mlkem##L##_keypair(uint8_t *pk, uint8_t *sk)                        \
  {                                                                       \
    uint8_t coins[64];                                                    \
    int r = randombytes(coins, 64) != 0                                   \
                ? -3                                                      \
                : mlkem##L##_keypair_derand(pk, sk, coins);               \
    zeroize(coins, sizeof(coins));                                        \
    return r;                                                             \
  }                                                                       \
  int mlkem##L##_enc(uint8_t *ct, uint8_t *ss, const uint8_t *pk)         \
  {                                                                       \
    uint8_t coins[32];                                                    \
    int r = randombytes(coins, 32) != 0                                   \
                ? -3                                                      \
                : mlkem##L##_enc_derand(ct, ss, pk, coins);               \
    zeroize(coins, sizeof(coins));                                        \
    return r;                                                             \
  }

RANDOMIZED(512)
RANDOMIZED(768)
RANDOMIZED(1024)
