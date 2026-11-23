/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/*
 * Constant-time check of the candidate's ML-KEM API under valgrind
 * memcheck: the secret inputs (the coins of keypair_derand and
 * enc_derand, and the secret parts of the decapsulation key, s and z, for
 * dec) are marked undefined, so memcheck reports any branch or memory
 * address that depends on them. The encapsulation key and its hash in the
 * decapsulation key are public. The library must itself declassify values
 * that are public although computed from secrets (the seed rho of the
 * matrix in keypair_derand), as mlkem-native does when built with
 * MLK_CONFIG_CT_TESTING_ENABLED.
 *
 * usage: valgrind --error-exitcode=1 ./test_ct [ITERATIONS]
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <valgrind/memcheck.h>

#define DECLARE(L)                                                     \
  int mlkem##L##_keypair_derand(uint8_t *, uint8_t *, const uint8_t *); \
  int mlkem##L##_enc_derand(uint8_t *, uint8_t *, const uint8_t *,      \
                            const uint8_t *);                           \
  int mlkem##L##_dec(uint8_t *, const uint8_t *, const uint8_t *);      \
  int mlkem##L##_check_pk(const uint8_t *);                             \
  int mlkem##L##_check_sk(const uint8_t *);
DECLARE(512)
DECLARE(768)
DECLARE(1024)

int randombytes(uint8_t *out, size_t outlen);
int randombytes(uint8_t *out, size_t outlen)
{
  (void)out, (void)outlen;
  abort();
}

static uint64_t rng = 1;
static void randfill(uint8_t *p, size_t n)
{
  for (size_t i = 0; i < n; i++)
  {
    rng ^= rng << 13, rng ^= rng >> 7, rng ^= rng << 17;
    p[i] = (uint8_t)rng;
  }
}

#define SECRET(p, n) VALGRIND_MAKE_MEM_UNDEFINED(p, n)
#define PUBLIC(p, n) VALGRIND_MAKE_MEM_DEFINED(p, n)

#define RUN(L, PKB, SKB, CTB)                                             \
  do                                                                      \
  {                                                                       \
    static uint8_t pk[PKB], sk[SKB], ct[CTB], ss[32], coins[64];          \
    int r = 0;                                                            \
    randfill(coins, 64);                                                  \
    SECRET(coins, 64);                                                    \
    r |= mlkem##L##_keypair_derand(pk, sk, coins);                        \
    PUBLIC(pk, PKB);                                                      \
    PUBLIC(sk, SKB);                                                      \
    SECRET(sk, 384 * (L / 256));                                          \
    SECRET(sk + SKB - 32, 32);                                            \
    r |= mlkem##L##_check_pk(pk);                                         \
    r |= mlkem##L##_check_sk(sk);                                         \
    randfill(coins, 32);                                                  \
    SECRET(coins, 32);                                                    \
    r |= mlkem##L##_enc_derand(ct, ss, pk, coins);                        \
    PUBLIC(ct, CTB);                                                      \
    r |= mlkem##L##_dec(ss, ct, sk);                                      \
    ct[it % CTB] ^= 1; /* implicit rejection */                           \
    r |= mlkem##L##_dec(ss, ct, sk);                                      \
    PUBLIC(&r, sizeof(r));                                                \
    if (r != 0)                                                           \
    {                                                                     \
      printf("ML-KEM-%d: unexpected failure\n", L);                       \
      return 1;                                                           \
    }                                                                     \
  } while (0)

int main(int argc, char **argv)
{
  unsigned n = argc > 1 ? (unsigned)atoi(argv[1]) : 3;
  for (unsigned it = 0; it < n; it++)
  {
    RUN(512, 800, 1632, 768);
    RUN(768, 1184, 2400, 1088);
    RUN(1024, 1568, 3168, 1568);
  }
  printf("test_ct: %u iterations done\n", n);
  return 0;
}
