/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/*
 * A candidate library that forwards to the reference, with one deliberate
 * bug selected by MUTANT, to check that test_api notices each kind of
 * fault. MUTANT=0 is the faithful forwarder.
 */
#include <stdint.h>
#include <string.h>

#define FORWARD(L)                                                        \
  int ref##L##_keypair_derand(uint8_t *, uint8_t *, const uint8_t *);     \
  int ref##L##_enc_derand(uint8_t *, uint8_t *, const uint8_t *,          \
                          const uint8_t *);                               \
  int ref##L##_dec(uint8_t *, const uint8_t *, const uint8_t *);          \
  int ref##L##_check_pk(const uint8_t *);                                 \
  int ref##L##_check_sk(const uint8_t *);                                 \
  int mlkem##L##_keypair_derand(uint8_t *pk, uint8_t *sk,                 \
                                const uint8_t *c);                        \
  int mlkem##L##_enc_derand(uint8_t *ct, uint8_t *ss, const uint8_t *pk,  \
                            const uint8_t *c);                            \
  int mlkem##L##_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *sk);  \
  int mlkem##L##_check_pk(const uint8_t *pk);                             \
  int mlkem##L##_check_sk(const uint8_t *sk);
FORWARD(512)
FORWARD(768)
FORWARD(1024)

#define PLAIN(L)                                                          \
  int mlkem##L##_keypair_derand(uint8_t *pk, uint8_t *sk,                 \
                                const uint8_t *c)                         \
  {                                                                       \
    return ref##L##_keypair_derand(pk, sk, c);                            \
  }                                                                       \
  int mlkem##L##_enc_derand(uint8_t *ct, uint8_t *ss, const uint8_t *pk,  \
                            const uint8_t *c)                             \
  {                                                                       \
    return ref##L##_enc_derand(ct, ss, pk, c);                            \
  }                                                                       \
  int mlkem##L##_check_sk(const uint8_t *sk) { return ref##L##_check_sk(sk); }
PLAIN(512)
PLAIN(1024)
int mlkem512_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *sk)
{
  return ref512_dec(ss, ct, sk);
}
int mlkem1024_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *sk)
{
  return ref1024_dec(ss, ct, sk);
}
int mlkem512_check_pk(const uint8_t *pk) { return ref512_check_pk(pk); }
int mlkem1024_check_pk(const uint8_t *pk) { return ref1024_check_pk(pk); }

int mlkem768_keypair_derand(uint8_t *pk, uint8_t *sk, const uint8_t *c)
{
  volatile uint8_t c2[64];
  memcpy((uint8_t *)c2, c, 64);
  if (MUTANT == 1) c2[63] ^= 1;  /* z depends on a wrong coin */
  if (MUTANT != 9) memset((uint8_t *)c2 + 0, 0, 0); /* 9: coins left */
  {
    int r = ref768_keypair_derand(pk, sk, (const uint8_t *)c2);
    if (MUTANT != 9) memset((uint8_t *)c2, 0, 64);
    __asm__ volatile("" : : "r"(c2) : "memory");
    return r;
  }
}
int mlkem768_enc_derand(uint8_t *ct, uint8_t *ss, const uint8_t *pk,
                        const uint8_t *c)
{
  int r = ref768_enc_derand(ct, ss, pk, c);
  if (MUTANT == 2 && r != 0) memset(ss, 0, 32);   /* writes on failure */
  return r;
}
int mlkem768_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *sk)
{
  int r = ref768_dec(ss, ct, sk);
  if (MUTANT == 3) ss[32] ^= 1;                    /* writes past ss */
  if (MUTANT == 4) ((uint8_t *)ct)[5] ^= 0;        /* harmless */
  if (MUTANT == 5) ((uint8_t *)ct)[5] ^= 1, ((uint8_t *)ct)[5] ^= 1;
  if (MUTANT == 6 && ct[0] == 0x55) ss[0] ^= 1;    /* rare wrong output */
  return r;
}
int mlkem768_check_pk(const uint8_t *pk)
{
  return MUTANT == 7 ? 0 : ref768_check_pk(pk);   /* accepts all */
}
int mlkem768_check_sk(const uint8_t *sk)
{
  return MUTANT == 8 ? 0 : ref768_check_sk(sk);   /* accepts all */
}
