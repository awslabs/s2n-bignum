/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/*
 * mlkem-native's KAT output (test/src/gen_KAT.c) for the candidate's
 * ML-KEM-L: 100 key pairs, ciphertexts and shared secrets from coins
 * chained through SHAKE256. Its SHA-256 should be the kat-sha256 of
 * mlkem-native's META.yml. The SHAKE256 is the reference's.
 *
 * usage: kat 512|768|1024
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void ref_shake256(uint8_t *out, size_t outlen, const uint8_t *in,
                  size_t inlen);

#define DECLARE(L)                                                     \
  int mlkem##L##_keypair_derand(uint8_t *, uint8_t *, const uint8_t *); \
  int mlkem##L##_enc_derand(uint8_t *, uint8_t *, const uint8_t *,      \
                            const uint8_t *);                           \
  int mlkem##L##_dec(uint8_t *, const uint8_t *, const uint8_t *);
DECLARE(512)
DECLARE(768)
DECLARE(1024)

/* Needed to link the randomized API, which the KAT does not use */
int randombytes(uint8_t *out, size_t outlen);
int randombytes(uint8_t *out, size_t outlen)
{
  (void)out, (void)outlen;
  abort();
}

static void print_hex(const char *label, const uint8_t *data, size_t size)
{
  printf("%s = ", label);
  for (size_t i = 0; i < size; i++) printf("%02x", data[i]);
  printf("\n");
}

int main(int argc, char **argv)
{
  int l = argc > 1 ? atoi(argv[1]) : 0;
  size_t pkb = l == 512 ? 800 : l == 768 ? 1184 : 1568;
  size_t skb = l == 512 ? 1632 : l == 768 ? 2400 : 3168;
  size_t ctb = l == 512 ? 768 : l == 768 ? 1088 : 1568;
  uint8_t coins[96], pk[1568], sk[3168], ct[1568], ss1[32], ss2[32];
  uint8_t seed[64];
  int (*kp)(uint8_t *, uint8_t *, const uint8_t *) =
      l == 512 ? mlkem512_keypair_derand
      : l == 768 ? mlkem768_keypair_derand : mlkem1024_keypair_derand;
  int (*enc)(uint8_t *, uint8_t *, const uint8_t *, const uint8_t *) =
      l == 512 ? mlkem512_enc_derand
      : l == 768 ? mlkem768_enc_derand : mlkem1024_enc_derand;
  int (*dec)(uint8_t *, const uint8_t *, const uint8_t *) =
      l == 512 ? mlkem512_dec : l == 768 ? mlkem768_dec : mlkem1024_dec;
  if (l != 512 && l != 768 && l != 1024)
  {
    fprintf(stderr, "usage: kat 512|768|1024\n");
    return 2;
  }
  for (int i = 0; i < 64; i++) seed[i] = (uint8_t)(32 + i);
  ref_shake256(coins, sizeof(coins), seed, sizeof(seed));
  for (int i = 0; i < 100; i++)
  {
    ref_shake256(coins, sizeof(coins), coins, sizeof(coins));
    if (kp(pk, sk, coins) != 0) return 1;
    print_hex("pk", pk, pkb);
    print_hex("sk", sk, skb);
    if (enc(ct, ss1, pk, coins + 64) != 0) return 1;
    print_hex("ct", ct, ctb);
    if (dec(ss2, ct, sk) != 0 || memcmp(ss1, ss2, 32) != 0) return 1;
    print_hex("ss", ss1, 32);
  }
  return 0;
}
