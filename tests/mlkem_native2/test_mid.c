/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/*
 * Tests of the mid-level mlkem_native2 functions against the reference
 * (mlkem-native's portable C, prefix "ref"):
 *
 *  - mlkem_gen_matrix, for k = 2, 3, 4, transposed or not, with no jobs,
 *    one or two hash jobs (SHA3-256 and SHAKE256, the lengths of ML-KEM's
 *    H(pk) and J(z || c) and others), against ref{512,768,1024}_gen_matrix
 *    and ref_sha3_256 / ref_shake256; jobs and noise not given are NULL,
 *    which must not be read, and inactive jobs (ds = 0) have a message and
 *    an output, which must not be written.
 *
 * Outputs sit between guard bytes, inputs must be unchanged. Functions
 * missing from the link (weak symbols) are skipped. On x86_64 the matrix
 * is compared in the custom NTT order of the x86 backend (each reference
 * polynomial permuted by mlkem_unpack), and the buffers are 64-byte
 * aligned, as the x86 kernels need.
 *
 * usage: test_mid [ITERATIONS [SEED]]   (default 1000, 1)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "mlkem_native2_consts.h"

#define Q 3329

typedef struct
{
  const uint8_t *msg;
  uint64_t len, ds;
  uint8_t *out;
} mlkem_hash_job;

typedef struct
{
  const uint8_t *sigma;
  uint64_t nonce0, n;
  int16_t *out;
} mlkem_noise_job;

#define WEAK __attribute__((weak))

void mlkem_gen_matrix(int16_t *a, const uint8_t rho[32], uint64_t k,
                      uint64_t flags, const mlkem_hash_job jobs[2],
                      const mlkem_noise_job *noise,
                      const mlkem_native2_consts *c) WEAK;

void mlkem_getnoise(int16_t *r, const uint8_t sigma[32], uint64_t nonce0,
                    uint64_t n, uint64_t n1, uint64_t eta1,
                    const mlkem_native2_consts *c) WEAK;
void mlkem_hash_h(uint8_t out[32], const uint8_t *in, uint64_t len,
                    const mlkem_native2_consts *c) WEAK;
void mlkem_hash_g(uint8_t out[64], const uint8_t *in, uint64_t len,
                    const mlkem_native2_consts *c) WEAK;

#if defined(__x86_64__)
/* On x86_64 the matrix is in the custom NTT order of the x86 backend:
   mlkem_unpack applied to each polynomial of the reference */
void mlkem_unpack(int16_t a[256]);
#endif
void ref_sha3_512(uint8_t *out, const uint8_t *in, size_t inlen);
void ref_poly_cbd2(int16_t *r, const uint8_t buf[128]);
void ref_poly_cbd3(int16_t *r, const uint8_t buf[192]);

void ref512_gen_matrix(int16_t *a, const uint8_t seed[32], int transposed);
void ref768_gen_matrix(int16_t *a, const uint8_t seed[32], int transposed);
void ref1024_gen_matrix(int16_t *a, const uint8_t seed[32], int transposed);
void ref_sha3_256(uint8_t *out, const uint8_t *in, size_t inlen);
void ref_shake256(uint8_t *out, size_t outlen, const uint8_t *in,
                  size_t inlen);

int randombytes(uint8_t *out, size_t outlen);
int randombytes(uint8_t *out, size_t outlen)
{
  (void)out, (void)outlen;
  abort();
}

static uint64_t rng;
static uint64_t rand64(void)
{
  uint64_t z = (rng += 0x9e3779b97f4a7c15ULL);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}
static void randfill(void *p, size_t n)
{
  for (size_t i = 0; i < n; i++) ((uint8_t *)p)[i] = (uint8_t)rand64();
}

static unsigned long failures, checks;

#define GUARD 64
#define FILL 0x5a

static int guarded_same(const char *what, const uint8_t *g, const void *want,
                        size_t n, unsigned long it)
{
  checks++;
  for (size_t i = 0; i < GUARD; i++)
    if (g[i] != FILL || g[GUARD + n + i] != FILL)
    {
      printf("FAIL %s iteration %lu: guard bytes overwritten\n", what, it);
      return 1;
    }
  for (size_t i = 0; i < n; i++)
    if (g[GUARD + i] != ((const uint8_t *)want)[i])
    {
      printf("FAIL %s iteration %lu: byte %zu differs\n", what, it, i);
      return 1;
    }
  return 0;
}

/* ------------------------------------------------------------------------- */

static int test_gen_matrix(unsigned long it)
{
  static uint8_t ga[GUARD + 16 * 512 + GUARD] __attribute__((aligned(64))),
      gd[2][GUARD + 32 + GUARD];
  static int16_t want[16 * 256] __attribute__((aligned(32)));
  static uint8_t msg[2][2048], copy[2][2048];
  uint8_t rho[32], rho2[32], wantd[2][32];
  unsigned k = 2 + (unsigned)(it % 3), transposed = (unsigned)(it / 3) % 2;
  /* mode 0: no jobs, 1: job 1, 2: both, 3: job 0 */
  unsigned mode = (unsigned)(it / 6) % 4;
  size_t pkb = 384 * k + 32, jb = 32 + 32 * (k == 4 ? 11 * 4 + 5 : 10 * k + 4);
  mlkem_hash_job jobs[2];
  size_t len[2] = {0, 0};
  int bad = 0;

  randfill(rho, 32);
  memcpy(rho2, rho, 32);
  memset(jobs, 0, sizeof(jobs));
  /* The lengths: those of ML-KEM's H(pk) and J(z || c) mostly, or random
     multiples of 8 up to 2048, which may outlast the matrix */
  for (int j = 0; j < 2; j++)
  {
    len[j] = (j == 1 ? pkb : jb);
    if (it % 7 == 6) len[j] = 8 * (rand64() % 257);
    randfill(msg[j], len[j]);
    memcpy(copy[j], msg[j], len[j]);
    memset(gd[j], FILL, sizeof(gd[j]));
  }
  for (int j = 0; j < 2; j++)
    jobs[j] = (mlkem_hash_job){msg[j], len[j], 0, gd[j] + GUARD};
  if (mode == 1 || mode == 2) jobs[1].ds = 0x06;
  if (mode == 2 || mode == 3) jobs[0].ds = 0x1f;

  /* A noise job in half the tests: 0 to 9 polynomials of eta = 2 */
  static uint8_t gn[GUARD + 9 * 512 + GUARD] __attribute__((aligned(64)));
  static int16_t wantn[9 * 256] __attribute__((aligned(32)));
  uint8_t sigma[32];
  unsigned nn = (it / 24) % 2 ? (unsigned)(rand64() % 10) : 0;
  unsigned nonce0 = (unsigned)(rand64() % (257 - nn));
  mlkem_noise_job noise = {sigma, nonce0, nn, (int16_t *)(gn + GUARD)};
  randfill(sigma, 32);
  memset(gn, FILL, sizeof(gn));
  memset(ga, FILL, sizeof(ga));
  /* The flags: bit 0 transposed, bit 1 jobs given, bit 2 noise given */
  int given = nn || it % 48 == 0;
  mlkem_gen_matrix((int16_t *)(ga + GUARD), rho, k,
                   transposed | (mode ? 2 : 0) | (given ? 4 : 0),
                   mode ? jobs : NULL, given ? &noise : NULL,
                   &mlkem_native2_constants);
  for (unsigned i = 0; i < nn; i++)
  {
    uint8_t in[33], nb[128];
    memcpy(in, sigma, 32);
    in[32] = (uint8_t)(nonce0 + i);
    ref_shake256(nb, 128, in, 33);
    ref_poly_cbd2(wantn + 256 * i, nb);
  }
  bad |= guarded_same("mlkem_gen_matrix (noise)", gn, wantn, 512 * nn, it);
  if (k == 2) ref512_gen_matrix(want, rho, (int)transposed);
  if (k == 3) ref768_gen_matrix(want, rho, (int)transposed);
  if (k == 4) ref1024_gen_matrix(want, rho, (int)transposed);
#if defined(__x86_64__)
  for (unsigned i = 0; i < k * k; i++) mlkem_unpack(want + 256 * i);
#endif
  bad |= guarded_same("mlkem_gen_matrix (matrix)", ga, want, 512 * k * k, it);
  checks++;
  if (memcmp(rho, rho2, 32) != 0)
    printf("FAIL mlkem_gen_matrix iteration %lu: rho modified\n", it), bad = 1;
  if (jobs[1].ds)
  {
    ref_sha3_256(wantd[1], msg[1], len[1]);
    bad |= guarded_same("mlkem_gen_matrix (job 1)", gd[1], wantd[1], 32, it);
  }
  if (jobs[0].ds)
  {
    ref_shake256(wantd[0], 32, msg[0], len[0]);
    bad |= guarded_same("mlkem_gen_matrix (job 0)", gd[0], wantd[0], 32, it);
  }
  for (int j = 0; j < 2; j++)
  {
    checks++;
    if (memcmp(msg[j], copy[j], len[j]) != 0)
      printf("FAIL mlkem_gen_matrix iteration %lu: message modified\n", it),
          bad = 1;
    if (!jobs[j].ds)
      for (size_t i = 0; i < sizeof(gd[j]); i++)
        if (gd[j][i] != FILL)
        {
          printf("FAIL mlkem_gen_matrix iteration %lu: inactive job's output "
                 "written\n", it);
          bad = 1;
          break;
        }
  }
  return bad;
}

/* ------------------------------------------------------------------------- */

static int test_getnoise(unsigned long it)
{
  static uint8_t gr[GUARD + 12 * 512 + GUARD] __attribute__((aligned(64)));
  static int16_t want[12 * 256] __attribute__((aligned(32)));
  uint8_t sigma[32], sigma2[32], in[33], buf[192];
  unsigned n, n1, eta1, nonce0;
  int bad = 0;
  /* The configurations of ML-KEM first, then random ones */
  static const unsigned conf[][3] = {{4, 4, 3}, {6, 6, 2}, {8, 8, 2},
                                     {5, 2, 3}, {7, 3, 2}, {9, 4, 2}};
  if (it < 6)
    n = conf[it][0], n1 = conf[it][1], eta1 = conf[it][2];
  else
    n = 1 + (unsigned)(rand64() % 12), n1 = (unsigned)(rand64() % (n + 1)),
    eta1 = 2 + (unsigned)(rand64() % 2);
  nonce0 = it < 6 ? 0 : (unsigned)(rand64() % (257 - n));
  randfill(sigma, 32);
  memcpy(sigma2, sigma, 32);
  memset(gr, FILL, sizeof(gr));
  mlkem_getnoise((int16_t *)(gr + GUARD), sigma, nonce0, n, n1, eta1,
                 &mlkem_native2_constants);
  for (unsigned i = 0; i < n; i++)
  {
    unsigned eta = i < n1 ? eta1 : 2;
    memcpy(in, sigma, 32);
    in[32] = (uint8_t)(nonce0 + i);
    ref_shake256(buf, 64 * eta, in, 33);
    if (eta == 2)
      ref_poly_cbd2(want + 256 * i, buf);
    else
      ref_poly_cbd3(want + 256 * i, buf);
  }
  bad |= guarded_same("mlkem_getnoise", gr, want, 512 * n, it);
  checks++;
  if (memcmp(sigma, sigma2, 32) != 0)
    printf("FAIL mlkem_getnoise iteration %lu: sigma modified\n", it), bad = 1;
  return bad;
}

/* ------------------------------------------------------------------------- */

static int test_sha3(unsigned long it)
{
  static uint8_t in[2200], copy[2200], go[GUARD + 64 + GUARD];
  uint8_t want[64];
  size_t len = it < 300 ? it : rand64() % 2200;
  int bad = 0;
  if (it % 5 == 1) len = 1184;
  if (it % 5 == 2) len = 33;
  if (it % 5 == 3) len = 64;
  randfill(in, len);
  memcpy(copy, in, len);
  memset(go, FILL, sizeof(go));
  mlkem_hash_h(go + GUARD, in, len, &mlkem_native2_constants);
  ref_sha3_256(want, in, len);
  bad |= guarded_same("mlkem_hash_h", go, want, 32, it);
  memset(go, FILL, sizeof(go));
  mlkem_hash_g(go + GUARD, in, len, &mlkem_native2_constants);
  ref_sha3_512(want, in, len);
  bad |= guarded_same("mlkem_hash_g", go, want, 64, it);
  checks++;
  if (memcmp(in, copy, len) != 0)
    printf("FAIL mlkem_hash iteration %lu: input modified\n", it), bad = 1;
  return bad;
}

int main(int argc, char **argv)
{
  unsigned long n = argc > 1 ? strtoul(argv[1], NULL, 0) : 1000;
  rng = argc > 2 ? strtoull(argv[2], NULL, 0) : 1;
  for (unsigned long it = 0; it < n; it++)
  {
    if (mlkem_gen_matrix && test_gen_matrix(it)) failures++;
    if (mlkem_getnoise && test_getnoise(it)) failures++;
    if (mlkem_hash_h && mlkem_hash_g && test_sha3(it)) failures++;
    if (failures > 10) break;
  }
  printf("%s: mlkem_gen_matrix%s, mlkem_getnoise%s, mlkem_hash_h/g%s %lu "
         "iterations, %lu checks, %lu failures\n",
         failures ? "FAIL" : "OK", mlkem_gen_matrix ? "" : " (absent)",
         mlkem_getnoise ? "" : " (absent)",
         mlkem_hash_h && mlkem_hash_g ? "" : " (absent)", n, checks,
         failures);
  return failures != 0;
}
