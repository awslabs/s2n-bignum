/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/*
 * Differential tests of the ML-KEM API of a candidate library, the
 * functions mlkem{512,768,1024}_{keypair_derand,enc_derand,dec,check_pk,
 * check_sk} and, if present, the randomized keypair and enc, against the
 * reference: mlkem-native's portable C built with the prefix "ref".
 *
 * Each iteration draws fresh random inputs and also exercises the rare
 * paths: implicit rejection (modified and random ciphertexts), invalid
 * public keys (a coefficient >= q) for check_pk and enc_derand, invalid
 * secret keys (wrong H(pk) or embedded pk) for check_sk and dec, and
 * secret vectors with coefficients >= q, which dec must still accept.
 * The first two iterations use all-zero and all-0xff seeds.
 *
 * Every output buffer sits between guard bytes and is pre-filled with a
 * random byte, the same for both libraries; after each call the whole
 * region (guards included) and the return value must agree with the
 * reference, the guards must be intact and the inputs unchanged.
 *
 * The random state of iteration I at level L depends only on the seed, L
 * and I, so "test_api 1 SEED I" repeats a failing iteration.
 *
 * With TEST_API_HEAP set in the environment, the candidate's buffers are
 * heap blocks of the exact sizes instead, for runs under valgrind.
 *
 * usage: test_api [ITERATIONS [SEED [FIRST]]]   (defaults 200, 1, 0)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define Q 3329
#define MAXBYTES 3200
#define GUARD 32

typedef int (*keypair_derand_fn)(uint8_t *, uint8_t *, const uint8_t *);
typedef int (*enc_derand_fn)(uint8_t *, uint8_t *, const uint8_t *,
                             const uint8_t *);
typedef int (*dec_fn)(uint8_t *, const uint8_t *, const uint8_t *);
typedef int (*check_fn)(const uint8_t *);
typedef int (*keypair_fn)(uint8_t *, uint8_t *);
typedef int (*enc_fn)(uint8_t *, uint8_t *, const uint8_t *);

typedef struct
{
  keypair_derand_fn keypair_derand;
  enc_derand_fn enc_derand;
  dec_fn dec;
  check_fn check_pk, check_sk;
  keypair_fn keypair;
  enc_fn enc;
} kem_api;

#define DECLARE(P)                                                       \
  int P##_keypair_derand(uint8_t *, uint8_t *, const uint8_t *);         \
  int P##_enc_derand(uint8_t *, uint8_t *, const uint8_t *,              \
                     const uint8_t *);                                   \
  int P##_dec(uint8_t *, const uint8_t *, const uint8_t *);              \
  int P##_check_pk(const uint8_t *);                                     \
  int P##_check_sk(const uint8_t *);                                     \
  int P##_keypair(uint8_t *, uint8_t *) __attribute__((weak));           \
  int P##_enc(uint8_t *, uint8_t *, const uint8_t *) __attribute__((weak));
#define API(P)                                                   \
  {P##_keypair_derand, P##_enc_derand, P##_dec, P##_check_pk,    \
   P##_check_sk, P##_keypair, P##_enc}

DECLARE(ref512)
DECLARE(ref768)
DECLARE(ref1024)
DECLARE(mlkem512)
DECLARE(mlkem768)
DECLARE(mlkem1024)

typedef struct
{
  unsigned level, k;
  size_t pkb, skb, ctb;
  kem_api ref, cand;
} kem_level;

static const kem_level levels[3] = {
    {512, 2, 800, 1632, 768, API(ref512), API(mlkem512)},
    {768, 3, 1184, 2400, 1088, API(ref768), API(mlkem768)},
    {1024, 4, 1568, 3168, 1568, API(ref1024), API(mlkem1024)}};

/* ------------------------------------------------------------------------- */
/* Random numbers (splitmix64), and randombytes for the randomized API.      */
/* ------------------------------------------------------------------------- */

static uint64_t rng;

static uint64_t rand64(void)
{
  uint64_t z = (rng += 0x9e3779b97f4a7c15ULL);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}

static unsigned randbelow(unsigned n) { return (unsigned)(rand64() % n); }

static void randfill(uint8_t *p, size_t n)
{
  for (size_t i = 0; i < n; i++) p[i] = (uint8_t)rand64();
}

/* randombytes draws from its own stream, reset before each randomized call
   so that the reference and the candidate see the same bytes. */
static uint64_t rb_state;
int randombytes(uint8_t *out, size_t outlen);
int randombytes(uint8_t *out, size_t outlen)
{
  for (size_t i = 0; i < outlen; i++)
  {
    uint64_t z = (rb_state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    out[i] = (uint8_t)((z ^ (z >> 27)) >> 32);
  }
  return 0;
}

/* ------------------------------------------------------------------------- */
/* Guarded output buffers and the comparison of the two libraries.           */
/* ------------------------------------------------------------------------- */

typedef struct
{
  uint8_t b[GUARD + MAXBYTES + GUARD];
  size_t n;
  uint8_t fill;
} obuf;

static void ob_init(obuf *o, size_t n, uint8_t fill)
{
  memset(o->b, fill, sizeof(o->b));
  o->n = n;
  o->fill = fill;
}

static uint8_t *ob(obuf *o) { return o->b + GUARD; }

static unsigned long failures, checks;
static const kem_level *cur;
static unsigned long cur_iter;

static void fail(const char *test, const char *what, long off)
{
  failures++;
  printf("FAIL ML-KEM-%u iteration %lu %s: %s", cur->level, cur_iter, test,
         what);
  if (off >= 0) printf(" at offset %ld", off);
  printf("\n");
  if (failures > 20)
  {
    printf("too many failures\n");
    exit(1);
  }
}

static long first_diff(const uint8_t *a, const uint8_t *b, size_t n)
{
  for (size_t i = 0; i < n; i++)
    if (a[i] != b[i]) return (long)i;
  return -1;
}

/* The reference's and the candidate's outputs, guards included, agree, and
   the candidate's guards are intact. */
static void same_out(const char *test, const char *name, obuf *r, obuf *c)
{
  long d;
  checks++;
  for (size_t i = 0; i < GUARD; i++)
    if (c->b[i] != c->fill || c->b[GUARD + c->n + i] != c->fill)
    {
      fail(test, "guard bytes overwritten", -1);
      return;
    }
  d = first_diff(r->b + GUARD, c->b + GUARD, r->n);
  if (d >= 0)
  {
    char msg[64];
    snprintf(msg, sizeof(msg), "%s differs", name);
    fail(test, msg, d);
  }
}

static void same_ret(const char *test, int r, int c)
{
  checks++;
  if (r != c)
  {
    char msg[64];
    snprintf(msg, sizeof(msg), "return value %d, reference %d", c, r);
    fail(test, msg, -1);
  }
}

static void unchanged(const char *test, const char *name, const uint8_t *p,
                      const uint8_t *copy, size_t n)
{
  long d = first_diff(p, copy, n);
  checks++;
  if (d >= 0)
  {
    char msg[64];
    snprintf(msg, sizeof(msg), "input %s modified", name);
    fail(test, msg, d);
  }
}

/* ------------------------------------------------------------------------- */
/* One differential test per API function. In heap mode (TEST_API_HEAP set) */
/* the candidate's inputs and outputs are heap blocks of the exact sizes, so */
/* that valgrind reports any access beyond them.                             */
/* ------------------------------------------------------------------------- */

static int heap_mode;
static uint8_t copy1[MAXBYTES], copy2[MAXBYTES];

static const uint8_t *in_buf(const uint8_t *p, size_t n)
{
  uint8_t *h;
  if (!heap_mode) return p;
  h = malloc(n);
  memcpy(h, p, n);
  return h;
}

static void in_done(const uint8_t *h, const uint8_t *p)
{
  if (h != p) free((void *)h);
}

static uint8_t *out_buf(obuf *o)
{
  uint8_t *h;
  if (!heap_mode) return ob(o);
  h = malloc(o->n);
  memset(h, o->fill, o->n);
  return h;
}

static void out_done(obuf *o, uint8_t *h)
{
  if (h == ob(o)) return;
  memcpy(ob(o), h, o->n);
  free(h);
}

static void t_keypair_derand(const char *test, const uint8_t coins[64],
                             uint8_t *pk, uint8_t *sk)
{
  obuf rpk, rsk, cpk, csk;
  uint8_t f = (uint8_t)rand64(), *hpk, *hsk;
  const uint8_t *hc;
  int r, c;
  ob_init(&rpk, cur->pkb, f), ob_init(&rsk, cur->skb, f);
  ob_init(&cpk, cur->pkb, f), ob_init(&csk, cur->skb, f);
  memcpy(copy1, coins, 64);
  r = cur->ref.keypair_derand(ob(&rpk), ob(&rsk), coins);
  hc = in_buf(coins, 64), hpk = out_buf(&cpk), hsk = out_buf(&csk);
  c = cur->cand.keypair_derand(hpk, hsk, hc);
  out_done(&cpk, hpk), out_done(&csk, hsk);
  same_ret(test, r, c);
  same_out(test, "pk", &rpk, &cpk);
  same_out(test, "sk", &rsk, &csk);
  unchanged(test, "coins", hc, copy1, 64);
  in_done(hc, coins);
  if (pk) memcpy(pk, ob(&rpk), cur->pkb);
  if (sk) memcpy(sk, ob(&rsk), cur->skb);
}

static int t_enc_derand(const char *test, const uint8_t *pk,
                        const uint8_t coins[32], uint8_t *ct, uint8_t *ss)
{
  obuf rct, rss, cct, css;
  uint8_t f = (uint8_t)rand64(), *hct, *hss;
  const uint8_t *hpk, *hc;
  int r, c;
  ob_init(&rct, cur->ctb, f), ob_init(&rss, 32, f);
  ob_init(&cct, cur->ctb, f), ob_init(&css, 32, f);
  memcpy(copy1, pk, cur->pkb);
  memcpy(copy2, coins, 32);
  r = cur->ref.enc_derand(ob(&rct), ob(&rss), pk, coins);
  hpk = in_buf(pk, cur->pkb), hc = in_buf(coins, 32);
  hct = out_buf(&cct), hss = out_buf(&css);
  c = cur->cand.enc_derand(hct, hss, hpk, hc);
  out_done(&cct, hct), out_done(&css, hss);
  same_ret(test, r, c);
  same_out(test, "ct", &rct, &cct);
  same_out(test, "ss", &rss, &css);
  unchanged(test, "pk", hpk, copy1, cur->pkb);
  unchanged(test, "coins", hc, copy2, 32);
  in_done(hpk, pk), in_done(hc, coins);
  if (ct) memcpy(ct, ob(&rct), cur->ctb);
  if (ss) memcpy(ss, ob(&rss), 32);
  return r;
}

static int t_dec(const char *test, const uint8_t *ct, const uint8_t *sk,
                 uint8_t *ss)
{
  obuf rss, css;
  uint8_t f = (uint8_t)rand64(), *hss;
  const uint8_t *hct, *hsk;
  int r, c;
  ob_init(&rss, 32, f), ob_init(&css, 32, f);
  memcpy(copy1, ct, cur->ctb);
  memcpy(copy2, sk, cur->skb);
  r = cur->ref.dec(ob(&rss), ct, sk);
  hct = in_buf(ct, cur->ctb), hsk = in_buf(sk, cur->skb);
  hss = out_buf(&css);
  c = cur->cand.dec(hss, hct, hsk);
  out_done(&css, hss);
  same_ret(test, r, c);
  same_out(test, "ss", &rss, &css);
  unchanged(test, "ct", hct, copy1, cur->ctb);
  unchanged(test, "sk", hsk, copy2, cur->skb);
  in_done(hct, ct), in_done(hsk, sk);
  if (ss) memcpy(ss, ob(&rss), 32);
  return r;
}

static int t_check(const char *test, int pk_or_sk, const uint8_t *key)
{
  size_t n = pk_or_sk ? cur->skb : cur->pkb;
  const uint8_t *hk;
  int r, c;
  memcpy(copy1, key, n);
  r = (pk_or_sk ? cur->ref.check_sk : cur->ref.check_pk)(key);
  hk = in_buf(key, n);
  c = (pk_or_sk ? cur->cand.check_sk : cur->cand.check_pk)(hk);
  same_ret(test, r, c);
  unchanged(test, pk_or_sk ? "sk" : "pk", hk, copy1, n);
  in_done(hk, key);
  return r;
}

/* The randomized functions, if the candidate has them, with the same
   randombytes stream for both libraries. */
static void t_randomized(const uint8_t *pk)
{
  obuf rpk, rsk, cpk, csk, rct, rss, cct, css;
  uint8_t f = (uint8_t)rand64();
  uint64_t s = rand64();
  int r, c;
  if (!cur->cand.keypair || !cur->cand.enc) return;
  ob_init(&rpk, cur->pkb, f), ob_init(&rsk, cur->skb, f);
  ob_init(&cpk, cur->pkb, f), ob_init(&csk, cur->skb, f);
  rb_state = s, r = cur->ref.keypair(ob(&rpk), ob(&rsk));
  rb_state = s, c = cur->cand.keypair(ob(&cpk), ob(&csk));
  same_ret("keypair", r, c);
  same_out("keypair", "pk", &rpk, &cpk);
  same_out("keypair", "sk", &rsk, &csk);
  ob_init(&rct, cur->ctb, f), ob_init(&rss, 32, f);
  ob_init(&cct, cur->ctb, f), ob_init(&css, 32, f);
  rb_state = s, r = cur->ref.enc(ob(&rct), ob(&rss), pk);
  rb_state = s, c = cur->cand.enc(ob(&cct), ob(&css), pk);
  same_ret("enc", r, c);
  same_out("enc", "ct", &rct, &cct);
  same_out("enc", "ss", &rss, &css);
}

/* ------------------------------------------------------------------------- */
/* Coverage: matrix polynomials that need more than the first three          */
/* SHAKE128 blocks for rejection sampling.                                   */
/* ------------------------------------------------------------------------- */

typedef struct
{
  uint64_t ctx[25];
} shake128ctx;
void ref_shake128_init(shake128ctx *);
void ref_shake128_absorb_once(shake128ctx *, const uint8_t *, size_t);
void ref_shake128_squeezeblocks(uint8_t *, size_t, shake128ctx *);
void ref_shake128_release(shake128ctx *);

static unsigned long extra_block_polys, matrix_polys;

static void count_extra_blocks(const uint8_t rho[32])
{
  uint8_t seed[34], buf[3 * 168];
  for (unsigned i = 0; i < cur->k; i++)
    for (unsigned j = 0; j < cur->k; j++)
    {
      shake128ctx st;
      unsigned n = 0;
      memcpy(seed, rho, 32);
      seed[32] = (uint8_t)i, seed[33] = (uint8_t)j;
      ref_shake128_init(&st);
      ref_shake128_absorb_once(&st, seed, 34);
      ref_shake128_squeezeblocks(buf, 3, &st);
      ref_shake128_release(&st);
      for (unsigned b = 0; b < sizeof(buf); b += 3)
      {
        unsigned d1 = buf[b] | ((buf[b + 1] & 0xf) << 8);
        unsigned d2 = (buf[b + 1] >> 4) | (buf[b + 2] << 4);
        n += (d1 < Q) + (d2 < Q);
      }
      matrix_polys++;
      extra_block_polys += (n < 256);
    }
}

/* ------------------------------------------------------------------------- */
/* Encoded keys: set one 12-bit coefficient of an encoded polynomial vector. */
/* ------------------------------------------------------------------------- */

static void set_coeff(uint8_t *p, unsigned c, unsigned v)
{
  uint8_t *b = p + 3 * (c / 2);
  if (c % 2 == 0)
  {
    b[0] = (uint8_t)v;
    b[1] = (uint8_t)((b[1] & 0xf0) | (v >> 8));
  }
  else
  {
    b[1] = (uint8_t)((b[1] & 0x0f) | ((v & 0xf) << 4));
    b[2] = (uint8_t)(v >> 4);
  }
}

/* ------------------------------------------------------------------------- */
/* One iteration at one level.                                               */
/* ------------------------------------------------------------------------- */

static void iteration(uint64_t seed, unsigned long it)
{
  static uint8_t pk[MAXBYTES], sk[MAXBYTES], ct[MAXBYTES], ct2[MAXBYTES];
  static uint8_t pk2[MAXBYTES], sk2[MAXBYTES];
  uint8_t coins[64], m[32], ss[32], ss2[32];
  size_t vb = 384 * cur->k; /* bytes of an encoded polynomial vector */
  unsigned ncoeffs = 256 * cur->k;

  rng = seed ^ ((uint64_t)cur->level << 40) ^ it;
  rand64();
  cur_iter = it;

  /* Keys and a ciphertext from random (or all-0, all-0xff) coins */
  if (it < 2)
    memset(coins, it ? 0xff : 0, 64), memset(m, it ? 0xff : 0, 32);
  else
    randfill(coins, 64), randfill(m, 32);
  t_keypair_derand("keypair_derand", coins, pk, sk);
  count_extra_blocks(pk + vb);
  if (t_check("check_pk", 0, pk) != 0) fail("check_pk", "valid pk", -1);
  if (t_check("check_sk", 1, sk) != 0) fail("check_sk", "valid sk", -1);
  t_enc_derand("enc_derand", pk, m, ct, ss);
  t_dec("dec", ct, sk, ss2);
  checks++;
  if (memcmp(ss, ss2, 32) != 0) fail("dec", "shared secrets differ", -1);

  /* Implicit rejection: one flipped bit, a changed last byte (in the
     compressed v), and a random ciphertext */
  memcpy(ct2, ct, cur->ctb);
  ct2[randbelow((unsigned)cur->ctb)] ^= (uint8_t)(1 << randbelow(8));
  t_dec("dec(bit flipped)", ct2, sk, NULL);
  memcpy(ct2, ct, cur->ctb);
  ct2[cur->ctb - 1] ^= (uint8_t)(1 + randbelow(255));
  t_dec("dec(v changed)", ct2, sk, NULL);
  randfill(ct2, cur->ctb);
  t_dec("dec(random ct)", ct2, sk, NULL);

  /* Public keys: a coefficient >= q (invalid), = q - 1 (valid), random
     bytes (almost always invalid) and a different rho (valid) */
  memcpy(pk2, pk, cur->pkb);
  set_coeff(pk2, randbelow(ncoeffs), Q + randbelow(4096 - Q));
  if (t_check("check_pk(coeff >= q)", 0, pk2) == 0)
    fail("check_pk(coeff >= q)", "invalid pk accepted", -1);
  t_enc_derand("enc_derand(coeff >= q)", pk2, m, NULL, NULL);
  memcpy(pk2, pk, cur->pkb);
  set_coeff(pk2, randbelow(ncoeffs), Q - 1);
  t_check("check_pk(coeff q-1)", 0, pk2);
  t_enc_derand("enc_derand(coeff q-1)", pk2, m, NULL, NULL);
  randfill(pk2, cur->pkb);
  t_check("check_pk(random)", 0, pk2);
  t_enc_derand("enc_derand(random pk)", pk2, m, NULL, NULL);
  memcpy(pk2, pk, cur->pkb);
  randfill(pk2 + vb, 32);
  t_check("check_pk(new rho)", 0, pk2);
  t_enc_derand("enc_derand(new rho)", pk2, m, NULL, NULL);
  if (it == 0)
  {
    for (unsigned c = 0; c < ncoeffs; c++) set_coeff(pk2, c, Q - 1);
    t_check("check_pk(all q-1)", 0, pk2);
    t_enc_derand("enc_derand(all q-1)", pk2, m, NULL, NULL);
    for (unsigned c = 0; c < ncoeffs; c++) set_coeff(pk2, c, Q);
    t_check("check_pk(all q)", 0, pk2);
    t_enc_derand("enc_derand(all q)", pk2, m, NULL, NULL);
  }

  /* Secret keys: a wrong H(pk) or embedded pk (invalid), and a random
     secret vector or z (valid, whatever the coefficients) */
  memcpy(sk2, sk, cur->skb);
  sk2[cur->skb - 64 + randbelow(32)] ^= (uint8_t)(1 << randbelow(8));
  if (t_check("check_sk(bad h)", 1, sk2) == 0)
    fail("check_sk(bad h)", "invalid sk accepted", -1);
  t_dec("dec(bad h)", ct, sk2, NULL);
  memcpy(sk2, sk, cur->skb);
  sk2[vb + randbelow((unsigned)cur->pkb)] ^= (uint8_t)(1 << randbelow(8));
  if (t_check("check_sk(bad pk)", 1, sk2) == 0)
    fail("check_sk(bad pk)", "invalid sk accepted", -1);
  t_dec("dec(bad pk)", ct, sk2, NULL);
  memcpy(sk2, sk, cur->skb);
  randfill(sk2, vb);
  t_check("check_sk(random s)", 1, sk2);
  t_dec("dec(random s)", ct, sk2, NULL);
  t_dec("dec(random s, random ct)", ct2, sk2, NULL);
  memcpy(sk2, sk, cur->skb);
  randfill(sk2 + cur->skb - 32, 32);
  t_dec("dec(random z, random ct)", ct2, sk2, NULL);

  t_randomized(pk);
}

int main(int argc, char **argv)
{
  unsigned long n = argc > 1 ? strtoul(argv[1], NULL, 0) : 200;
  uint64_t seed = argc > 2 ? strtoull(argv[2], NULL, 0) : 1;
  unsigned long first = argc > 3 ? strtoul(argv[3], NULL, 0) : 0;
  heap_mode = getenv("TEST_API_HEAP") != NULL;
  for (int l = 0; l < 3; l++)
  {
    cur = &levels[l];
    extra_block_polys = matrix_polys = 0;
    for (unsigned long it = first; it < first + n; it++) iteration(seed, it);
    printf("ML-KEM-%u: iterations %lu-%lu, %lu of %lu matrix polynomials "
           "needed a 4th block\n",
           cur->level, first, first + n - 1, extra_block_polys,
           matrix_polys);
  }
  printf("%s: %lu checks, %lu failures%s\n", failures ? "FAIL" : "OK", checks,
         failures,
         levels[0].cand.keypair ? "" : " (no randomized API in candidate)");
  return failures != 0;
}
