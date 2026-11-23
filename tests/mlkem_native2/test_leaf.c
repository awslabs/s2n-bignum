/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/*
 * Tests of the new asm leaf functions (arm/mlkem, or x86/mlkem on x86_64)
 * against the reference: mlkem-native's portable C built with the prefix
 * "ref". Where
 * the input space allows, each coefficient or byte position sees every
 * possible value; otherwise inputs are random. Outputs sit between guard
 * bytes, which must survive, and inputs must be unchanged.
 *
 * On x86_64 the compress and decompress kernels are mlkem-native's,
 * mlkem_compress_d4_x86 and so on, which take their tables from the
 * constants block; they are called through adapters with the arm
 * signatures. mlkem_frombytes and mlkem_tobytes there include the
 * permutation into the custom NTT order of the x86 backend, so they are
 * checked against the reference composed with mlkem_unpack, which is
 * checked to be that permutation, a fixed reordering of 256 entries.
 * The rejection sampler is also run with its buffer and output next to
 * pages without access, which must not be touched. The Keccak-f1600
 * permutations on one state (sha3_keccak_f1600 and, on x86_64, its _alt,
 * _alt2 and _avx512 versions, whichever are linked) are checked against
 * the reference permutation.
 *
 * Functions missing from the link (weak symbols) are skipped.
 *
 * usage: test_leaf [RANDOM_TESTS [NAME]]   (default 10000, all)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#define Q 3329
#define WEAK __attribute__((weak))

typedef struct
{
  int16_t coeffs[256];
} __attribute__((aligned(32))) poly;

/* The reference */
void ref_poly_cbd2(poly *r, const uint8_t buf[128]);
void ref_poly_cbd3(poly *r, const uint8_t buf[192]);

void ref_poly_compress_d4(uint8_t *r, const poly *a);
void ref_poly_compress_d5(uint8_t *r, const poly *a);
void ref_poly_compress_d10(uint8_t *r, const poly *a);
void ref_poly_compress_d11(uint8_t *r, const poly *a);
void ref_poly_decompress_d4(poly *r, const uint8_t *a);
void ref_poly_decompress_d5(poly *r, const uint8_t *a);
void ref_poly_decompress_d10(poly *r, const uint8_t *a);
void ref_poly_decompress_d11(poly *r, const uint8_t *a);

void ref_poly_frommsg(poly *r, const uint8_t msg[32]);
void ref_poly_tomsg(uint8_t msg[32], const poly *a);

void ref_poly_frombytes(poly *r, const uint8_t a[384]);
void ref_poly_tobytes(uint8_t r[384], const poly *a);
void ref_poly_add(poly *r, const poly *b);
void ref_poly_sub(poly *r, const poly *b);
void ref_poly_reduce(poly *r);

/* The candidates */
void mlkem_cbd2(int16_t r[256], const uint8_t buf[128]) WEAK;
void mlkem_cbd3(int16_t r[256], const uint8_t buf[192]) WEAK;
void mlkem_frommsg(int16_t r[256], const uint8_t msg[32]) WEAK;
void mlkem_frombytes(int16_t r[256], const uint8_t a[384]) WEAK;
uint64_t mlkem_check_encoding(const uint8_t *a, uint64_t k) WEAK;
void mlkem_add_reduce(int16_t r[256], const int16_t a[256]) WEAK;
uint64_t mlkem_rej_uniform_VARIABLE_TIME(int16_t r[256], const uint8_t *buf,
                                         uint64_t buflen,
                                         const uint8_t *table) WEAK;
uint64_t mlkem_rej_uniform_alt_VARIABLE_TIME(int16_t r[256], uint64_t n,
                                             const uint8_t *buf,
                                             uint64_t buflen,
                                             const uint8_t *table) WEAK;
extern const uint8_t ref_rej_uniform_table[4096] WEAK;
void mlkem_sub_reduce(int16_t r[256], const int16_t a[256]) WEAK;
void ref_keccakf1600_permute(uint64_t s[25]);
void sha3_keccak_f1600(uint64_t a[25], const uint64_t rc[24]) WEAK;
#if defined(__x86_64__)
void sha3_keccak_f1600_alt2(uint64_t a[25], const uint64_t rc[24]) WEAK;
void sha3_keccak_f1600_avx512(uint64_t a[25], const uint64_t rc[24]) WEAK;
#endif
void mlkem_tomsg(uint8_t msg[32], const int16_t a[256]) WEAK;
void mlkem_compress_d4(uint8_t r[128], const int16_t a[256]) WEAK;
void mlkem_compress_d5(uint8_t r[160], const int16_t a[256]) WEAK;
void mlkem_compress_d10(uint8_t r[320], const int16_t a[256]) WEAK;
void mlkem_compress_d11(uint8_t r[352], const int16_t a[256]) WEAK;
void mlkem_decompress_d4(int16_t r[256], const uint8_t a[128]) WEAK;
void mlkem_decompress_d5(int16_t r[256], const uint8_t a[160]) WEAK;
void mlkem_decompress_d10(int16_t r[256], const uint8_t a[320]) WEAK;
void mlkem_decompress_d11(int16_t r[256], const uint8_t a[352]) WEAK;
void mlkem_tobytes(uint8_t r[384], const int16_t a[256]) WEAK;
void mlkem_unpack(int16_t a[256]) WEAK;

#include "mlkem_native2_consts.h"

#if defined(__x86_64__)
#define X86_CODEC(d, ct, dt)                                                \
  void mlkem_compress_d##d##_x86(uint8_t *r, const int16_t *a,              \
                                 const uint8_t data[ct]) WEAK;              \
  void mlkem_decompress_d##d##_x86(int16_t *r, const uint8_t *a,            \
                                   const uint8_t data[dt]) WEAK;            \
  static void x86_compress_d##d(uint8_t *r, const int16_t *a)               \
  {                                                                         \
    mlkem_compress_d##d##_x86(r, a,                                         \
                              mlkem_native2_constants.compress_d##d##_data); \
  }                                                                         \
  static void x86_decompress_d##d(int16_t *r, const uint8_t *a)             \
  {                                                                         \
    mlkem_decompress_d##d##_x86(                                            \
        r, a, mlkem_native2_constants.decompress_d##d##_data);              \
  }
X86_CODEC(4, 32, 32)
X86_CODEC(5, 32, 96)
X86_CODEC(10, 32, 32)
X86_CODEC(11, 64, 128)
/* The candidate for test_compress_dN: the adapter, if the kernel exists */
#define COMPRESS_FN(d) \
  (mlkem_compress_d##d##_x86 ? x86_compress_d##d : NULL)
#define DECOMPRESS_FN(d) \
  (mlkem_decompress_d##d##_x86 ? x86_decompress_d##d : NULL)
#else
#define COMPRESS_FN(d) mlkem_compress_d##d
#define DECOMPRESS_FN(d) mlkem_decompress_d##d
#endif

/* ------------------------------------------------------------------------- */

static uint64_t rng = 1;
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

static unsigned long ntests = 10000, failures, checks;

#define GUARD 64
#define FILL 0xa5
/* An output area with guards; out() is where the function writes. */
typedef struct
{
  uint8_t b[GUARD + 4096 + GUARD];
} __attribute__((aligned(64))) area;
static void *out(area *a)
{
  memset(a->b, FILL, sizeof(a->b));
  return a->b + GUARD;
}

/* Compare n bytes of candidate output with the reference, and check the
   guards around the candidate's n bytes. */
static int compare(const char *name, area *cand, const void *want, size_t n,
                   unsigned long test)
{
  const uint8_t *c = cand->b + GUARD;
  checks++;
  for (size_t i = 0; i < GUARD; i++)
    if (cand->b[i] != FILL || c[n + i] != FILL)
    {
      printf("FAIL %s test %lu: guard bytes overwritten\n", name, test);
      return 1;
    }
  for (size_t i = 0; i < n; i++)
    if (c[i] != ((const uint8_t *)want)[i])
    {
      printf("FAIL %s test %lu: byte %zu is 0x%02x, reference 0x%02x\n", name,
             test, i, c[i], ((const uint8_t *)want)[i]);
      return 1;
    }
  return 0;
}

static int same_input(const char *name, const void *p, const void *copy,
                      size_t n, unsigned long test)
{
  checks++;
  if (memcmp(p, copy, n) != 0)
  {
    printf("FAIL %s test %lu: input modified\n", name, test);
    return 1;
  }
  return 0;
}

/* ------------------------------------------------------------------------- */
/* CBD: bytes to coefficients. Tests 0..255 give every position every byte  */
/* value; the rest are random.                                              */
/* ------------------------------------------------------------------------- */

static void cbd_input(uint8_t *buf, size_t n, unsigned long t)
{
  if (t < 256)
    for (size_t i = 0; i < n; i++) buf[i] = (uint8_t)(t + 97 * i);
  else
    randfill(buf, n);
}

static int test_cbd2(void)
{
  uint8_t buf[128], copy[128];
  poly want;
  area a;
  for (unsigned long t = 0; t < 256 + ntests; t++)
  {
    cbd_input(buf, sizeof(buf), t);
    memcpy(copy, buf, sizeof(buf));
    ref_poly_cbd2(&want, buf);
    mlkem_cbd2(out(&a), buf);
    if (compare("mlkem_cbd2", &a, &want, 512, t) ||
        same_input("mlkem_cbd2", buf, copy, sizeof(buf), t))
      return 1;
  }
  return 0;
}

static int test_cbd3(void)
{
  uint8_t buf[192], copy[192];
  poly want;
  area a;
  for (unsigned long t = 0; t < 256 + ntests; t++)
  {
    cbd_input(buf, sizeof(buf), t);
    memcpy(copy, buf, sizeof(buf));
    ref_poly_cbd3(&want, buf);
    mlkem_cbd3(out(&a), buf);
    if (compare("mlkem_cbd3", &a, &want, 512, t) ||
        same_input("mlkem_cbd3", buf, copy, sizeof(buf), t))
      return 1;
  }
  return 0;
}

/* ------------------------------------------------------------------------- */
/* Compression: coefficients 0..q-1 to d-bit fields. Tests 0..q-1 give every */
/* position every value; the rest are random.                               */
/* ------------------------------------------------------------------------- */

static void canonical_input(poly *p, unsigned long t)
{
  for (int i = 0; i < 256; i++)
    p->coeffs[i] = (int16_t)(t < Q ? (t + 97 * (unsigned long)i) % Q
                                   : rand64() % Q);
}

static int test_compress(const char *name, unsigned d,
                         void (*cand)(uint8_t *, const int16_t *),
                         void (*ref)(uint8_t *, const poly *))
{
  uint8_t want[352];
  poly a, copy;
  area o;
  for (unsigned long t = 0; t < Q + ntests; t++)
  {
    canonical_input(&a, t);
    copy = a;
    ref(want, &a);
    cand(out(&o), a.coeffs);
    if (compare(name, &o, want, 32 * d, t) ||
        same_input(name, &a, &copy, sizeof(a), t))
      return 1;
  }
  return 0;
}

/* Decompression: d-bit fields to coefficients. Tests 0..2^d-1 give every */
/* field every value; the rest are random bytes.                         */

static void set_field(uint8_t *b, unsigned d, unsigned i, unsigned v)
{
  for (unsigned k = 0; k < d; k++)
  {
    unsigned bit = d * i + k;
    b[bit / 8] = (uint8_t)((b[bit / 8] & ~(1u << (bit % 8))) |
                           (((v >> k) & 1) << (bit % 8)));
  }
}

static int test_decompress(const char *name, unsigned d,
                           void (*cand)(int16_t *, const uint8_t *),
                           void (*ref)(poly *, const uint8_t *))
{
  uint8_t in[352], copy[352];
  poly want;
  area o;
  for (unsigned long t = 0; t < (1u << d) + ntests; t++)
  {
    if (t < (1u << d))
      for (unsigned i = 0; i < 256; i++)
        set_field(in, d, i, (unsigned)(t + 97 * i) & ((1u << d) - 1));
    else
      randfill(in, 32 * d);
    memcpy(copy, in, 32 * d);
    ref(&want, in);
    cand(out(&o), in);
    if (compare(name, &o, &want, 512, t) ||
        same_input(name, in, copy, 32 * d, t))
      return 1;
  }
  return 0;
}

#define COMPRESS_TEST(d)                                                  \
  static int test_compress_d##d(void)                                     \
  {                                                                       \
    return test_compress("mlkem_compress_d" #d, d, COMPRESS_FN(d),        \
                         ref_poly_compress_d##d);                         \
  }                                                                       \
  static int test_decompress_d##d(void)                                   \
  {                                                                       \
    return test_decompress("mlkem_decompress_d" #d, d, DECOMPRESS_FN(d),  \
                           ref_poly_decompress_d##d);                     \
  }
COMPRESS_TEST(4)
COMPRESS_TEST(5)
COMPRESS_TEST(10)
COMPRESS_TEST(11)

/* ------------------------------------------------------------------------- */
/* 12-bit encodings                                                          */
/* ------------------------------------------------------------------------- */

#if !defined(__x86_64__)
static int test_frombytes(void)
{
  uint8_t in[384], copy[384];
  poly want;
  area o;
  for (unsigned long t = 0; t < 4096 + ntests; t++)
  {
    if (t < 4096)
      for (unsigned i = 0; i < 256; i++)
        set_field(in, 12, i, (unsigned)(t + 97 * i) & 4095);
    else
      randfill(in, 384);
    memcpy(copy, in, 384);
    ref_poly_frombytes(&want, in);
    mlkem_frombytes(out(&o), in);
    if (compare("mlkem_frombytes", &o, &want, 512, t) ||
        same_input("mlkem_frombytes", in, copy, 384, t))
      return 1;
  }
  return 0;
}
#endif

/* The encoding check, against a direct model, for k = 0..4: valid
   encodings of random reduced coefficients, then one field changed to a
   value from q - 1 to 4095 (q - 1 and q among them each time), all
   fields 4095, and random bytes. */
static int test_check_encoding(void)
{
  static uint8_t in[4 * 384 + 64], copy[sizeof(in)];
  for (unsigned long t = 0; t < 4 * ntests + 64; t++)
  {
    uint64_t k = t % 5, want = 1, got;
    unsigned n = 256 * (unsigned)k, v;
    randfill(in, sizeof(in));
    for (unsigned i = 0; i < n; i++) set_field(in, 12, i, rand64() % Q);
    if (n && t % 4 != 0)
    {
      unsigned pos = (unsigned)(rand64() % n);
      v = t % 4 == 1   ? Q - 1
          : t % 4 == 2 ? Q
                       : Q + (unsigned)(rand64() % (4096 - Q));
      if (t % 64 == 3) v = 4095;
      set_field(in, 12, pos, v);
      want = v < Q;
    }
    if (n && t % 97 == 5)
    {
      randfill(in, 384 * k);
      want = 1;
      for (unsigned i = 0; i < n; i++)
      {
        unsigned b = 12 * i, f = (in[b / 8] | in[b / 8 + 1] << 8) >> (b % 8);
        if ((f & 4095) >= Q) want = 0;
      }
    }
    memcpy(copy, in, sizeof(in));
    got = mlkem_check_encoding(in, k);
    checks++;
    if (got != want)
    {
      printf("FAIL mlkem_check_encoding test %lu (k = %lu): %lu, want %lu\n",
             t, (unsigned long)k, (unsigned long)got, (unsigned long)want);
      return 1;
    }
    if (same_input("mlkem_check_encoding", in, copy, sizeof(in), t)) return 1;
  }
  return 0;
}

/* ------------------------------------------------------------------------- */
/* Add or subtract and reduce, for inputs whose sum or difference is less    */
/* than 2^15 in magnitude: every sum or difference z (-32767..32767), as     */
/* (z, 0), (0, +/-z) and halves; then random, extreme and boundary values.   */
/* ------------------------------------------------------------------------- */

static int16_t edge_value(unsigned long t, unsigned i)
{
  static const int16_t e[] = {0, 1, -1, 3328, -3328, 3329, -3329, 6658,
                              -6658, 16383, -16384, 16384, -16383, 32767 / 2,
                              -32767 / 2, 26632, -26632};
  unsigned n = sizeof(e) / sizeof(e[0]);
  return e[(t + i) % n];
}

static int test_addsub(int sub)
{
  const char *name = sub ? "mlkem_sub_reduce" : "mlkem_add_reduce";
  poly r, a, copy, want;
  area o;
  for (unsigned long t = 0; t < 3 * 256 + 20 + ntests; t++)
  {
    for (int i = 0; i < 256; i++)
    {
      int x, y, z;
      if (t < 3 * 256)
      {
        int w = -32767 + (int)(256 * (t % 256)) + i, d = (int)(t / 256);
        if (w > 32767) w = 32767;
        x = d == 0 ? w : d == 1 ? 0 : w / 2;
        y = sub ? x - w : w - x; /* x + y = w, or x - y = w */
      }
      else if (t < 3 * 256 + 20)
        x = edge_value(t, (unsigned)i), y = edge_value(t * 7 + 3, (unsigned)i);
      else if (t % 3 == 0)
        x = (int)(rand64() % 32768) - 16384,
        y = (int)(rand64() % 32768) - 16384;
      else
        x = (int)(rand64() % 65536) - 32768,
        y = (int)(rand64() % 65536) - 32768;
      z = sub ? x - y : x + y;
      if (z > 32767 || z < -32767) y = 0; /* keep within the precondition */
      r.coeffs[i] = (int16_t)x, a.coeffs[i] = (int16_t)y;
    }
    copy = a;
    want = r;
    if (sub)
      ref_poly_sub(&want, &a);
    else
      ref_poly_add(&want, &a);
    ref_poly_reduce(&want);
    memcpy(out(&o), &r, 512);
    (sub ? mlkem_sub_reduce : mlkem_add_reduce)((int16_t *)(o.b + GUARD),
                                                a.coeffs);
    if (compare(name, &o, &want, 512, t) ||
        same_input(name, &a, &copy, sizeof(a), t))
      return 1;
  }
  return 0;
}
static int test_add_reduce(void) { return test_addsub(0); }
static int test_sub_reduce(void) { return test_addsub(1); }

/* ------------------------------------------------------------------------- */
/* Rejection sampling: the alt version against the direct definition, on   */
/* random buffers with a varying proportion of rejected fields; then with   */
/* the buffer starting just after, or ending just before, a page without    */
/* access, and r ending just before one.                                    */
/* ------------------------------------------------------------------------- */

typedef uint64_t (*rej_fn)(int16_t r[256], uint64_t n, const uint8_t *buf,
                           uint64_t buflen);
static uint64_t rej_with_table(int16_t r[256], uint64_t n, const uint8_t *buf,
                               uint64_t buflen)
{
  return mlkem_rej_uniform_alt_VARIABLE_TIME(
      r, n, buf, buflen, mlkem_native2_constants.rej_uniform_table);
}

/* The entries from n0 entries in want[] and len bytes of buf; returns n */
static uint64_t rej_want(int16_t want[256], uint64_t n0, const uint8_t *buf,
                         uint64_t len)
{
  uint64_t n = n0;
  for (uint64_t i = 0; i + 3 <= len && n < 256; i += 3)
  {
    unsigned d1 = buf[i] | ((buf[i + 1] & 0xf) << 8);
    unsigned d2 = (buf[i + 1] >> 4) | (buf[i + 2] << 4);
    if (d1 < Q) want[n++] = (int16_t)d1;
    if (d2 < Q && n < 256) want[n++] = (int16_t)d2;
  }
  return n;
}

static int rej_count(const char *name, unsigned long t, uint64_t got,
                     uint64_t n)
{
  checks++;
  if (got == n) return 0;
  printf("FAIL %s test %lu: count %lu, want %lu\n", name, t,
         (unsigned long)got, (unsigned long)n);
  return 1;
}

static int test_rej_with(const char *name, rej_fn f)
{
  static uint8_t buf[24 * 40], copy[sizeof(buf)];
  int16_t want[256];
  area o;
  long page = sysconf(_SC_PAGESIZE);
  uint8_t *pages;
  int bad = 0;
  for (unsigned long t = 0; t < 30 * 40 + ntests; t++)
  {
    uint64_t len = 24 * (t % 41), n, n0, got;
    unsigned bias = (unsigned)(t / 41) % 30; /* bytes forced to 0xff */
    int16_t *r;
    randfill(buf, sizeof(buf));
    for (size_t i = 0; i < sizeof(buf); i++)
      if (rand64() % 30 < bias) buf[i] = 0xff;
    memcpy(copy, buf, sizeof(buf));
    /* Start from n0 entries already present: 0 mostly, else random */
    n0 = t % 3 == 0 ? rand64() % 257 : 0;
    r = (int16_t *)out(&o);
    for (uint64_t i = 0; i < n0; i++) want[i] = r[i] = (int16_t)(rand64() % Q);
    n = rej_want(want, n0, buf, len);
    got = f(r, n0, buf, len);
    if (rej_count(name, t, got, n)) return 1;
    /* r[n..255] may be written too, but nothing beyond r */
    for (size_t i = 0; i < GUARD; i++)
      if (o.b[i] != FILL || o.b[GUARD + 512 + i] != FILL)
      {
        printf("FAIL %s test %lu: wrote outside r\n", name, t);
        return 1;
      }
    memset(o.b + GUARD + 2 * n, FILL, 512 - 2 * n);
    if (compare(name, &o, want, 2 * n, t) ||
        same_input(name, buf, copy, sizeof(buf), t))
      return 1;
  }
  /* Pages: none, buf (page 1), none, r (page 3), none */
  pages = mmap(NULL, 5 * page, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (pages == MAP_FAILED ||
      mprotect(pages + page, page, PROT_READ | PROT_WRITE) != 0 ||
      mprotect(pages + 3 * page, page, PROT_READ | PROT_WRITE) != 0)
  {
    printf("FAIL %s: cannot map the pages\n", name);
    return 1;
  }
  for (unsigned long t = 0; t < 2 * 41 * 4; t++)
  {
    uint64_t len = 24 * (t % 41), n0 = (t / 82) * 80, n, got;
    uint8_t *b = pages + page + (t / 41 % 2 ? page - len : 0);
    int16_t *r = (int16_t *)(pages + 4 * page - 512);
    randfill(b, len);
    memcpy(copy, b, len);
    for (uint64_t i = 0; i < n0; i++) want[i] = r[i] = (int16_t)(rand64() % Q);
    n = rej_want(want, n0, b, len);
    got = f(r, n0, b, len);
    if ((bad = rej_count(name, t, got, n)) != 0) break;
    checks++;
    if (memcmp(r, want, 2 * n) != 0 || memcmp(b, copy, len) != 0)
    {
      printf("FAIL %s test %lu: wrong entries or input modified\n", name, t);
      bad = 1;
      break;
    }
  }
  munmap(pages, 5 * page);
  return bad;
}

static int test_rej_uniform_alt(void)
{
  return test_rej_with("mlkem_rej_uniform_alt", rej_with_table);
}

/* ------------------------------------------------------------------------- */
/* Keccak-f1600 on one state against the reference permutation: random     */
/* states, and the states of all zeros and all ones.                         */
/* ------------------------------------------------------------------------- */

static const uint64_t keccak_rc[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL,
    0x8000000080008000ULL, 0x000000000000808bULL, 0x0000000080000001ULL,
    0x8000000080008081ULL, 0x8000000000008009ULL, 0x000000000000008aULL,
    0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL,
    0x8000000000008003ULL, 0x8000000000008002ULL, 0x8000000000000080ULL,
    0x000000000000800aULL, 0x800000008000000aULL, 0x8000000080008081ULL,
    0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL};

static int test_keccak_with(const char *name,
                            void (*f)(uint64_t[25], const uint64_t[24]))
{
  uint64_t a[25], want[25], rc[24];
  memcpy(rc, keccak_rc, sizeof(rc));
  for (unsigned long t = 0; t < 2 + ntests; t++)
  {
    for (int i = 0; i < 25; i++)
      a[i] = t == 0 ? 0 : t == 1 ? ~(uint64_t)0 : rand64();
    memcpy(want, a, sizeof(a));
    ref_keccakf1600_permute(want);
    f(a, rc);
    checks++;
    if (memcmp(a, want, sizeof(a)) != 0)
    {
      printf("FAIL %s test %lu: state differs from the reference\n", name, t);
      return 1;
    }
    if (memcmp(rc, keccak_rc, sizeof(rc)) != 0)
    {
      printf("FAIL %s test %lu: round constants modified\n", name, t);
      return 1;
    }
  }
  return 0;
}
static int test_keccak(void)
{
  return test_keccak_with("sha3_keccak_f1600", sha3_keccak_f1600);
}
#if defined(__x86_64__)
static int test_keccak_alt2(void)
{
  return test_keccak_with("sha3_keccak_f1600_alt2", sha3_keccak_f1600_alt2);
}
static int test_keccak_avx512(void)
{
  return test_keccak_with("sha3_keccak_f1600_avx512",
                          sha3_keccak_f1600_avx512);
}
#endif

#if defined(__x86_64__)
/* ------------------------------------------------------------------------- */
/* x86_64: the custom NTT order. mlkem_unpack must be a fixed reordering:    */
/* the permutation is read off from an input with distinct entries, then    */
/* checked on random inputs; then frombytes = unpack o ref frombytes, and   */
/* tobytes o unpack = ref tobytes on reduced coefficients.                  */
/* ------------------------------------------------------------------------- */

static int perm_known, perm[256];

static int test_unpack(void)
{
  poly a, b;
  int seen[256] = {0};
  for (int i = 0; i < 256; i++) a.coeffs[i] = (int16_t)i;
  mlkem_unpack(a.coeffs);
  checks++;
  for (int i = 0; i < 256; i++)
  {
    int v = a.coeffs[i];
    if (v < 0 || v > 255 || seen[v]++)
    {
      printf("FAIL mlkem_unpack: not a permutation\n");
      return 1;
    }
    perm[i] = v;
  }
  perm_known = 1;
  for (unsigned long t = 0; t < ntests; t++)
  {
    randfill(&a, sizeof(a));
    b = a;
    mlkem_unpack(b.coeffs);
    checks++;
    for (int i = 0; i < 256; i++)
      if (b.coeffs[i] != a.coeffs[perm[i]])
      {
        printf("FAIL mlkem_unpack test %lu: entry %d\n", t, i);
        return 1;
      }
  }
  return 0;
}

static void apply_unpack(poly *p)
{
  poly q = *p;
  for (int i = 0; i < 256; i++) p->coeffs[i] = q.coeffs[perm[i]];
}

static int test_frombytes_custom(void)
{
  uint8_t in[384], copy[384];
  poly want;
  area o;
  if (!perm_known && (!mlkem_unpack || test_unpack())) return 1;
  for (unsigned long t = 0; t < 4096 + ntests; t++)
  {
    if (t < 4096)
      for (unsigned i = 0; i < 256; i++)
        set_field(in, 12, i, (unsigned)(t + 97 * i) & 4095);
    else
      randfill(in, 384);
    memcpy(copy, in, 384);
    ref_poly_frombytes(&want, in);
    apply_unpack(&want);
    mlkem_frombytes(out(&o), in);
    if (compare("mlkem_frombytes", &o, &want, 512, t) ||
        same_input("mlkem_frombytes", in, copy, 384, t))
      return 1;
  }
  return 0;
}

static int test_tobytes_custom(void)
{
  uint8_t want[384];
  poly a, copy;
  area o;
  if (!perm_known && (!mlkem_unpack || test_unpack())) return 1;
  for (unsigned long t = 0; t < Q + ntests; t++)
  {
    canonical_input(&a, t);
    ref_poly_tobytes(want, &a);
    apply_unpack(&a);
    copy = a;
    mlkem_tobytes(out(&o), a.coeffs);
    if (compare("mlkem_tobytes", &o, want, 384, t) ||
        same_input("mlkem_tobytes", &a, &copy, sizeof(a), t))
      return 1;
  }
  return 0;
}
#endif

/* ------------------------------------------------------------------------- */
/* Messages                                                                  */
/* ------------------------------------------------------------------------- */

static int test_frommsg(void)
{
  uint8_t m[32], copy[32];
  poly want;
  area o;
  for (unsigned long t = 0; t < 256 + ntests; t++)
  {
    cbd_input(m, 32, t);
    memcpy(copy, m, 32);
    ref_poly_frommsg(&want, m);
    mlkem_frommsg(out(&o), m);
    if (compare("mlkem_frommsg", &o, &want, 512, t) ||
        same_input("mlkem_frommsg", m, copy, 32, t))
      return 1;
  }
  return 0;
}

static int test_tomsg(void)
{
  uint8_t want[32];
  poly a, copy;
  area o;
  for (unsigned long t = 0; t < Q + ntests; t++)
  {
    canonical_input(&a, t);
    copy = a;
    ref_poly_tomsg(want, &a);
    mlkem_tomsg(out(&o), a.coeffs);
    if (compare("mlkem_tomsg", &o, want, 32, t) ||
        same_input("mlkem_tomsg", &a, &copy, sizeof(a), t))
      return 1;
  }
  return 0;
}

/* ------------------------------------------------------------------------- */

typedef struct
{
  const char *name;
  void *fn;
  int (*test)(void);
} leaf;

#define LEAF(f) {#f, (void *)(f), test_##f}
#define LEAF2(f, t) {#f, (void *)(f), t}
#if defined(__x86_64__)
#define CODEC(d)                                                          \
  {"mlkem_compress_d" #d "_x86", (void *)mlkem_compress_d##d##_x86,       \
   test_compress_d##d},                                                   \
  {"mlkem_decompress_d" #d "_x86", (void *)mlkem_decompress_d##d##_x86,   \
   test_decompress_d##d}
#else
#define CODEC(d)                                                          \
  LEAF2(mlkem_compress_d##d, test_compress_d##d),                         \
  LEAF2(mlkem_decompress_d##d, test_decompress_d##d)
#endif

int main(int argc, char **argv)
{
  const leaf leaves[] = {
      LEAF2(mlkem_cbd2, test_cbd2),
      LEAF2(mlkem_cbd3, test_cbd3),
#if defined(__x86_64__)
      LEAF2(mlkem_unpack, test_unpack),
      LEAF2(mlkem_frombytes, test_frombytes_custom),
      LEAF2(mlkem_tobytes, test_tobytes_custom),
#else
      LEAF2(mlkem_frombytes, test_frombytes),
#endif
      LEAF2(mlkem_check_encoding, test_check_encoding),
      LEAF2(mlkem_rej_uniform_alt_VARIABLE_TIME, test_rej_uniform_alt),
      LEAF2(sha3_keccak_f1600, test_keccak),
#if defined(__x86_64__)
      LEAF2(sha3_keccak_f1600_alt2, test_keccak_alt2),
      LEAF2(sha3_keccak_f1600_avx512, test_keccak_avx512),
#endif
      LEAF2(mlkem_add_reduce, test_add_reduce),
      LEAF2(mlkem_sub_reduce, test_sub_reduce),
      LEAF2(mlkem_frommsg, test_frommsg),
      LEAF2(mlkem_tomsg, test_tomsg),
      CODEC(4),
      CODEC(5),
      CODEC(10),
      CODEC(11),
  };
  const char *only = argc > 2 ? argv[2] : NULL;
  unsigned tested = 0, skipped = 0;
  if (argc > 1) ntests = strtoul(argv[1], NULL, 0);
  for (size_t i = 0; i < sizeof(leaves) / sizeof(leaves[0]); i++)
  {
    if (only && strcmp(only, leaves[i].name) != 0) continue;
    if (!leaves[i].fn)
    {
      skipped++;
      continue;
    }
    tested++;
    if (leaves[i].test())
      failures++;
    else
      printf("ok %s\n", leaves[i].name);
  }
  printf("%s: %u functions tested, %u not present, %lu checks, %lu "
         "failures\n",
         failures ? "FAIL" : "OK", tested, skipped, checks, failures);
  return failures != 0;
}
