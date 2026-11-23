/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/*
 * Cycles per call of the ML-KEM API functions (all three parameter sets),
 * for the library this is linked with. There may be no access to the PMU
 * or perf counters, so time is read from a fixed-rate counter and turned
 * into cycles with the clock frequency measured by a chain of dependent
 * additions:
 *  - AArch64: cntvct_el0 (1 GHz on Graviton 4), with the clock measured
 *    once at the start, since it does not vary;
 *  - x86_64: the TSC, with the clock measured right after each run of
 *    calls, since it varies with the turbo and the AVX frequency licences
 *    (the licence of a run persists for some time after it). The time per
 *    call in ns is also printed.
 * Each figure is the median over NTESTS runs of NITER calls, after
 * NWARMUP calls.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define NTESTS 31
#define NITER 200
#define NWARMUP 50

#if defined(__aarch64__)

static inline uint64_t ticks(void)
{
  uint64_t t;
  __asm__ volatile("isb; mrs %0, cntvct_el0" : "=r"(t));
  return t;
}

static uint64_t tick_hz(void)
{
  uint64_t f;
  __asm__ volatile("mrs %0, cntfrq_el0" : "=r"(f));
  return f;
}

#define ADD_CHAIN ".rept 1000\n add %0, %0, %0\n .endr"

#elif defined(__x86_64__)

static inline uint64_t ticks(void)
{
  uint32_t lo, hi;
  __asm__ volatile("lfence; rdtsc; lfence" : "=a"(lo), "=d"(hi));
  return ((uint64_t)hi << 32) | lo;
}

/* The TSC rate, against CLOCK_MONOTONIC over 100 ms */
static uint64_t tick_hz(void)
{
  struct timespec a, b;
  clock_gettime(CLOCK_MONOTONIC, &a);
  uint64_t t0 = ticks();
  do clock_gettime(CLOCK_MONOTONIC, &b);
  while ((b.tv_sec - a.tv_sec) * 1000000000LL + (b.tv_nsec - a.tv_nsec) <
         100000000LL);
  uint64_t t = ticks() - t0;
  double ns = (b.tv_sec - a.tv_sec) * 1e9 + (b.tv_nsec - a.tv_nsec);
  return (uint64_t)(t / ns * 1e9 + 0.5);
}

#define ADD_CHAIN ".rept 1000\n add %0, %0\n .endr"

#else
#error "AArch64 or x86_64 only"
#endif

/* Clock frequency in cycles per tick: n blocks of 1000 dependent
   additions, the fastest of r runs. */
static double cycles_per_tick_n(int r, int n)
{
  uint64_t best = ~(uint64_t)0;
  for (int k = 0; k < r; k++)
  {
    uint64_t x = 1, t0 = ticks();
    for (int i = 0; i < n; i++) __asm__ volatile(ADD_CHAIN : "+r"(x));
    uint64_t t = ticks() - t0;
    if (t < best) best = t;
  }
  return 1000.0 * n / (double)best;
}

static double cycles_per_tick(void) { return cycles_per_tick_n(20, 10000); }


static double cpt, hz;

/* On x86_64 each run's ticks are converted with the clock measured right
   after it (3 x 20000 additions, about 20 us), and the median of the
   cycle counts is printed with the median time in ns and the median
   clock. */
#if defined(__x86_64__)
static int cmp_double(const void *a, const void *b)
{
  double x = *(const double *)a, y = *(const double *)b;
  return (x > y) - (x < y);
}

#define BENCH(name, call)                                          \
  do                                                               \
  {                                                                \
    double c[NTESTS], ns[NTESTS], f[NTESTS];                       \
    for (int w = 0; w < NWARMUP; w++) (void)(call);                \
    for (int k = 0; k < NTESTS; k++)                               \
    {                                                              \
      uint64_t t0 = ticks();                                       \
      for (int i = 0; i < NITER; i++) (void)(call);                \
      uint64_t t = ticks() - t0;                                   \
      double r = cycles_per_tick_n(3, 20);                         \
      c[k] = (double)t * r / (double)NITER;                        \
      ns[k] = (double)t * 1e9 / hz / (double)NITER;                \
      f[k] = r * hz / 1e9;                                         \
    }                                                              \
    qsort(c, NTESTS, sizeof(double), cmp_double);                  \
    qsort(ns, NTESTS, sizeof(double), cmp_double);                 \
    qsort(f, NTESTS, sizeof(double), cmp_double);                  \
    printf("%-26s %9.0f %9.0f ns %6.3f GHz\n", name,               \
           c[NTESTS / 2], ns[NTESTS / 2], f[NTESTS / 2]);          \
  } while (0)
#else
static int cmp_u64(const void *a, const void *b)
{
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return (x > y) - (x < y);
}

#define BENCH(name, call)                                          \
  do                                                               \
  {                                                                \
    uint64_t t[NTESTS];                                            \
    for (int w = 0; w < NWARMUP; w++) (void)(call);                \
    for (int k = 0; k < NTESTS; k++)                               \
    {                                                              \
      uint64_t t0 = ticks();                                       \
      for (int i = 0; i < NITER; i++) (void)(call);                \
      t[k] = ticks() - t0;                                         \
    }                                                              \
    qsort(t, NTESTS, sizeof(uint64_t), cmp_u64);                   \
    printf("%-26s %9.0f\n", name,                                  \
           (double)t[NTESTS / 2] * cpt / (double)NITER);           \
  } while (0)
#endif

/* Deterministic randombytes for the randomized API functions. */
static uint64_t rng_state = 0x0123456789abcdefULL;
int randombytes(uint8_t *out, size_t outlen)
{
  for (size_t i = 0; i < outlen; i++)
  {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    out[i] = (uint8_t)rng_state;
  }
  return 0;
}

#define DECLARE(L)                                                        \
  int mlkem##L##_keypair_derand(uint8_t *, uint8_t *, const uint8_t *);   \
  int mlkem##L##_keypair(uint8_t *, uint8_t *) __attribute__((weak));     \
  int mlkem##L##_enc_derand(uint8_t *, uint8_t *, const uint8_t *,        \
                            const uint8_t *);                             \
  int mlkem##L##_enc(uint8_t *, uint8_t *, const uint8_t *)               \
      __attribute__((weak));                                              \
  int mlkem##L##_dec(uint8_t *, const uint8_t *, const uint8_t *);        \
  int mlkem##L##_check_pk(const uint8_t *);                               \
  int mlkem##L##_check_sk(const uint8_t *);
DECLARE(512)
DECLARE(768)
DECLARE(1024)

#define RUN(L)                                                            \
  do                                                                      \
  {                                                                       \
    static uint8_t pk[1568], sk[3168], ct[1568], ss[32], coins[64];      \
    randombytes(coins, 64);                                               \
    mlkem##L##_keypair_derand(pk, sk, coins);                             \
    mlkem##L##_enc_derand(ct, ss, pk, coins);                             \
    BENCH("mlkem" #L "_keypair_derand",                                   \
          mlkem##L##_keypair_derand(pk, sk, coins));                      \
    if (mlkem##L##_keypair)                                               \
      BENCH("mlkem" #L "_keypair", mlkem##L##_keypair(pk, sk));           \
    BENCH("mlkem" #L "_enc_derand",                                       \
          mlkem##L##_enc_derand(ct, ss, pk, coins));                      \
    if (mlkem##L##_enc)                                                   \
      BENCH("mlkem" #L "_enc", mlkem##L##_enc(ct, ss, pk));               \
    BENCH("mlkem" #L "_dec", mlkem##L##_dec(ss, ct, sk));                 \
    BENCH("mlkem" #L "_check_pk", mlkem##L##_check_pk(pk));               \
    BENCH("mlkem" #L "_check_sk", mlkem##L##_check_sk(sk));               \
  } while (0)

int main(int argc, char **argv)
{
  hz = (double)tick_hz();
  cpt = cycles_per_tick();
  printf("# clock %.3f GHz (timer %.3f GHz)%s%s\n", cpt * hz / 1e9,
         hz / 1e9,
         argc > 1 ? ", " : "", argc > 1 ? argv[1] : "");
  RUN(512);
  RUN(768);
  RUN(1024);
  return 0;
}
