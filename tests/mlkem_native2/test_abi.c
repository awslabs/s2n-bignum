/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/*
 * ABI check of the candidate's ML-KEM API. Each function is called
 * through abi_call (abi_stub.S) with random values in x8..x29 (x18
 * included) and q0..q31, on a stack of its own painted with a pattern.
 * After the call:
 *  - x19..x29, the low halves of q8..q15 and sp must be unchanged, as
 *    AAPCS64 requires, and so must x18, the platform register, which the
 *    asm does not use (compiled C may, so -x18 makes that a warning);
 *  - the outputs must equal those of a direct call;
 *  - the stack depth is the extent of the stack no longer holding the
 *    pattern, and the residue is the number of bytes there that are
 *    neither the pattern nor zero, i.e. what the function leaves behind;
 *  - no 16 consecutive bytes of the residue may equal 16 consecutive bytes
 *    of a secret known to the test (the coins, the seeds sigma and r
 *    derived from them, the secret vector s in bytes and in coefficients,
 *    the shared secret, z), since secrets on the stack must be zeroed
 *    (-leaks reports these as warnings instead, for compiled C).
 *
 * On x86_64 the stub is abi_stub_x86.S, which randomizes all the general
 * and vector registers but rsp; rbx, rbp, r12..r15 and rsp must be
 * preserved (System V), and for the Microsoft x64 entries (the API built
 * with WINDOWS_ABI, its symbols renamed with the prefix ms_, called through
 * abi_call_ms), also rdi, rsi and the low halves of xmm6..xmm15. The
 * -x18 option has no effect there.
 *
 * usage: test_abi [-x18] [-leaks]
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

uint64_t abi_call(void *fn, const uint64_t args[8], const uint64_t in[96],
                  uint64_t out[96], void *stack_top);
#if defined(__x86_64__)
uint64_t abi_call_ms(void *fn, const uint64_t args[8],
                     const uint64_t in[96], uint64_t out[96],
                     void *stack_top);
#endif

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

#if defined(__x86_64__)
#define MS __attribute__((ms_abi))
#define MSW __attribute__((ms_abi, weak))
#define DECLARE_MS(L)                                                        \
  MSW int ms_mlkem##L##_keypair_derand(uint8_t *, uint8_t *,                 \
                                       const uint8_t *);                     \
  MSW int ms_mlkem##L##_enc_derand(uint8_t *, uint8_t *, const uint8_t *,    \
                                   const uint8_t *);                         \
  MSW int ms_mlkem##L##_dec(uint8_t *, const uint8_t *, const uint8_t *);    \
  MSW int ms_mlkem##L##_check_pk(const uint8_t *);                           \
  MSW int ms_mlkem##L##_check_sk(const uint8_t *);
DECLARE_MS(512)
DECLARE_MS(768)
DECLARE_MS(1024)
#endif

int randombytes(uint8_t *out, size_t outlen);
int randombytes(uint8_t *out, size_t outlen)
{
  (void)out, (void)outlen;
  abort();
}

static uint64_t rng = 7;
static uint64_t rand64(void)
{
  uint64_t z = (rng += 0x9e3779b97f4a7c15ULL);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}
static void randfill(uint8_t *p, size_t n)
{
  for (size_t i = 0; i < n; i++) p[i] = (uint8_t)rand64();
}

#define STACK (1 << 20)
#define PATTERN 0xa5
static uint8_t stack[STACK] __attribute__((aligned(16)));
static int strict_x18 = 1, strict_leaks = 1;

/* The 16-byte windows of the secrets of the current call, sorted */
typedef struct
{
  uint64_t lo, hi;
} win;
static win secrets[65536];
static size_t nsecrets;
static int wincmp(const void *a, const void *b)
{
  const win *x = a, *y = b;
  if (x->hi != y->hi) return x->hi < y->hi ? -1 : 1;
  return (x->lo > y->lo) - (x->lo < y->lo);
}
static void add_secret(const void *p, size_t n)
{
  for (size_t i = 0; i + 16 <= n && nsecrets < 65536; i++)
  {
    memcpy(&secrets[nsecrets].lo, (const uint8_t *)p + i, 8);
    memcpy(&secrets[nsecrets].hi, (const uint8_t *)p + i + 8, 8);
    nsecrets++;
  }
}
static size_t leaks_in(const uint8_t *p, size_t n)
{
  size_t found = 0;
  qsort(secrets, nsecrets, sizeof(win), wincmp);
  for (size_t i = 0; i + 16 <= n; i++)
  {
    win w;
    memcpy(&w.lo, p + i, 8);
    memcpy(&w.hi, p + i + 8, 8);
    if (bsearch(&w, secrets, nsecrets, sizeof(win), wincmp)) found++;
  }
  return found;
}
static unsigned long failures;

typedef struct
{
  const char *name;
  void *fn;
  int nargs;
  uint8_t *out[2];
  size_t outlen[2];
  const uint8_t *in[3];
  int ms; /* x86_64: the Microsoft x64 entry */
} call;

/* Calls fn(args) directly and then three times through abi_call, and
   checks the register state, outputs and stack of the latter. */
static void check(unsigned level, call *c)
{
  static uint8_t want[2][4096];
  uint64_t args[8] = {0}, in[96], out[96];
  int nout = 0, want_ret;
  size_t depth = 0, residue = 0, leaks = 0;
  for (int i = 0; i < 2 && c->out[i]; i++) nout = i + 1;
  for (int i = 0; i < nout; i++) args[i] = (uint64_t)c->out[i];
  for (int i = nout; i < c->nargs; i++)
    args[i] = (uint64_t)c->in[i - nout];
#if defined(__x86_64__)
  if (c->ms) switch (c->nargs)
  {
    case 1:
      want_ret = ((MS int (*)(uint64_t))c->fn)(args[0]);
      break;
    case 3:
      want_ret = ((MS int (*)(uint64_t, uint64_t, uint64_t))c->fn)(
          args[0], args[1], args[2]);
      break;
    default:
      want_ret = ((MS int (*)(uint64_t, uint64_t, uint64_t, uint64_t))c->fn)(
          args[0], args[1], args[2], args[3]);
      break;
  }
  else
#endif
  switch (c->nargs)
  {
    case 1:
      want_ret = ((int (*)(uint64_t))c->fn)(args[0]);
      break;
    case 3:
      want_ret =
          ((int (*)(uint64_t, uint64_t, uint64_t))c->fn)(args[0], args[1],
                                                        args[2]);
      break;
    default:
      want_ret = ((int (*)(uint64_t, uint64_t, uint64_t, uint64_t))c->fn)(
          args[0], args[1], args[2], args[3]);
      break;
  }
  for (int i = 0; i < nout; i++) memcpy(want[i], c->out[i], c->outlen[i]);
  for (int t = 0; t < 3; t++)
  {
    int ret, bad = 0;
    size_t d = 0, r = 0;
    for (int i = 0; i < 96; i++) in[i] = rand64(), out[i] = 0;
    for (int i = 0; i < nout; i++) memset(c->out[i], 0, c->outlen[i]);
    memset(stack, PATTERN, STACK);
#if defined(__x86_64__)
    {
      static const char *gpr[16] = {"rax", "rbx", "rcx", "rdx", "rsi", "rdi",
                                    "rbp", "rsp", "r8",  "r9",  "r10", "r11",
                                    "r12", "r13", "r14", "r15"};
      static const int sysv[] = {1, 6, 12, 13, 14, 15}, msx[] = {4, 5};
      ret = (int)(c->ms ? abi_call_ms : abi_call)(c->fn, args, in, out,
                                                  stack + STACK);
      for (size_t i = 0; i < sizeof(sysv) / sizeof(sysv[0]); i++)
        if (out[sysv[i]] != in[sysv[i]])
          printf("FAIL ML-KEM-%u %s: %s not preserved\n", level, c->name,
                 gpr[sysv[i]]),
              bad = 1;
      if (c->ms)
      {
        for (size_t i = 0; i < sizeof(msx) / sizeof(msx[0]); i++)
          if (out[msx[i]] != in[msx[i]])
            printf("FAIL ML-KEM-%u %s: %s not preserved\n", level, c->name,
                   gpr[msx[i]]),
                bad = 1;
        for (int q = 6; q <= 15; q++)
          if (out[16 + 4 * q] != in[16 + 4 * q] ||
              out[17 + 4 * q] != in[17 + 4 * q])
            printf("FAIL ML-KEM-%u %s: xmm%d not preserved\n", level,
                   c->name, q),
                bad = 1;
      }
      if (out[7] != (uint64_t)(stack + STACK))
        printf("FAIL ML-KEM-%u %s: rsp not preserved\n", level, c->name),
            bad = 1;
    }
#else
    ret = (int)abi_call(c->fn, args, in, out, stack + STACK);
    for (int x = 19; x <= 29; x++)
      if (out[x] != in[x])
        printf("FAIL ML-KEM-%u %s: x%d not preserved\n", level, c->name, x),
            bad = 1;
    for (int q = 8; q <= 15; q++)
      if (out[32 + 2 * q] != in[32 + 2 * q])
        printf("FAIL ML-KEM-%u %s: d%d not preserved\n", level, c->name, q),
            bad = 1;
    if (out[31] != (uint64_t)(stack + STACK))
      printf("FAIL ML-KEM-%u %s: sp not preserved\n", level, c->name),
          bad = 1;
    if (out[18] != in[18])
    {
      printf("%s ML-KEM-%u %s: x18 not preserved\n",
             strict_x18 ? "FAIL" : "warning", level, c->name);
      bad |= strict_x18;
    }
#endif
    if (ret != want_ret)
      printf("FAIL ML-KEM-%u %s: return value %d, direct call %d\n", level,
             c->name, ret, want_ret),
          bad = 1;
    for (int i = 0; i < nout; i++)
      if (memcmp(want[i], c->out[i], c->outlen[i]) != 0)
        printf("FAIL ML-KEM-%u %s: output %d differs from direct call\n",
               level, c->name, i),
            bad = 1;
    while (d < STACK && stack[d] == PATTERN) d++;
    for (size_t i = d; i < STACK; i++)
      r += stack[i] != PATTERN && stack[i] != 0;
    {
      size_t l = leaks_in(stack + d, STACK - d);
      if (l > leaks) leaks = l;
    }
    d = STACK - d;
    if (d > depth) depth = d;
    if (r > residue) residue = r;
    failures += bad;
  }
  if (leaks)
  {
    printf("%s ML-KEM-%u %s: %zu windows of secrets left on the stack\n",
           strict_leaks ? "FAIL" : "warning", level, c->name, leaks);
    failures += strict_leaks;
  }
  printf("ML-KEM-%-4u %-19s stack %6zu bytes, residue %5zu bytes\n", level,
         c->name, depth, residue);
}

/* The secrets of call i (0 keypair_derand, 1 enc_derand, 2, 3 dec, 4
   check_pk, 5 check_sk), given the coins (the same for keypair and enc as
   used here), sk, ss and pk */
void ref_sha3_512(uint8_t *out, const uint8_t *in, size_t inlen);
void ref_sha3_256(uint8_t *out, const uint8_t *in, size_t inlen);
static void set_secrets(unsigned k, size_t i, const uint8_t *coins,
                        const uint8_t *sk, const uint8_t *ss,
                        const uint8_t *pk)
{
  uint8_t in[64], g[64];
  int16_t s16[1024];
  size_t pkb = 384 * k + 32, skb = 768 * k + 96;
  nsecrets = 0;
  if (i == 0)
  {
    add_secret(coins, 64);
    memcpy(in, coins, 32);
    in[32] = (uint8_t)k;
    ref_sha3_512(g, in, 33);
    add_secret(g + 32, 32);
  }
  if (i == 1 || i == 2 || i == 3)
  {
    add_secret(coins, 32);
    memcpy(in, coins, 32);
    ref_sha3_256(in + 32, pk, pkb);
    ref_sha3_512(g, in, 64);
    add_secret(g, 64);
    add_secret(ss, 32);
  }
  if (i == 0 || i == 2 || i == 3)
  {
    add_secret(sk, 384 * k);
    for (unsigned j = 0; j < 256 * k; j++)
    {
      unsigned b = 12 * j;
      s16[j] = (int16_t)(((sk[b / 8] | sk[b / 8 + 1] << 8) >> (b % 8)) & 4095);
    }
    add_secret(s16, 512 * k);
    add_secret(sk + skb - 32, 32);
  }
}

#define RUN(L, PKB, SKB, CTB)                                                \
  do                                                                         \
  {                                                                          \
    static uint8_t pk[PKB], sk[SKB], ct[CTB], ss[32], coins[64], bad[CTB];  \
    randfill(coins, 64);                                                     \
    mlkem##L##_keypair_derand(pk, sk, coins);                                \
    mlkem##L##_enc_derand(ct, ss, pk, coins);                                \
    memcpy(bad, ct, CTB);                                                    \
    bad[0] ^= 1;                                                             \
    call cs[] = {                                                            \
        {"keypair_derand", (void *)mlkem##L##_keypair_derand, 3, {pk, sk},  \
         {PKB, SKB}, {coins}, 0},                                            \
        {"enc_derand", (void *)mlkem##L##_enc_derand, 4, {ct, ss},           \
         {CTB, 32}, {pk, coins}, 0},                                         \
        {"dec", (void *)mlkem##L##_dec, 3, {ss}, {32}, {ct, sk}, 0},         \
        {"dec(reject)", (void *)mlkem##L##_dec, 3, {ss}, {32}, {bad, sk},    \
         0},                                                                 \
        {"check_pk", (void *)mlkem##L##_check_pk, 1, {0}, {0}, {pk}, 0},     \
        {"check_sk", (void *)mlkem##L##_check_sk, 1, {0}, {0}, {sk}, 0}};    \
    for (size_t i = 0; i < sizeof(cs) / sizeof(cs[0]); i++)                 \
    {                                                                        \
      set_secrets(L / 256, i, coins, sk, ss, pk);                            \
      check(L, &cs[i]);                                                      \
    }                                                                        \
    RUN_MS(L, PKB, SKB, CTB);                                                \
  } while (0)

#if defined(__x86_64__)
#define RUN_MS(L, PKB, SKB, CTB)                                             \
  do                                                                         \
  {                                                                          \
    call ms[] = {                                                            \
        {"ms keypair_derand", (void *)ms_mlkem##L##_keypair_derand, 3,       \
         {pk, sk}, {PKB, SKB}, {coins}, 1},                                  \
        {"ms enc_derand", (void *)ms_mlkem##L##_enc_derand, 4, {ct, ss},     \
         {CTB, 32}, {pk, coins}, 1},                                         \
        {"ms dec", (void *)ms_mlkem##L##_dec, 3, {ss}, {32}, {ct, sk}, 1},   \
        {"ms dec(reject)", (void *)ms_mlkem##L##_dec, 3, {ss}, {32},         \
         {bad, sk}, 1},                                                      \
        {"ms check_pk", (void *)ms_mlkem##L##_check_pk, 1, {0}, {0}, {pk},   \
         1},                                                                 \
        {"ms check_sk", (void *)ms_mlkem##L##_check_sk, 1, {0}, {0}, {sk},   \
         1}};                                                                \
    for (size_t i = 0; i < sizeof(ms) / sizeof(ms[0]); i++)                 \
      if (ms[i].fn)                                                          \
      {                                                                      \
        set_secrets(L / 256, i, coins, sk, ss, pk);                          \
        check(L, &ms[i]);                                                    \
      }                                                                      \
  } while (0)
#else
#define RUN_MS(L, PKB, SKB, CTB) \
  do                             \
  {                              \
  } while (0)
#endif

int main(int argc, char **argv)
{
  for (int a = 1; a < argc; a++)
  {
    if (strcmp(argv[a], "-x18") == 0) strict_x18 = 0;
    if (strcmp(argv[a], "-leaks") == 0) strict_leaks = 0;
  }
  RUN(512, 800, 1632, 768);
  RUN(768, 1184, 2400, 1088);
  RUN(1024, 1568, 3168, 1568);
  printf("%s: %lu failed calls\n", failures ? "FAIL" : "OK", failures);
  return failures != 0;
}
