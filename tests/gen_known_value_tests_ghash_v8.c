// Generator for known_value_tests_ghash_v8.h. NOT built by the Makefile and not
// part of the test binary; it exists so the frozen KAT table is reproducible and
// its provenance auditable.
//
// aws-lc has no GHASH-only vector file (gcm_tests.txt holds full AEAD vectors,
// and gcm_test.cc's GHASH coverage is an ABI test with no expected values), so
// the expected Xi_out values are computed here by the VERBATIM aws-lc reference
// gcm_ghash_nohw / gcm_init_nohw in ref_gcm_nohw.c (copied byte-for-byte from
// aws-lc crypto/fipsmodule/modes/gcm_nohw.c at commit 83e7c97c6). No value is
// invented: each is the output of unmodified aws-lc code on the stated input.
// Note the reference is driven here, NOT the assembly -- the assembly is what
// the resulting KAT then holds to account.
//
// Reproduce with, from this directory:
//
//   cc -std=gnu99 -O2 -o /tmp/genkat gen_known_value_tests_ghash_v8.c -lm
//   /tmp/genkat
//
// and the emitted GHASH_KAT lines must match known_value_tests_ghash_v8.h.

#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/s2n-bignum.h"
#include "ref_aes_xts.c"
#include "ref_gcm_nohw.c"

// splitmix64, so the H / Xi / input bytes are reproducible from the seed alone.
static uint64_t sm_state;
static uint64_t sm_next(void) {
  uint64_t z = (sm_state += 0x9e3779b97f4a7c15ULL);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}
static void sm_bytes(uint8_t *p, size_t n) {
  for (size_t i = 0; i < n; ++i) p[i] = (uint8_t)(sm_next() >> 24);
}
static void phex(const uint8_t *p, size_t n) {
  for (size_t i = 0; i < n; ++i) printf("%02x", p[i]);
}

int main(void) {
  // Block counts chosen to hit every distinct trace through the assembly:
  // 1,2,3 = the len < 64 path; 4 = 4x path/.Ldone4x; 5,7 = .Lone/.Lthree tails;
  // 8 = one .Loop4x iteration; 11 = one iteration + .Lthree; 17 = many + .Lone.
  static const int ns[] = { 1, 2, 3, 4, 5, 7, 8, 11, 17 };
  sm_state = 0x6763686173687638ULL;   // "gchashv8"
  for (unsigned k = 0; k < sizeof(ns)/sizeof(ns[0]); ++k) {
    int n = ns[k];
    uint8_t Hbytes[16], Xi[16];
    static uint8_t inp[17*16];
    sm_bytes(Hbytes, 16);
    sm_bytes(Xi, 16);
    sm_bytes(inp, (size_t)n * 16);

    uint64_t H[2] = { CRYPTO_load_u64_be(Hbytes), CRYPTO_load_u64_be(Hbytes+8) };
    u128 Ht[16]; memset(Ht, 0, sizeof Ht);
    gcm_init_nohw(Ht, H);
    uint8_t Xo[16]; memcpy(Xo, Xi, 16);
    gcm_ghash_nohw(Xo, Ht, inp, (size_t)n * 16);

    printf("  GHASH_KAT(%2d, \"", n); phex(Hbytes,16);
    printf("\",\n       \""); phex(Xi,16);
    printf("\",\n       \""); phex(inp,(size_t)n*16);
    printf("\",\n       \""); phex(Xo,16);
    printf("\" )\n");
  }
  return 0;
}
