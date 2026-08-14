// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//
// KAT gate for the AES-256-GCM whole-blocks DECRYPT kernel.
//
// PURPOSE
// -------
// Mechanically validate the nblk>8 machine code of aesv8_gcm_8x_dec_256_wb.o
// -- the main loop (.L256_dec_main_loop 0x4a0..0x9ec) and prepretail
// (0x9f0..0xec0) -- by execution, independently of the HOL Light proof.
//
// PRIMARY CHECK (differential) -- implemented here.
//   The wb binary was derived from the trusted upstream sibling
//   aesv8_gcm_8x_dec_256.o by exactly two edits (verified by disassembly diff):
//     (a) an entry guard  `tst x1,#127; b.ne .L256_dec_ret`;
//     (b) DELETION of the partial-last-block masking tail
//         (.L256_dec_blocks_less_than_1: ld1/mvn/and/lsr/csel/bif ...).
//   The whole entire main-loop + prepretail + whole-block tail is BYTE-IDENTICAL
//   between the two objects.  On a whole-block (bit_len % 128 == 0) input the
//   sibling's deleted tail is a no-op (it blends the freshly computed block with
//   an all-ones mask, discarding the buffer it read), so BOTH functions must
//   compute the identical (out, Xi, ivec, return value).  Any divergence is
//   exactly the guard-shifted-PC / ABI-clobber / byteswap bug class this gate
//   exists to surface.
//
//   Neither binary has any DATA-dependent branch (AES / GHASH / CTR are
//   straight-line constant-time NEON; every branch is LENGTH-dependent only).
//   Therefore the differential is valid with ARBITRARY but IDENTICAL key /
//   Htable / ivec / Xi / ciphertext material -- we do not need a
//   cryptographically consistent (H = E_K(0)) H-table for the two binaries to
//   agree.  This keeps the primary gate self-contained (no aws-lc helper wiring).
//
// ABI (confirmed from the .S and objdump; both objects share it):
//   size_t f(const uint8_t *in,      // X0  ciphertext, read-only, 16*nblk bytes
//            size_t     bit_len,     // X1  message length in BITS = 128*nblk
//            uint8_t   *out,         // X2  plaintext out,  16*nblk bytes
//            uint8_t   *Xi,          // X3  GHASH acc, 16 bytes, IN and OUT
//            uint8_t    ivec[16],    // X4  counter block, 16 bytes, IN and OUT
//            const void *key,        // X5  AES-256 round-key schedule, 240 bytes RO
//            const void *Htable);    // X6  GHASH H-power table, 192 bytes read RO
//   returns bit_len/8 == 16*nblk on the whole-block path.
//
// TRIP-COUNT LEGS EXERCISED (q = number of full 8-block main-loop iterations):
//   nblk <= 8        -> early b.ge .L256_dec_tail (proven DISPATCH path).
//   9 <= nblk <= 16  -> b.ge .L256_dec_prepretail (loop body NOT entered), q=0.
//   nblk >= 17       -> q = (nblk-9) DIV 8 >= 1 full main-loop-body iterations,
//                       then prepretail + tail(r), r = nblk - 8*(q+1) in 1..8.
//   The sweep below covers all three legs and every tail remainder r=1..8.

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern size_t aesv8_gcm_8x_dec_256_wb(const uint8_t *in, size_t bit_len,
                                      uint8_t *out, uint8_t *Xi, uint8_t *ivec,
                                      const void *key, const void *Htable);

extern size_t aesv8_gcm_8x_dec_256(const uint8_t *in, size_t bit_len,
                                   uint8_t *out, uint8_t *Xi, uint8_t *ivec,
                                   const void *key, const void *Htable);

#define KEY_BYTES     240u   // AES-256: 15 round keys * 16 bytes (rk0..rk14)
#define HTABLE_BYTES  256u   // u128 Htable[16]; kernel reads up to offset 176
#define MAX_NBLK      256u   // largest block count in the sweep
#define BLK           16u

// Deterministic PRNG (splitmix64) so the gate is fully reproducible.
static uint64_t sm_state;
static uint64_t sm_next(void) {
  uint64_t z = (sm_state += 0x9E3779B97F4A7C15ull);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
  return z ^ (z >> 31);
}
static void fill_rand(uint8_t *p, size_t n) {
  for (size_t i = 0; i < n; i++) p[i] = (uint8_t)(sm_next() & 0xff);
}

// 16-byte aligned shared inputs (real callers pass aligned struct/table ptrs).
static uint8_t key[KEY_BYTES]        __attribute__((aligned(16)));
static uint8_t Htable[HTABLE_BYTES]  __attribute__((aligned(16)));
static uint8_t in_ct[MAX_NBLK * BLK] __attribute__((aligned(16)));
static uint8_t xi0[BLK]              __attribute__((aligned(16)));
static uint8_t ivec0[BLK]            __attribute__((aligned(16)));

// per-binary mutable state
static uint8_t out_a[MAX_NBLK * BLK] __attribute__((aligned(16)));
static uint8_t out_b[MAX_NBLK * BLK] __attribute__((aligned(16)));
static uint8_t xi_a[BLK]             __attribute__((aligned(16)));
static uint8_t xi_b[BLK]             __attribute__((aligned(16)));
static uint8_t ivec_a[BLK]           __attribute__((aligned(16)));
static uint8_t ivec_b[BLK]           __attribute__((aligned(16)));

static void hexdiff(const char *tag, const uint8_t *a, const uint8_t *b,
                    size_t n) {
  size_t first = (size_t)-1;
  for (size_t i = 0; i < n; i++)
    if (a[i] != b[i]) { first = i; break; }
  if (first == (size_t)-1) return;
  printf("      %s first mismatch at byte %zu: wb=%02x sib=%02x\n", tag, first,
         a[first], b[first]);
}

// Run the differential on one block count.  Returns 1 on pass, 0 on fail.
static int run_one(size_t nblk) {
  const size_t nbytes  = nblk * BLK;
  const size_t bit_len = nbytes * 8u;   // = 128 * nblk

  // Poison output buffers so a "wrote nothing" bug is visible, not a silent 0.
  memset(out_a, 0xAA, nbytes);
  memset(out_b, 0x55, nbytes);
  memcpy(xi_a, xi0, BLK);       memcpy(xi_b, xi0, BLK);
  memcpy(ivec_a, ivec0, BLK);   memcpy(ivec_b, ivec0, BLK);

  size_t ra = aesv8_gcm_8x_dec_256_wb(in_ct, bit_len, out_a, xi_a, ivec_a,
                                      key, Htable);
  size_t rb = aesv8_gcm_8x_dec_256(in_ct, bit_len, out_b, xi_b, ivec_b,
                                   key, Htable);

  int ok = 1;
  if (ra != rb) {
    printf("  nblk=%3zu  FAIL: return wb=%zu sib=%zu\n", nblk, ra, rb);
    ok = 0;
  }
  if (ra != nbytes) {
    printf("  nblk=%3zu  FAIL: wb return %zu != expected %zu\n", nblk, ra,
           nbytes);
    ok = 0;
  }
  if (memcmp(out_a, out_b, nbytes) != 0) {
    printf("  nblk=%3zu  FAIL: plaintext differs\n", nblk);
    hexdiff("out", out_a, out_b, nbytes);
    ok = 0;
  }
  if (memcmp(xi_a, xi_b, BLK) != 0) {
    printf("  nblk=%3zu  FAIL: Xi differs\n", nblk);
    hexdiff("Xi", xi_a, xi_b, BLK);
    ok = 0;
  }
  if (memcmp(ivec_a, ivec_b, BLK) != 0) {
    printf("  nblk=%3zu  FAIL: ivec differs\n", nblk);
    hexdiff("ivec", ivec_a, ivec_b, BLK);
    ok = 0;
  }
  // Non-degeneracy: for random CT the decrypt MUST change bytes and advance
  // GHASH; a "both no-op'd identically" bug would else pass the diff silently.
  if (ok && memcmp(out_a, in_ct, nbytes) == 0) {
    printf("  nblk=%3zu  FAIL: output == input (no decryption happened)\n",
           nblk);
    ok = 0;
  }
  if (ok && memcmp(xi_a, xi0, BLK) == 0) {
    printf("  nblk=%3zu  FAIL: Xi unchanged (no GHASH happened)\n", nblk);
    ok = 0;
  }
  return ok;
}

int main(void) {
  sm_state = 0xC0FFEE123456789Aull;   // fixed seed => reproducible
  fill_rand(key, sizeof key);
  fill_rand(Htable, sizeof Htable);
  fill_rand(in_ct, sizeof in_ct);
  fill_rand(xi0, sizeof xi0);
  fill_rand(ivec0, sizeof ivec0);

  // Sweep every leg: DISPATCH (1..8), prepretail-only (9..16),
  // multi-iteration loop body (17..) covering every tail remainder r=1..8,
  // plus a few larger counts.
  static const size_t counts[] = {
      1, 2, 3, 4, 5, 6, 7, 8,           // <=8: DISPATCH (loop never entered)
      9, 10, 11, 12, 13, 14, 15, 16,    // 9..16: prepretail-only, q=0
      17, 18, 19, 20, 21, 22, 23, 24,   // q=1, remainders r=1..8
      25, 32, 33, 40, 48, 49,           // q>=2, assorted remainders
      64, 100, 128, 200, 256,           // larger, many iterations
  };
  const size_t ncases = sizeof(counts) / sizeof(counts[0]);

  printf("=== AES-256-GCM WB DEC KAT gate (differential wb vs sibling) ===\n");
  printf("    key=%u B  Htable=%u B  arbitrary-but-identical material\n",
         KEY_BYTES, HTABLE_BYTES);

  size_t passed = 0, failed = 0, body = 0;
  for (size_t i = 0; i < ncases; i++) {
    size_t nblk = counts[i];
    if (nblk > MAX_NBLK) { printf("  (skip nblk=%zu > MAX)\n", nblk); continue; }
    int ok = run_one(nblk);
    if (ok) {
      passed++;
      const char *leg = nblk <= 8    ? "dispatch"
                        : nblk <= 16 ? "prepretail-only"
                                     : "MAIN-LOOP-BODY";
      size_t q = nblk >= 9 ? (nblk - 9) / 8 : 0;
      if (nblk >= 17) body++;
      printf("  nblk=%3zu  PASS  (%s, q=%zu full iters)\n", nblk, leg, q);
    } else {
      failed++;
    }
  }

  printf("\n=== SUMMARY: %zu passed, %zu failed (%zu of the passing cases "
         "exercised the main-loop BODY, nblk>=17) ===\n",
         passed, failed, body);
  if (failed == 0 && body > 0) {
    printf("KAT GATE: PASS\n");
    return 0;
  }
  printf("KAT GATE: FAIL\n");
  return 1;
}
