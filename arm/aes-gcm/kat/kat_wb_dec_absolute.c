// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//
// Phase-0 KAT gate, ABSOLUTE (stretch) check for the AES-256-GCM whole-blocks
// DECRYPT main-loop proof.  Complements the differential gate kat_wb_dec.c.
//
// Where the differential test proves "wb agrees with its trusted sibling on the
// whole-block path", this test proves "wb computes the CORRECT AES-256-GCM
// decryption" against a REAL, cryptographically-consistent key schedule and
// H-table, via an encrypt->decrypt round-trip:
//
//   1. Build a real AES-256 round-key schedule with aws-lc's
//      aes_hw_set_encrypt_key (read-only aarch64 asm, assembled into the
//      harness -- aws-lc is NOT modified).
//   2. Build a real GHASH H-power table: H = E_K(0) via aes_hw_encrypt, then
//      gcm_init_v8 fills the 192-byte Htable[0..11] (= H^1..H^8) that the 8x
//      kernel reads (up to offset 176).
//   3. Encrypt a known random plaintext PT (nblk whole blocks) with the trusted
//      sibling aesv8_gcm_8x_enc_256.o, starting from ivec0 and Xi=0.  Capture
//      the ciphertext CT and the encrypt's final GHASH accumulator Xi_enc.
//   4. Decrypt CT with the TARGET aesv8_gcm_8x_dec_256_wb.o, from the SAME
//      ivec0 and Xi=0.  Assert:
//        - recovered plaintext == PT  (CTR keystream is symmetric),
//        - Xi_dec == Xi_enc           (GHASH over the same ciphertext blocks),
//        - return value == 16*nblk.
//
//   Xi_dec == Xi_enc is the real tag-consistency check: GCM decrypt authenticates
//   the ciphertext, so its running GHASH must equal the encrypt's over identical
//   CT blocks.  A byteswap / lane / H-power-index bug in the dec main loop that
//   the differential test cannot see (because it would hit BOTH dec binaries
//   identically) is caught here against the independently-derived enc kernel.
//
// This is the aws-lc-dependent leg; it is a SEPARATE program from the primary
// differential gate so that gate stays self-contained.

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// --- objects under test / reference (frozen; do not rebuild) ---------------
extern size_t aesv8_gcm_8x_dec_256_wb(const uint8_t *in, size_t bit_len,
                                      uint8_t *out, uint8_t *Xi, uint8_t *ivec,
                                      const void *key, const void *Htable);
extern size_t aesv8_gcm_8x_enc_256(const uint8_t *in, size_t bit_len,
                                   uint8_t *out, uint8_t *Xi, uint8_t *ivec,
                                   const void *key, const void *Htable);

// --- aws-lc aarch64 asm helpers (assembled in, read-only) ------------------
typedef struct { uint64_t hi, lo; } u128;
typedef struct { uint32_t rd_key[60]; unsigned rounds; } AES_KEY;  // AES-256
extern int  aes_hw_set_encrypt_key(const uint8_t *user_key, int bits,
                                    AES_KEY *key);
extern void aes_hw_encrypt(const uint8_t *in, uint8_t *out, const AES_KEY *key);
extern void gcm_init_v8(u128 Htable[16], const uint64_t H[2]);

#define BLK       16u
#define MAX_NBLK  256u

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

static AES_KEY aes_key;
static u128    Htable[16]              __attribute__((aligned(16)));
static uint8_t user_key[32]            __attribute__((aligned(16)));
static uint8_t pt[MAX_NBLK * BLK]      __attribute__((aligned(16)));
static uint8_t ct[MAX_NBLK * BLK]      __attribute__((aligned(16)));
static uint8_t rt[MAX_NBLK * BLK]      __attribute__((aligned(16)));  // round-trip
static uint8_t ivec0[BLK]              __attribute__((aligned(16)));
static uint8_t ivec_e[BLK], ivec_d[BLK] __attribute__((aligned(16)));
static uint8_t xi_e[BLK], xi_d[BLK]    __attribute__((aligned(16)));

static void setup_key_and_htable(void) {
  fill_rand(user_key, sizeof user_key);
  int rc = aes_hw_set_encrypt_key(user_key, 256, &aes_key);
  if (rc != 0 || aes_key.rounds != 14) {
    printf("FATAL: aes_hw_set_encrypt_key rc=%d rounds=%u\n", rc,
           aes_key.rounds);
    _Exit(2);
  }
  // H = E_K(0), presented to gcm_init_v8 as big-endian uint64_t[2].
  uint8_t zero[BLK] = {0}, H[BLK];
  aes_hw_encrypt(zero, H, &aes_key);
  uint64_t Hbe[2];
  Hbe[0] = ((uint64_t)H[0] << 56) | ((uint64_t)H[1] << 48) |
           ((uint64_t)H[2] << 40) | ((uint64_t)H[3] << 32) |
           ((uint64_t)H[4] << 24) | ((uint64_t)H[5] << 16) |
           ((uint64_t)H[6] << 8) | (uint64_t)H[7];
  Hbe[1] = ((uint64_t)H[8] << 56) | ((uint64_t)H[9] << 48) |
           ((uint64_t)H[10] << 40) | ((uint64_t)H[11] << 32) |
           ((uint64_t)H[12] << 24) | ((uint64_t)H[13] << 16) |
           ((uint64_t)H[14] << 8) | (uint64_t)H[15];
  memset(Htable, 0, sizeof Htable);
  gcm_init_v8(Htable, Hbe);
}

static int run_one(size_t nblk) {
  const size_t nbytes  = nblk * BLK;
  const size_t bit_len = nbytes * 8u;   // = 128 * nblk

  fill_rand(pt, nbytes);
  memcpy(ivec_e, ivec0, BLK);   memset(xi_e, 0, BLK);
  memcpy(ivec_d, ivec0, BLK);   memset(xi_d, 0, BLK);
  memset(ct, 0, nbytes);
  memset(rt, 0, nbytes);

  // Encrypt PT -> CT with the trusted enc kernel.
  size_t re = aesv8_gcm_8x_enc_256(pt, bit_len, ct, xi_e, ivec_e,
                                   aes_key.rd_key, Htable);
  // Decrypt CT -> RT with the target wb dec kernel (same ivec0, Xi=0).
  size_t rd = aesv8_gcm_8x_dec_256_wb(ct, bit_len, rt, xi_d, ivec_d,
                                      aes_key.rd_key, Htable);

  int ok = 1;
  if (re != nbytes || rd != nbytes) {
    printf("  nblk=%3zu  FAIL: return enc=%zu dec=%zu expected=%zu\n", nblk, re,
           rd, nbytes);
    ok = 0;
  }
  if (memcmp(rt, pt, nbytes) != 0) {
    size_t j = 0; while (j < nbytes && rt[j] == pt[j]) j++;
    printf("  nblk=%3zu  FAIL: round-trip plaintext mismatch at byte %zu "
           "(pt=%02x rt=%02x)\n", nblk, j, pt[j], rt[j]);
    ok = 0;
  }
  if (memcmp(xi_d, xi_e, BLK) != 0) {
    printf("  nblk=%3zu  FAIL: GHASH acc mismatch enc vs dec\n", nblk);
    ok = 0;
  }
  // Non-degeneracy: real GCM must actually transform the data.
  if (ok && memcmp(ct, pt, nbytes) == 0) {
    printf("  nblk=%3zu  FAIL: ciphertext == plaintext (no encryption)\n", nblk);
    ok = 0;
  }
  return ok;
}

int main(void) {
  sm_state = 0x5EED1234ABCDEF01ull;
  fill_rand(ivec0, sizeof ivec0);
  setup_key_and_htable();

  static const size_t counts[] = {
      1, 2, 4, 7, 8,                    // dispatch
      9, 12, 15, 16,                    // prepretail-only
      17, 18, 20, 23, 24,               // q=1, remainders
      25, 32, 40, 48, 49, 64, 100, 128, 256,  // multi-iteration
  };
  const size_t ncases = sizeof(counts) / sizeof(counts[0]);

  printf("=== AES-256-GCM WB DEC KAT gate (ABSOLUTE enc->dec round-trip) ===\n");
  printf("    real AES-256 schedule + real H^1..H^8 table (H=E_K(0))\n");

  size_t passed = 0, failed = 0, body = 0;
  for (size_t i = 0; i < ncases; i++) {
    size_t nblk = counts[i];
    if (nblk > MAX_NBLK) continue;
    int ok = run_one(nblk);
    if (ok) {
      passed++;
      if (nblk >= 17) body++;
      const char *leg = nblk <= 8 ? "dispatch"
                        : nblk <= 16 ? "prepretail-only" : "MAIN-LOOP-BODY";
      printf("  nblk=%3zu  PASS  (%s)\n", nblk, leg);
    } else {
      failed++;
    }
  }

  printf("\n=== SUMMARY: %zu passed, %zu failed (%zu body cases nblk>=17) ===\n",
         passed, failed, body);
  if (failed == 0 && body > 0) { printf("ABSOLUTE KAT: PASS\n"); return 0; }
  printf("ABSOLUTE KAT: FAIL\n");
  return 1;
}
