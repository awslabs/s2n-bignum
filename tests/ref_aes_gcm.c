// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// Minimal AES-256-GCM reference for testing the s2n-bignum aes256_gcm assembly.
//
// The GF(2^128) routines gcm_mul32_nohw / gcm_mul64_nohw / gcm_polyval_nohw
// below are ported VERBATIM from AWS-LC
//   crypto/fipsmodule/modes/gcm_nohw.c
// (the generic, no-uint128/no-SSE variant) and retain their original license:
//
//   Copyright (c) 2019, Google Inc.
//   SPDX-License-Identifier: ISC
//
// Everything else here (the Htable power-table builder, the single-block GHASH
// fold, and the CTR+GHASH+partial-mask driver) is test-only glue.  The AES-256
// key expansion and block encrypt are reused from ref_aes_xts.c, which must be
// #included before this file.
//
// This file is #included directly into test.c (not compiled separately), like
// ref_aes_xts.c.  All symbols are static.  ARM-only data path: the callers are
// guarded with #ifdef __x86_64__.

#ifndef __x86_64__

// ---------------------------------------------------------------------------
// AWS-LC gcm_nohw.c (verbatim): 32x32 -> 64 carryless multiply.
// ---------------------------------------------------------------------------
static uint64_t gcm_mul32_nohw(uint32_t a, uint32_t b) {
  // One term every four bits means the largest term is 32/4 = 8, which does not
  // overflow into the next term.
  uint32_t a0 = a & 0x11111111;
  uint32_t a1 = a & 0x22222222;
  uint32_t a2 = a & 0x44444444;
  uint32_t a3 = a & 0x88888888;

  uint32_t b0 = b & 0x11111111;
  uint32_t b1 = b & 0x22222222;
  uint32_t b2 = b & 0x44444444;
  uint32_t b3 = b & 0x88888888;

  uint64_t c0 = (a0 * (uint64_t)b0) ^ (a1 * (uint64_t)b3) ^
                (a2 * (uint64_t)b2) ^ (a3 * (uint64_t)b1);
  uint64_t c1 = (a0 * (uint64_t)b1) ^ (a1 * (uint64_t)b0) ^
                (a2 * (uint64_t)b3) ^ (a3 * (uint64_t)b2);
  uint64_t c2 = (a0 * (uint64_t)b2) ^ (a1 * (uint64_t)b1) ^
                (a2 * (uint64_t)b0) ^ (a3 * (uint64_t)b3);
  uint64_t c3 = (a0 * (uint64_t)b3) ^ (a1 * (uint64_t)b2) ^
                (a2 * (uint64_t)b1) ^ (a3 * (uint64_t)b0);

  return (c0 & UINT64_C(0x1111111111111111)) |
         (c1 & UINT64_C(0x2222222222222222)) |
         (c2 & UINT64_C(0x4444444444444444)) |
         (c3 & UINT64_C(0x8888888888888888));
}

// AWS-LC gcm_nohw.c (verbatim): 64x64 -> 128 carryless multiply (Karatsuba).
static void gcm_mul64_nohw(uint64_t *out_lo, uint64_t *out_hi, uint64_t a,
                           uint64_t b) {
  uint32_t a0 = a & 0xffffffff;
  uint32_t a1 = a >> 32;
  uint32_t b0 = b & 0xffffffff;
  uint32_t b1 = b >> 32;
  // Karatsuba multiplication.
  uint64_t lo = gcm_mul32_nohw(a0, b0);
  uint64_t hi = gcm_mul32_nohw(a1, b1);
  uint64_t mid = gcm_mul32_nohw(a0 ^ a1, b0 ^ b1) ^ lo ^ hi;
  *out_lo = lo ^ (mid << 32);
  *out_hi = hi ^ (mid >> 32);
}

// ---------------------------------------------------------------------------
// AWS-LC gcm_nohw.c (verbatim, modulo H being passed as a uint64_t[2] = {lo,hi}
// instead of a const u128*): POLYVAL multiply + x^-128 Montgomery reduction.
// Computes Xi = Xi * H * x^{-128} mod Q, matching the assembly's convention.
// ---------------------------------------------------------------------------
static void gcm_polyval_nohw(uint64_t Xi[2], const uint64_t H[2]) {
  // Karatsuba multiplication. The product of |Xi| and |H| is stored in |r0|
  // through |r3|. Note there is no byte or bit reversal because we are
  // evaluating POLYVAL.
  uint64_t r0, r1;
  gcm_mul64_nohw(&r0, &r1, Xi[0], H[0]);   // H[0] = H.lo
  uint64_t r2, r3;
  gcm_mul64_nohw(&r2, &r3, Xi[1], H[1]);   // H[1] = H.hi
  uint64_t mid0, mid1;
  gcm_mul64_nohw(&mid0, &mid1, Xi[0] ^ Xi[1], H[1] ^ H[0]);
  mid0 ^= r0 ^ r2;
  mid1 ^= r1 ^ r3;
  r2 ^= mid1;
  r1 ^= mid0;

  // Now we multiply our 256-bit result by x^-128 and reduce. |r2| and |r3|
  // shift into position and we must multiply |r0| and |r1| by x^-128. We have:
  //
  //       1 = x^121 + x^126 + x^127 + x^128
  //  x^-128 = x^-7 + x^-2 + x^-1 + 1
  //
  // This is the GHASH reduction step, but with bits flowing in reverse.
  r1 ^= (r0 << 63) ^ (r0 << 62) ^ (r0 << 57);

  // 1
  r2 ^= r0;
  r3 ^= r1;

  // x^-1
  r2 ^= r0 >> 1;
  r2 ^= r1 << 63;
  r3 ^= r1 >> 1;

  // x^-2
  r2 ^= r0 >> 2;
  r2 ^= r1 << 62;
  r3 ^= r1 >> 2;

  // x^-7
  r2 ^= r0 >> 7;
  r2 ^= r1 << 57;
  r3 ^= r1 >> 7;

  Xi[0] = r2;
  Xi[1] = r3;
}

// ---------------------------------------------------------------------------
// Fold one 16-byte block into the GHASH accumulator Xi:
//   Xi := (Xi XOR block) * H   over GF(2^128), H taken from Htable[0].
// Matches the assembly's big-endian-byte / POLYVAL-limb convention.  Uses the
// existing global reference_wordbytereverse() from test.c.
// ---------------------------------------------------------------------------
static void reference_gcm_ghash_block(uint8_t Xi[16], const uint8_t block[16],
                                      const u128 Htable[16]) {
  uint8_t t[16];
  for (int j = 0; j < 16; j++) t[j] = Xi[j] ^ block[j];
  uint64_t X[2], H_polyval[2];
  X[0] = reference_wordbytereverse(((uint64_t *)t)[1]);
  X[1] = reference_wordbytereverse(((uint64_t *)t)[0]);
  H_polyval[0] = Htable[0].lo;
  H_polyval[1] = Htable[0].hi;
  gcm_polyval_nohw(X, H_polyval);
  ((uint64_t *)Xi)[0] = reference_wordbytereverse(X[1]);
  ((uint64_t *)Xi)[1] = reference_wordbytereverse(X[0]);
}

// ---------------------------------------------------------------------------
// C reference of the gcm_init_v8 assembly: build the 16-slot Htable of twisted
// H powers (H..H^8) and packed Karatsuba mids from the raw hash key H (= AES(0),
// two big-endian 64-bit limbs as AWS-LC loads it).  Bit-exact to the gcm_init_v8
// PMULL assembly (checked over random H).
//
// Twisted H = mulX_POLYVAL(H), in the {lo,hi} POLYVAL limb order the assembly
// uses (lo = H[1], hi = H[0]).  H^k = polyval(H^{k-1}, twisted H).  Slot layout
// (.hi = bytes 0-7, .lo = bytes 8-15); hNk = hN.hi ^ hN.lo:
//   [0]=tw H  [1]=mids(h1k,h2k)  [2]=tw H^2  [3]=tw H^3  [4]=mids(h3k,h4k)
//   [5]=tw H^4 [6]=tw H^5 [7]=mids(h5k,h6k) [8]=tw H^6 [9]=tw H^7
//   [10]=mids(h7k,h8k) [11]=tw H^8 ; [12..15] left as caller's zero-init.
// ---------------------------------------------------------------------------
static void ref_gcm_init_v8(u128 Htable[16], const uint64_t H[2]) {
  uint64_t lo = H[1], hi = H[0];
  uint64_t carry = (uint64_t)((int64_t)hi >> 63);
  hi = (hi << 1) | (lo >> 63);
  lo = lo << 1;
  lo ^= carry & UINT64_C(0x0000000000000001);
  hi ^= carry & UINT64_C(0xc200000000000000);
  uint64_t Hp[2] = { lo, hi };                  // twisted H, {lo,hi}
  uint64_t P[9][2];
  P[1][0] = lo; P[1][1] = hi;
  for (int k = 2; k <= 8; k++) {
    P[k][0] = P[k-1][0]; P[k][1] = P[k-1][1];
    gcm_polyval_nohw(P[k], Hp);                 // P[k] = P[k-1] * H
  }
  #define HMID(k) (P[k][0] ^ P[k][1])
  Htable[ 0].hi = P[1][1]; Htable[ 0].lo = P[1][0];   // twisted H
  Htable[ 1].hi = HMID(1); Htable[ 1].lo = HMID(2);   // mids H, H^2
  Htable[ 2].hi = P[2][1]; Htable[ 2].lo = P[2][0];   // twisted H^2
  Htable[ 3].hi = P[3][1]; Htable[ 3].lo = P[3][0];   // twisted H^3
  Htable[ 4].hi = HMID(3); Htable[ 4].lo = HMID(4);   // mids H^3, H^4
  Htable[ 5].hi = P[4][1]; Htable[ 5].lo = P[4][0];   // twisted H^4
  Htable[ 6].hi = P[5][1]; Htable[ 6].lo = P[5][0];   // twisted H^5
  Htable[ 7].hi = HMID(5); Htable[ 7].lo = HMID(6);   // mids H^5, H^6
  Htable[ 8].hi = P[6][1]; Htable[ 8].lo = P[6][0];   // twisted H^6
  Htable[ 9].hi = P[7][1]; Htable[ 9].lo = P[7][0];   // twisted H^7
  Htable[10].hi = HMID(7); Htable[10].lo = HMID(8);   // mids H^7, H^8
  Htable[11].hi = P[8][1]; Htable[11].lo = P[8][0];   // twisted H^8
  #undef HMID
}

// ---------------------------------------------------------------------------
// C reference of the gcm_gmult_v8 assembly: Xi := Xi * H over GF(2^128), with H
// taken from Htable[0] (the twisted hash key).  This is AWS-LC's gcm_gmult_nohw
// (crypto/fipsmodule/modes/gcm_nohw.c) verbatim: load Xi as two big-endian
// 64-bit limbs (halves swapped), POLYVAL-multiply by Htable[0], store back.
// Bit-exact to the gcm_gmult_v8 PMULL assembly (checked over random inputs).
// ---------------------------------------------------------------------------
static void ref_gcm_gmult_v8(uint8_t Xi[16], const u128 Htable[16]) {
  uint64_t swapped[2];
  swapped[0] = reference_wordbytereverse(((const uint64_t *)Xi)[1]);  // load_u64_be(Xi+8)
  swapped[1] = reference_wordbytereverse(((const uint64_t *)Xi)[0]);  // load_u64_be(Xi)
  uint64_t H[2] = { Htable[0].lo, Htable[0].hi };
  gcm_polyval_nohw(swapped, H);
  ((uint64_t *)Xi)[0] = reference_wordbytereverse(swapped[1]);        // store_u64_be(Xi)
  ((uint64_t *)Xi)[1] = reference_wordbytereverse(swapped[0]);        // store_u64_be(Xi+8)
}

// ---------------------------------------------------------------------------
// Pure-C reference for aes256_gcm: AES-256-CTR encrypt of N blocks (blocks
// 1..N-1 full, last block byte_len in 1..16) plus GHASH accumulation into Xi,
// modelling the partial-block masking and the bif store fixup.
//
//   * counter starts at the 16-byte big-endian value in ivec (caller sets the
//     low byte to 2 = J0+1) and increments its low 32 bits per block;
//   * keystream = AES256(counter); ct = pt XOR keystream;
//   * full blocks: store all 16 bytes, GHASH the full block;
//   * last block: store only byte_len ciphertext bytes (the bytes past the end
//     keep their original out contents = out0), GHASH the ciphertext block
//     ZERO-PADDED to 16 bytes.
//
// out[] must be preloaded with out0 (the original buffer) so the test can check
// that the tail bytes of a partial block are preserved.  Uses the AES from
// ref_aes_xts.c (ref_aes256_encrypt_block: in, out, key).
// ---------------------------------------------------------------------------
static void reference_aes256_gcm_blocks(const uint8_t *pt, int N, int byte_len,
                                        uint8_t *out, uint8_t Xi[16],
                                        const uint8_t ivec[16],
                                        const s2n_bignum_AES_KEY *ek,
                                        const u128 Htable[16]) {
  uint8_t ctr[16];
  memcpy(ctr, ivec, 16);
  for (int k = 0; k < N; k++) {
    uint8_t ks[16];
    ref_aes256_encrypt_block(ctr, ks, ek);
    int nb = (k == N - 1) ? byte_len : 16;       // bytes produced by this block
    uint8_t block[16] = {0};                     // GHASH input (zero-padded)
    for (int j = 0; j < nb; j++) {
      uint8_t c = (uint8_t)(pt[16 * k + j] ^ ks[j]);
      out[16 * k + j] = c;                        // store message bytes
      block[j] = c;                               // and feed into GHASH
    }
    // bytes [nb..15] of a partial last block: out keeps out0; block stays 0.
    reference_gcm_ghash_block(Xi, block, Htable);
    // increment low 32 bits of the big-endian counter
    for (int b = 15; b >= 12; b--) { if (++ctr[b]) break; }
  }
}

#endif  // !__x86_64__
