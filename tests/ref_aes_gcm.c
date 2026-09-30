// Naive reference implementation of AES-GCM (AES-128 and AES-256) for testing
//
// Based directly on:
//   - FIPS 197          (AES block cipher)
//   - NIST SP 800-38D   (GCM mode: GCTR, GHASH, J0, tag)
//   - McGrew & Viega, "The Galois/Counter Mode of Operation (GCM)"
//     (the original GCM submission; source of the test vectors)
//
// Prioritizes clarity and transparency over performance. Everything operates
// on byte arrays in the natural big-endian GHASH convention of the standard;
// there is no use of the optimized "Htable" representation here (that lives in
// ref_gcm_init_htable below, used only to feed the assembly kernel).

// ***************************************************************************
// AES-128 core: FIPS 197 (reuses the S-box / xtime style of ref_aes_xts.c)
// ***************************************************************************

// FIPS 197, Figure 7: S-box substitution values

static const uint8_t ref_gcm_sbox[256] =
{ 0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,
  0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
  0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,
  0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
  0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,
  0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
  0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,
  0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
  0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,
  0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
  0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,
  0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
  0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,
  0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
  0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,
  0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
  0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,
  0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
  0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,
  0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
  0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,
  0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
  0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,
  0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
  0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,
  0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
  0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,
  0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
  0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,
  0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
  0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,
  0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16
};

// FIPS 197, Section 5.2: round constants

static const uint8_t ref_gcm_rcon[11] =
{ 0x00, 0x01, 0x02, 0x04, 0x08, 0x10,
  0x20, 0x40, 0x80, 0x1b, 0x36
};

// FIPS 197, Section 4.2.1: xtime (multiply by {02} in GF(2^8))

static uint8_t ref_gcm_xtime(uint8_t x)
{ return (x << 1) ^ ((x >> 7) * 0x1b);
}

// AES-128 key expansion: FIPS 197, Section 5.2 (Nk=4, Nr=10).
// Produces the encryption key schedule in s2n_bignum_AES_KEY format:
//   rd_key = 11 round keys (176 bytes) as little-endian uint64_t pairs,
//   rounds = 10. This is the layout the assembly kernel reads from "key".

static void ref_aes128_expand_key(const uint8_t key[16],
                                  s2n_bignum_AES_KEY *ek)
{ uint8_t w[176]; // 11 round keys * 16 bytes
  int i;

  memcpy(w, key, 16);

  for (i = 4; i < 44; ++i)
   { uint8_t t[4];
     t[0] = w[4*(i-1)+0]; t[1] = w[4*(i-1)+1];
     t[2] = w[4*(i-1)+2]; t[3] = w[4*(i-1)+3];

     if (i % 4 == 0)
      { // RotWord + SubWord + Rcon
        uint8_t u = t[0];
        t[0] = ref_gcm_sbox[t[1]] ^ ref_gcm_rcon[i/4];
        t[1] = ref_gcm_sbox[t[2]];
        t[2] = ref_gcm_sbox[t[3]];
        t[3] = ref_gcm_sbox[u];
      }

     w[4*i+0] = w[4*(i-4)+0] ^ t[0];
     w[4*i+1] = w[4*(i-4)+1] ^ t[1];
     w[4*i+2] = w[4*(i-4)+2] ^ t[2];
     w[4*i+3] = w[4*(i-4)+3] ^ t[3];
   }

  memcpy(ek->rd_key, w, 176);
  ek->rounds = 10;
}

// AES-128 single block encrypt: FIPS 197, Section 5.1 (Nr=10).

static void ref_aes128_encrypt_block(const uint8_t in[16], uint8_t out[16],
                                     const s2n_bignum_AES_KEY *ek)
{ uint8_t s[16]; // state as column-major 4x4 byte matrix
  const uint8_t *rk = (const uint8_t *)ek->rd_key;
  int r, i;

  // Initial AddRoundKey (round 0)
  for (i = 0; i < 16; ++i) s[i] = in[i] ^ rk[i];

  for (r = 1; r <= 10; ++r)
   { uint8_t t[16];

     // SubBytes
     for (i = 0; i < 16; ++i) t[i] = ref_gcm_sbox[s[i]];

     // ShiftRows (row r shifts left by r positions)
     s[0]  = t[0];  s[1]  = t[5];  s[2]  = t[10]; s[3]  = t[15];
     s[4]  = t[4];  s[5]  = t[9];  s[6]  = t[14]; s[7]  = t[3];
     s[8]  = t[8];  s[9]  = t[13]; s[10] = t[2];  s[11] = t[7];
     s[12] = t[12]; s[13] = t[1];  s[14] = t[6];  s[15] = t[11];

     // MixColumns (skip in final round)
     if (r < 10)
      { for (i = 0; i < 4; ++i)
         { uint8_t a = s[4*i], b = s[4*i+1], c = s[4*i+2], d = s[4*i+3];
           s[4*i]   = ref_gcm_xtime(a) ^ ref_gcm_xtime(b) ^ b ^ c ^ d;
           s[4*i+1] = a ^ ref_gcm_xtime(b) ^ ref_gcm_xtime(c) ^ c ^ d;
           s[4*i+2] = a ^ b ^ ref_gcm_xtime(c) ^ ref_gcm_xtime(d) ^ d;
           s[4*i+3] = ref_gcm_xtime(a) ^ a ^ b ^ c ^ ref_gcm_xtime(d);
         }
      }

     // AddRoundKey
     for (i = 0; i < 16; ++i) s[i] ^= rk[16*r + i];
   }

  memcpy(out, s, 16);
}

// ***************************************************************************
// GHASH: NIST SP 800-38D, Section 6.3
// ***************************************************************************

// Multiplication in GF(2^128) with the GHASH reduction polynomial
// R = 11100001 || 0^120 (i.e. x^128 + x^7 + x^2 + x + 1), per NIST
// SP 800-38D Section 6.3 / Algorithm 1. Blocks are big-endian bit strings:
// bit 0 is the most significant bit of byte 0.

static void ref_ghash_mul(uint8_t z[16], const uint8_t x[16],
                          const uint8_t h[16])
{ uint8_t v[16], r[16];
  int i, j;

  memcpy(v, h, 16);
  memset(r, 0, 16);

  for (i = 0; i < 128; ++i)
   { // If bit i of x (MSB-first) is set, add (XOR) current V into the result
     if ((x[i >> 3] >> (7 - (i & 7))) & 1)
       for (j = 0; j < 16; ++j) r[j] ^= v[j];

     // V = V * x in GF(2^128): right-shift the bit string by one, and if a
     // 1 was shifted out of the low end, reduce by XORing R into the top byte
     int lsb = v[15] & 1;
     for (j = 15; j > 0; --j) v[j] = (uint8_t)((v[j] >> 1) | (v[j-1] << 7));
     v[0] >>= 1;
     if (lsb) v[0] ^= 0xe1;
   }

  memcpy(z, r, 16);
}

// GHASH over a sequence of full 16-byte blocks, folding into accumulator y:
//   y := (y XOR block) * H, for each block.

static void ref_ghash_blocks(uint8_t y[16], const uint8_t *data,
                             size_t nblocks, const uint8_t h[16])
{ size_t b;
  int j;
  for (b = 0; b < nblocks; ++b)
   { for (j = 0; j < 16; ++j) y[j] ^= data[16*b + j];
     ref_ghash_mul(y, y, h);
   }
}

// ***************************************************************************
// Kernel-level reference: mirrors the exact contract of aes128_gcm_enc
// ***************************************************************************
//
// The assembly kernel processes only whole 16-byte blocks. For each block it
//   - forms a keystream block by AES-encrypting the 16-byte counter "ivec",
//   - XORs it with the plaintext to make the ciphertext block,
//   - folds the ciphertext block into the running GHASH accumulator "tag",
//   - increments the counter (GCM inc32: rightmost 32 bits, mod 2^32).
// On return ivec holds the final counter and tag the final GHASH value.
//
// The GHASH subkey is H = AES_K(0^128), exactly as encoded (in optimized form)
// in the Htable that the kernel reads. Here we compute GHASH directly with H,
// independently of that table.

static void ref_gcm_inc32(uint8_t ctr[16])
{ // Increment the rightmost 32 bits (bytes 12..15) as a big-endian counter
  uint32_t c = ((uint32_t)ctr[12] << 24) | ((uint32_t)ctr[13] << 16) |
               ((uint32_t)ctr[14] << 8)  |  (uint32_t)ctr[15];
  c += 1;
  ctr[12] = (uint8_t)(c >> 24); ctr[13] = (uint8_t)(c >> 16);
  ctr[14] = (uint8_t)(c >> 8);  ctr[15] = (uint8_t)c;
}

static void ref_aes128_gcm_enc(const uint8_t *in, uint64_t len_bits,
                                   uint8_t *out, uint8_t tag[16],
                                   uint8_t ivec[16],
                                   const s2n_bignum_AES_KEY *ek)
{ uint8_t h[16], zero[16], ks[16];
  uint64_t byte_len = len_bits >> 3;
  uint64_t nblocks  = byte_len >> 4;
  uint64_t b;
  int j;

  // H = AES_K(0^128)
  memset(zero, 0, 16);
  ref_aes128_encrypt_block(zero, h, ek);

  for (b = 0; b < nblocks; ++b)
   { ref_aes128_encrypt_block(ivec, ks, ek);
     for (j = 0; j < 16; ++j) out[16*b + j] = in[16*b + j] ^ ks[j];

     // Fold the ciphertext block into the GHASH accumulator
     for (j = 0; j < 16; ++j) tag[j] ^= out[16*b + j];
     ref_ghash_mul(tag, tag, h);

     ref_gcm_inc32(ivec);
   }
}

// Reference for the AES-256-GCM encryption kernel. Identical in structure to
// the AES-128 one above; the ONLY difference is that AES-256 is used for
// both the CTR keystream and the GHASH subkey H = AES256_K(0^128). The AES-256
// block cipher and its key schedule are reused verbatim from ref_aes_xts.c
// (ref_aes256_expand_key / ref_aes256_encrypt_block), which is #included before
// this file in the test harness. GCM mode, GHASH and counter handling are
// exactly as for AES-128.
static void ref_aes256_gcm_enc(const uint8_t *in, uint64_t len_bits,
                                      uint8_t *out, uint8_t tag[16],
                                      uint8_t ivec[16],
                                      const s2n_bignum_AES_KEY *ek)
{ uint8_t h[16], zero[16], ks[16];
  uint64_t byte_len = len_bits >> 3;
  uint64_t nblocks  = byte_len >> 4;
  uint64_t b;
  int j;

  // H = AES256_K(0^128)
  memset(zero, 0, 16);
  ref_aes256_encrypt_block(zero, h, ek);

  for (b = 0; b < nblocks; ++b)
   { ref_aes256_encrypt_block(ivec, ks, ek);
     for (j = 0; j < 16; ++j) out[16*b + j] = in[16*b + j] ^ ks[j];

     // Fold the ciphertext block into the GHASH accumulator
     for (j = 0; j < 16; ++j) tag[j] ^= out[16*b + j];
     ref_ghash_mul(tag, tag, h);

     ref_gcm_inc32(ivec);
   }
}

// Reference for the AES-256-GCM decryption kernel. This is ref_aes256_gcm_enc
// with the GHASH folding the INPUT (ciphertext) block rather than the output, the
// only enc/dec difference; AES-256 (14 rounds) drives both the CTR keystream and
// H = AES256_K(0^128). Uses ref_aes256_encrypt_block (from tests/ref_aes_xts.c).
static void ref_aes256_gcm_dec(const uint8_t *in, uint64_t len_bits,
                                      uint8_t *out, uint8_t tag[16],
                                      uint8_t ivec[16],
                                      const s2n_bignum_AES_KEY *ek)
{ uint8_t h[16], zero[16], ks[16];
  uint64_t byte_len = len_bits >> 3;
  uint64_t nblocks  = byte_len >> 4;
  uint64_t b;
  int j;

  // H = AES256_K(0^128)
  memset(zero, 0, 16);
  ref_aes256_encrypt_block(zero, h, ek);

  for (b = 0; b < nblocks; ++b)
   { // Fold the ciphertext (input) block into the GHASH accumulator
     for (j = 0; j < 16; ++j) tag[j] ^= in[16*b + j];
     ref_ghash_mul(tag, tag, h);

     // CTR-decrypt: plaintext = ciphertext XOR AES256_K(counter)
     ref_aes256_encrypt_block(ivec, ks, ek);
     for (j = 0; j < 16; ++j) out[16*b + j] = in[16*b + j] ^ ks[j];

     ref_gcm_inc32(ivec);
   }
}

// Reference for the AES-128-GCM decryption kernel. Identical to the encrypt kernel
// above except that GHASH folds the INPUT (ciphertext) block rather than the
// output (plaintext): in decryption the authenticated data is the ciphertext,
// which is what the kernel reads. The CTR keystream and counter handling are
// unchanged (CTR mode is symmetric).
static void ref_aes128_gcm_dec(const uint8_t *in, uint64_t len_bits,
                                   uint8_t *out, uint8_t tag[16],
                                   uint8_t ivec[16],
                                   const s2n_bignum_AES_KEY *ek)
{ uint8_t h[16], zero[16], ks[16];
  uint64_t byte_len = len_bits >> 3;
  uint64_t nblocks  = byte_len >> 4;
  uint64_t b;
  int j;

  // H = AES_K(0^128)
  memset(zero, 0, 16);
  ref_aes128_encrypt_block(zero, h, ek);

  for (b = 0; b < nblocks; ++b)
   { // Fold the ciphertext (input) block into the GHASH accumulator
     for (j = 0; j < 16; ++j) tag[j] ^= in[16*b + j];
     ref_ghash_mul(tag, tag, h);

     // CTR-decrypt: plaintext = ciphertext XOR AES_K(counter)
     ref_aes128_encrypt_block(ivec, ks, ek);
     for (j = 0; j < 16; ++j) out[16*b + j] = in[16*b + j] ^ ks[j];

     ref_gcm_inc32(ivec);
   }
}

// ***************************************************************************
// Htable construction: feeds the assembly kernel's "Htable" argument
// ***************************************************************************
//
// The kernel reads precomputed powers of H in the OpenSSL gcm_init_v8 layout
// (also formalized as "htable_mem" in common/polyval_ghash.ml). Rather than
// transliterate the SIMD twiddling, we build the table directly from that
// formal specification using GF(2)[x] arithmetic on 128-bit values, where a
// 128-bit value is a pair (lo,hi) of 64-bit words (lo = bits 0..63):
//
//   table base   h  = ghash_twist(H)             (multiply-by-x in the POLYVAL
//                                                  representation, the "C2" form)
//   powers       h_power h k = h, then *h via polyval_dot
//   entry k      stores byteswap128(h_power h k), with packed Karatsuba middle
//                terms karatsuba_mid in the interleaved slots.
//
// where, per common/polyval_ghash.ml and common/polyval.ml,
//   polyval_dot a b      = polyval_reduce_prop3(clmul128 a b)
//   byteswap128 x        = swap the two 64-bit halves of x
//   karatsuba_mid x      = (low64 x) XOR (high64 x)

typedef struct { uint64_t lo, hi; } ref_u128;

// Carry-less (polynomial) multiply of two 64-bit values -> 128-bit (lo,hi)

static void ref_clmul64(uint64_t a, uint64_t b, uint64_t *lo, uint64_t *hi)
{ uint64_t l = 0, h = 0;
  int i;
  for (i = 0; i < 64; ++i)
    if ((b >> i) & 1)
     { l ^= a << i;
       if (i) h ^= a >> (64 - i);
     }
  *lo = l; *hi = h;
}

// Carry-less multiply of two 128-bit values -> 256-bit, as four 64-bit words
// w0..w3 (w0 = bits 0..63). Uses the Karatsuba identity for the middle term.

static void ref_clmul128(ref_u128 a, ref_u128 b, uint64_t w[4])
{ uint64_t t0l, t0h, t2l, t2h, tml, tmh;
  ref_clmul64(a.lo, b.lo, &t0l, &t0h);          // low product
  ref_clmul64(a.hi, b.hi, &t2l, &t2h);          // high product
  ref_clmul64(a.lo ^ a.hi, b.lo ^ b.hi, &tml, &tmh); // (a0+a1)(b0+b1)
  // middle = (a0+a1)(b0+b1) - low - high  (XOR in GF(2))
  tml ^= t0l ^ t2l;
  tmh ^= t0h ^ t2h;
  // result = low + (middle << 64) + (high << 128)
  w[0] = t0l;
  w[1] = t0h ^ tml;
  w[2] = t2l ^ tmh;
  w[3] = t2h;
}

// polyval_reduce_prop3 (common/polyval.ml): Gueron's two-step folding of a
// 256-bit carry-less product down to 128 bits modulo Q(x), the POLYVAL
// modulus, using W = 0xC200000000000000.

static ref_u128 ref_polyval_reduce_prop3(const uint64_t t[4])
{ const uint64_t W = 0xC200000000000000ULL;
  uint64_t a = t[0], b = t[1], c = t[2], d = t[3];
  uint64_t wa_lo, wa_hi, wv_lo, wv_hi, v, u, f, g;
  ref_u128 res;

  ref_clmul64(a, W, &wa_lo, &wa_hi);
  v = b ^ wa_lo;
  u = (c ^ a) ^ wa_hi;
  ref_clmul64(v, W, &wv_lo, &wv_hi);
  f = u ^ wv_lo;
  g = (d ^ v) ^ wv_hi;

  res.lo = f; res.hi = g;
  return res;
}

static ref_u128 ref_polyval_dot(ref_u128 a, ref_u128 b)
{ uint64_t prod[4];
  ref_clmul128(a, b, prod);
  return ref_polyval_reduce_prop3(prod);
}

// ghash_twist (common/polyval_ghash.ml): multiply-by-x mod Q(x), realized as
// a left shift by 1 with conditional reduction by the constant
// 0xC2000000000000000000000000000001 when the top bit is set.

static ref_u128 ref_ghash_twist(ref_u128 h)
{ int carry = (int)(h.hi >> 63);
  ref_u128 r;
  r.hi = (h.hi << 1) | (h.lo >> 63);
  r.lo = (h.lo << 1);
  if (carry)
   { r.lo ^= 0x0000000000000001ULL; // low half of the twist constant
     r.hi ^= 0xC200000000000000ULL; // high half
   }
  return r;
}

// Load 16 bytes (little-endian) into a (lo,hi) 128-bit value, matching the
// formal model's "bytes128" memory read.

static ref_u128 ref_u128_load_le(const uint8_t b[16])
{ ref_u128 r;
  int i;
  r.lo = 0; r.hi = 0;
  for (i = 0; i < 8; ++i) r.lo |= (uint64_t)b[i]   << (8*i);
  for (i = 0; i < 8; ++i) r.hi |= (uint64_t)b[8+i] << (8*i);
  return r;
}

static void ref_u128_store_le(uint8_t b[16], ref_u128 x)
{ int i;
  for (i = 0; i < 8; ++i) b[i]   = (uint8_t)(x.lo >> (8*i));
  for (i = 0; i < 8; ++i) b[8+i] = (uint8_t)(x.hi >> (8*i));
}

static ref_u128 ref_byteswap128(ref_u128 x)
{ ref_u128 r; r.lo = x.hi; r.hi = x.lo; return r;
}

static uint64_t ref_karatsuba_mid(ref_u128 x)
{ return x.lo ^ x.hi;
}

// Build the 192-byte Htable for GHASH subkey H (16 bytes, = AES_K(0)).
// Layout (matching htable_mem in common/polyval_ghash.ml), 12 x 16-byte slots:
//   0:bswap(H^1) 16:mid(H^1,H^2) 32:bswap(H^2) 48:bswap(H^3) 64:mid(H^3,H^4)
//   80:bswap(H^4) 96:bswap(H^5) 112:mid(H^5,H^6) 128:bswap(H^6) 144:bswap(H^7)
//   160:mid(H^7,H^8) 176:bswap(H^8)
// (The kernels only consult slots 0..80, i.e. H^1..H^4 and their midpoints.)

static void ref_gcm_init_htable(uint8_t Htable[192], const uint8_t h_bytes[16])
{ ref_u128 hp[8]; // hp[k] = h_power(base, k) = (twisted H)^(k+1)
  uint8_t h_rev[16];
  int k;

  // The GHASH subkey H is a big-endian 128-bit block (NIST SP 800-38D); the
  // POLYVAL word convention used by the formal model and the multiply is
  // little-endian, so we reverse all 16 bytes before twisting. The table base
  // is then ghash_twist(H) = x * H mod Q(x).
  for (k = 0; k < 16; ++k) h_rev[k] = h_bytes[15 - k];

  hp[0] = ref_ghash_twist(ref_u128_load_le(h_rev));
  for (k = 1; k < 8; ++k) hp[k] = ref_polyval_dot(hp[k-1], hp[0]);

  ref_u128_store_le(Htable + 0,   ref_byteswap128(hp[0]));
  ref_u128_store_le(Htable + 32,  ref_byteswap128(hp[1]));
  ref_u128_store_le(Htable + 48,  ref_byteswap128(hp[2]));
  ref_u128_store_le(Htable + 80,  ref_byteswap128(hp[3]));
  ref_u128_store_le(Htable + 96,  ref_byteswap128(hp[4]));
  ref_u128_store_le(Htable + 128, ref_byteswap128(hp[5]));
  ref_u128_store_le(Htable + 144, ref_byteswap128(hp[6]));
  ref_u128_store_le(Htable + 176, ref_byteswap128(hp[7]));

  { ref_u128 m;
    m.lo = ref_karatsuba_mid(hp[0]); m.hi = ref_karatsuba_mid(hp[1]);
    ref_u128_store_le(Htable + 16, m);
    m.lo = ref_karatsuba_mid(hp[2]); m.hi = ref_karatsuba_mid(hp[3]);
    ref_u128_store_le(Htable + 64, m);
    m.lo = ref_karatsuba_mid(hp[4]); m.hi = ref_karatsuba_mid(hp[5]);
    ref_u128_store_le(Htable + 112, m);
    m.lo = ref_karatsuba_mid(hp[6]); m.hi = ref_karatsuba_mid(hp[7]);
    ref_u128_store_le(Htable + 160, m);
  }
}

// ***************************************************************************
// Full AES-128-GCM (NIST SP 800-38D): used only to validate this reference
// against published known-answer test vectors (McGrew & Viega).
// ***************************************************************************

// GCTR (SP 800-38D Section 6.5): counter-mode over arbitrary-length data,
// starting from initial counter block icb, incrementing the low 32 bits.

static void ref_gctr(const s2n_bignum_AES_KEY *ek, const uint8_t icb[16],
                     const uint8_t *in, uint8_t *out, size_t len)
{ uint8_t cb[16], ks[16];
  size_t off = 0;
  memcpy(cb, icb, 16);
  while (off < len)
   { size_t n = (len - off < 16) ? (len - off) : 16;
     size_t j;
     ref_aes128_encrypt_block(cb, ks, ek);
     for (j = 0; j < n; ++j) out[off + j] = in[off + j] ^ ks[j];
     ref_gcm_inc32(cb);
     off += n;
   }
}

// Append a 64-bit big-endian value into a buffer at position *pos.

static void ref_put_be64(uint8_t *p, uint64_t v)
{ int i;
  for (i = 0; i < 8; ++i) p[i] = (uint8_t)(v >> (8*(7 - i)));
}

// GHASH over AAD then ciphertext, with the trailing length block
// [len(A)]_64 || [len(C)]_64 (in bits), per SP 800-38D Section 6.4.
// Operates on whole and partial blocks (partial blocks are zero-padded).

static void ref_ghash_full(const uint8_t h[16],
                           const uint8_t *aad, size_t aadlen,
                           const uint8_t *ct, size_t ctlen,
                           uint8_t out[16])
{ uint8_t y[16], block[16];
  size_t off;
  int j;

  memset(y, 0, 16);

  for (off = 0; off < aadlen; off += 16)
   { size_t n = (aadlen - off < 16) ? (aadlen - off) : 16;
     memset(block, 0, 16);
     memcpy(block, aad + off, n);
     for (j = 0; j < 16; ++j) y[j] ^= block[j];
     ref_ghash_mul(y, y, h);
   }

  for (off = 0; off < ctlen; off += 16)
   { size_t n = (ctlen - off < 16) ? (ctlen - off) : 16;
     memset(block, 0, 16);
     memcpy(block, ct + off, n);
     for (j = 0; j < 16; ++j) y[j] ^= block[j];
     ref_ghash_mul(y, y, h);
   }

  memset(block, 0, 16);
  ref_put_be64(block + 0, (uint64_t)aadlen * 8);
  ref_put_be64(block + 8, (uint64_t)ctlen * 8);
  for (j = 0; j < 16; ++j) y[j] ^= block[j];
  ref_ghash_mul(y, y, h);

  memcpy(out, y, 16);
}

// AES-128-GCM authenticated encryption (SP 800-38D Section 7.1).
// Produces ciphertext ct (same length as pt) and a 16-byte tag.
// Supports a 96-bit IV (the common case, used by the test vectors) and the
// general case where J0 itself is computed via GHASH.

static void ref_aes128_gcm_encrypt(const uint8_t key[16],
                                   const uint8_t *iv, size_t ivlen,
                                   const uint8_t *aad, size_t aadlen,
                                   const uint8_t *pt, size_t ptlen,
                                   uint8_t *ct, uint8_t tag[16])
{ s2n_bignum_AES_KEY ek;
  uint8_t h[16], zero[16], j0[16], icb[16], s[16], ej0[16];
  int j;

  ref_aes128_expand_key(key, &ek);

  memset(zero, 0, 16);
  ref_aes128_encrypt_block(zero, h, &ek); // H = AES_K(0)

  // Compute the pre-counter block J0 (SP 800-38D Section 7.1, step 2)
  if (ivlen == 12)
   { memcpy(j0, iv, 12);
     j0[12] = 0; j0[13] = 0; j0[14] = 0; j0[15] = 1;
   }
  else
   { // J0 = GHASH_H(IV || 0^s || [len(IV)]_64)
     ref_ghash_full(h, NULL, 0, iv, ivlen, j0);
     // ref_ghash_full appends [0]_64 || [len(IV)]_64; for J0 the standard uses
     // a single length block [0]_64 || [len(IV)]_64 after the (padded) IV,
     // which is exactly GHASH with empty AAD over the IV as "ciphertext".
   }

  // C = GCTR_K(inc32(J0), P)
  memcpy(icb, j0, 16);
  ref_gcm_inc32(icb);
  ref_gctr(&ek, icb, pt, ct, ptlen);

  // S = GHASH_H(A, C); T = MSB_128(GCTR_K(J0, S)) = AES_K(J0) XOR S
  ref_ghash_full(h, aad, aadlen, ct, ptlen, s);
  ref_aes128_encrypt_block(j0, ej0, &ek);
  for (j = 0; j < 16; ++j) tag[j] = ej0[j] ^ s[j];
}
