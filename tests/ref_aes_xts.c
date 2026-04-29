// Naive reference implementation of AES-256-XTS for testing
//
// Based directly on FIPS 197 (AES) and IEEE 1619 (XTS-AES).
// Prioritizes clarity and transparency over performance.

// ***************************************************************************
// AES-256 core: FIPS 197 tables and operations
// ***************************************************************************

// FIPS 197, Figure 7: S-box substitution values

static const uint8_t ref_aes_sbox[256] =
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

// FIPS 197, Figure 14: inverse S-box substitution values

static const uint8_t ref_aes_inv_sbox[256] =
{ 0x52,0x09,0x6a,0xd5,0x30,0x36,0xa5,0x38,
  0xbf,0x40,0xa3,0x9e,0x81,0xf3,0xd7,0xfb,
  0x7c,0xe3,0x39,0x82,0x9b,0x2f,0xff,0x87,
  0x34,0x8e,0x43,0x44,0xc4,0xde,0xe9,0xcb,
  0x54,0x7b,0x94,0x32,0xa6,0xc2,0x23,0x3d,
  0xee,0x4c,0x95,0x0b,0x42,0xfa,0xc3,0x4e,
  0x08,0x2e,0xa1,0x66,0x28,0xd9,0x24,0xb2,
  0x76,0x5b,0xa2,0x49,0x6d,0x8b,0xd1,0x25,
  0x72,0xf8,0xf6,0x64,0x86,0x68,0x98,0x16,
  0xd4,0xa4,0x5c,0xcc,0x5d,0x65,0xb6,0x92,
  0x6c,0x70,0x48,0x50,0xfd,0xed,0xb9,0xda,
  0x5e,0x15,0x46,0x57,0xa7,0x8d,0x9d,0x84,
  0x90,0xd8,0xab,0x00,0x8c,0xbc,0xd3,0x0a,
  0xf7,0xe4,0x58,0x05,0xb8,0xb3,0x45,0x06,
  0xd0,0x2c,0x1e,0x8f,0xca,0x3f,0x0f,0x02,
  0xc1,0xaf,0xbd,0x03,0x01,0x13,0x8a,0x6b,
  0x3a,0x91,0x11,0x41,0x4f,0x67,0xdc,0xea,
  0x97,0xf2,0xcf,0xce,0xf0,0xb4,0xe6,0x73,
  0x96,0xac,0x74,0x22,0xe7,0xad,0x35,0x85,
  0xe2,0xf9,0x37,0xe8,0x1c,0x75,0xdf,0x6e,
  0x47,0xf1,0x1a,0x71,0x1d,0x29,0xc5,0x89,
  0x6f,0xb7,0x62,0x0e,0xaa,0x18,0xbe,0x1b,
  0xfc,0x56,0x3e,0x4b,0xc6,0xd2,0x79,0x20,
  0x9a,0xdb,0xc0,0xfe,0x78,0xcd,0x5a,0xf4,
  0x1f,0xdd,0xa8,0x33,0x88,0x07,0xc7,0x31,
  0xb1,0x12,0x10,0x59,0x27,0x80,0xec,0x5f,
  0x60,0x51,0x7f,0xa9,0x19,0xb5,0x4a,0x0d,
  0x2d,0xe5,0x7a,0x9f,0x93,0xc9,0x9c,0xef,
  0xa0,0xe0,0x3b,0x4d,0xae,0x2a,0xf5,0xb0,
  0xc8,0xeb,0xbb,0x3c,0x83,0x53,0x99,0x61,
  0x17,0x2b,0x04,0x7e,0xba,0x77,0xd6,0x26,
  0xe1,0x69,0x14,0x63,0x55,0x21,0x0c,0x7d
};

// FIPS 197, Section 5.2: round constants

static const uint8_t ref_aes_rcon[11] =
{ 0x00, 0x01, 0x02, 0x04, 0x08, 0x10,
  0x20, 0x40, 0x80, 0x1b, 0x36
};

// ***************************************************************************
// GF(2^8) arithmetic for MixColumns / InvMixColumns
// ***************************************************************************

// FIPS 197, Section 4.2.1: xtime (multiply by {02} in GF(2^8))

static uint8_t ref_aes_xtime(uint8_t x)
{ return (x << 1) ^ ((x >> 7) * 0x1b);
}

// General multiply in GF(2^8) with reduction polynomial x^8+x^4+x^3+x+1

static uint8_t ref_aes_gfmul(uint8_t a, uint8_t b)
{ uint8_t r = 0;
  int i;
  for (i = 0; i < 8; ++i)
   { if (b & 1) r ^= a;
     a = ref_aes_xtime(a);
     b >>= 1;
   }
  return r;
}

// ***************************************************************************
// AES-256 key expansion: FIPS 197, Section 5.2 (Nk=8, Nr=14)
// ***************************************************************************

// Produce encryption key schedule in s2n_bignum_AES_KEY format:
//   rd_key[0..29] = 15 round keys stored as little-endian uint64_t pairs
//   rounds = 13 (the assembly convention: Nr - 1)

static void ref_aes256_expand_key(const uint8_t key[32],
                                  s2n_bignum_AES_KEY *ek)
{ uint8_t w[240]; // 15 round keys * 16 bytes
  int i;

  // First 32 bytes are the original key
  memcpy(w, key, 32);

  // Expand: FIPS 197 key expansion for Nk=8
  for (i = 8; i < 60; ++i)
   { uint8_t t[4];
     t[0] = w[4*(i-1)+0]; t[1] = w[4*(i-1)+1];
     t[2] = w[4*(i-1)+2]; t[3] = w[4*(i-1)+3];

     if (i % 8 == 0)
      { // RotWord + SubWord + Rcon
        uint8_t u = t[0];
        t[0] = ref_aes_sbox[t[1]] ^ ref_aes_rcon[i/8];
        t[1] = ref_aes_sbox[t[2]];
        t[2] = ref_aes_sbox[t[3]];
        t[3] = ref_aes_sbox[u];
      }
     else if (i % 8 == 4)
      { // SubWord only (extra step for Nk=8)
        t[0] = ref_aes_sbox[t[0]]; t[1] = ref_aes_sbox[t[1]];
        t[2] = ref_aes_sbox[t[2]]; t[3] = ref_aes_sbox[t[3]];
      }

     w[4*i+0] = w[4*(i-8)+0] ^ t[0];
     w[4*i+1] = w[4*(i-8)+1] ^ t[1];
     w[4*i+2] = w[4*(i-8)+2] ^ t[2];
     w[4*i+3] = w[4*(i-8)+3] ^ t[3];
   }

  // Copy into rd_key as little-endian uint64_t values
  memcpy(ek->rd_key, w, 240);
  ek->rounds = 13;
}

// Produce decryption key schedule: round keys reversed, InvMixColumns
// applied to the middle ones (FIPS 197, Section 5.3.5 equivalent inverse).
// This is what the assembly decrypt function expects.

static void ref_aes256_expand_decrypt_key(const uint8_t key[32],
                                          s2n_bignum_AES_KEY *dk)
{ uint8_t ek_bytes[240], dk_bytes[240];
  s2n_bignum_AES_KEY ek;
  int r, i;

  // First produce the standard encryption schedule
  ref_aes256_expand_key(key, &ek);
  memcpy(ek_bytes, ek.rd_key, 240);

  // Reverse round keys: dk[r] = ek[14-r]
  for (r = 0; r <= 14; ++r)
    memcpy(dk_bytes + 16*r, ek_bytes + 16*(14-r), 16);

  // Apply InvMixColumns to the middle round keys (dk[1] through dk[13])
  for (r = 1; r <= 13; ++r)
   { uint8_t *rk = dk_bytes + 16*r;
     for (i = 0; i < 4; ++i)
      { uint8_t a = rk[4*i], b = rk[4*i+1], c = rk[4*i+2], d = rk[4*i+3];
        rk[4*i]   = ref_aes_gfmul(0x0e,a) ^ ref_aes_gfmul(0x0b,b) ^
                     ref_aes_gfmul(0x0d,c) ^ ref_aes_gfmul(0x09,d);
        rk[4*i+1] = ref_aes_gfmul(0x09,a) ^ ref_aes_gfmul(0x0e,b) ^
                     ref_aes_gfmul(0x0b,c) ^ ref_aes_gfmul(0x0d,d);
        rk[4*i+2] = ref_aes_gfmul(0x0d,a) ^ ref_aes_gfmul(0x09,b) ^
                     ref_aes_gfmul(0x0e,c) ^ ref_aes_gfmul(0x0b,d);
        rk[4*i+3] = ref_aes_gfmul(0x0b,a) ^ ref_aes_gfmul(0x0d,b) ^
                     ref_aes_gfmul(0x09,c) ^ ref_aes_gfmul(0x0e,d);
      }
   }

  memcpy(dk->rd_key, dk_bytes, 240);
  dk->rounds = 13;
}

// ***************************************************************************
// AES-256 single block encrypt: FIPS 197, Section 5.1
// ***************************************************************************

static void ref_aes256_encrypt_block(const uint8_t in[16], uint8_t out[16],
                                     const s2n_bignum_AES_KEY *ek)
{ uint8_t s[16]; // state as column-major 4x4 byte matrix
  const uint8_t *rk = (const uint8_t *)ek->rd_key;
  int r, i;

  // Initial AddRoundKey (round 0)
  for (i = 0; i < 16; ++i) s[i] = in[i] ^ rk[i];

  for (r = 1; r <= 14; ++r)
   { uint8_t t[16];

     // SubBytes
     for (i = 0; i < 16; ++i) t[i] = ref_aes_sbox[s[i]];

     // ShiftRows (row r shifts left by r positions)
     s[0]  = t[0];  s[1]  = t[5];  s[2]  = t[10]; s[3]  = t[15];
     s[4]  = t[4];  s[5]  = t[9];  s[6]  = t[14]; s[7]  = t[3];
     s[8]  = t[8];  s[9]  = t[13]; s[10] = t[2];  s[11] = t[7];
     s[12] = t[12]; s[13] = t[1];  s[14] = t[6];  s[15] = t[11];

     // MixColumns (skip in final round)
     if (r < 14)
      { for (i = 0; i < 4; ++i)
         { uint8_t a = s[4*i], b = s[4*i+1], c = s[4*i+2], d = s[4*i+3];
           s[4*i]   = ref_aes_xtime(a) ^ ref_aes_xtime(b) ^ b ^ c ^ d;
           s[4*i+1] = a ^ ref_aes_xtime(b) ^ ref_aes_xtime(c) ^ c ^ d;
           s[4*i+2] = a ^ b ^ ref_aes_xtime(c) ^ ref_aes_xtime(d) ^ d;
           s[4*i+3] = ref_aes_xtime(a) ^ a ^ b ^ c ^ ref_aes_xtime(d);
         }
      }

     // AddRoundKey
     for (i = 0; i < 16; ++i) s[i] ^= rk[16*r + i];
   }

  memcpy(out, s, 16);
}

// ***************************************************************************
// AES-256 single block decrypt: FIPS 197, Section 5.3
// Uses the standard encryption key schedule (applies keys in reverse order).
// ***************************************************************************

static void ref_aes256_decrypt_block(const uint8_t in[16], uint8_t out[16],
                                     const s2n_bignum_AES_KEY *ek)
{ uint8_t s[16];
  const uint8_t *rk = (const uint8_t *)ek->rd_key;
  int r, i;

  // Initial AddRoundKey (round 14)
  for (i = 0; i < 16; ++i) s[i] = in[i] ^ rk[14*16 + i];

  for (r = 13; r >= 0; --r)
   { uint8_t t[16];

     // InvShiftRows
     t[0]  = s[0];  t[5]  = s[1];  t[10] = s[2];  t[15] = s[3];
     t[4]  = s[4];  t[9]  = s[5];  t[14] = s[6];  t[3]  = s[7];
     t[8]  = s[8];  t[13] = s[9];  t[2]  = s[10]; t[7]  = s[11];
     t[12] = s[12]; t[1]  = s[13]; t[6]  = s[14]; t[11] = s[15];

     // InvSubBytes
     for (i = 0; i < 16; ++i) s[i] = ref_aes_inv_sbox[t[i]];

     // AddRoundKey
     for (i = 0; i < 16; ++i) s[i] ^= rk[16*r + i];

     // InvMixColumns (skip in round 0)
     if (r > 0)
      { for (i = 0; i < 4; ++i)
         { uint8_t a = s[4*i], b = s[4*i+1], c = s[4*i+2], d = s[4*i+3];
           s[4*i]   = ref_aes_gfmul(0x0e,a) ^ ref_aes_gfmul(0x0b,b) ^
                       ref_aes_gfmul(0x0d,c) ^ ref_aes_gfmul(0x09,d);
           s[4*i+1] = ref_aes_gfmul(0x09,a) ^ ref_aes_gfmul(0x0e,b) ^
                       ref_aes_gfmul(0x0b,c) ^ ref_aes_gfmul(0x0d,d);
           s[4*i+2] = ref_aes_gfmul(0x0d,a) ^ ref_aes_gfmul(0x09,b) ^
                       ref_aes_gfmul(0x0e,c) ^ ref_aes_gfmul(0x0b,d);
           s[4*i+3] = ref_aes_gfmul(0x0b,a) ^ ref_aes_gfmul(0x0d,b) ^
                       ref_aes_gfmul(0x09,c) ^ ref_aes_gfmul(0x0e,d);
         }
      }
   }

  memcpy(out, s, 16);
}

// ***************************************************************************
// XTS tweak: GF(2^128) doubling (IEEE 1619, Section 5.2)
// ***************************************************************************

// Multiply tweak by the primitive element x in GF(2^128)
// with reduction polynomial x^128 + x^7 + x^2 + x + 1.
// Tweak is treated as a little-endian 128-bit value.

static void ref_gf128_mul_x(uint8_t t[16])
{ int i;
  uint8_t carry = 0, next_carry;
  for (i = 0; i < 16; ++i)
   { next_carry = t[i] >> 7;
     t[i] = (t[i] << 1) | carry;
     carry = next_carry;
   }
  // If the top bit was set, XOR with the reduction constant 0x87
  // (representing x^7 + x^2 + x + 1, stored in byte 0 since little-endian)
  t[0] ^= carry * 0x87;
}

// ***************************************************************************
// AES-256-XTS encrypt: IEEE 1619, Section 5.4.1
// ***************************************************************************

// Takes raw 32-byte keys (not pre-expanded).
// Handles ciphertext stealing for non-block-aligned lengths.

static void ref_aes_xts_encrypt(const uint8_t *in, uint8_t *out, size_t len,
                                const uint8_t key1[32],
                                const uint8_t key2[32],
                                const uint8_t iv[16])
{ s2n_bignum_AES_KEY ek1, ek2;
  uint8_t tweak[16], block[16];
  size_t nblocks, tail, i, j;

  if (len < 16) return; // XTS requires at least one full block

  ref_aes256_expand_key(key1, &ek1);
  ref_aes256_expand_key(key2, &ek2);

  // Encrypt IV with key2 to produce initial tweak
  ref_aes256_encrypt_block(iv, tweak, &ek2);

  tail = len % 16;
  nblocks = len / 16;
  if (tail != 0) --nblocks; // reserve last full block for stealing

  // Encrypt full blocks with sequential tweaks
  for (i = 0; i < nblocks; ++i)
   { for (j = 0; j < 16; ++j) block[j] = in[16*i + j] ^ tweak[j];
     ref_aes256_encrypt_block(block, block, &ek1);
     for (j = 0; j < 16; ++j) out[16*i + j] = block[j] ^ tweak[j];
     ref_gf128_mul_x(tweak);
   }

  // Ciphertext stealing for partial final block (IEEE 1619 Section 5.4.1)
  if (tail != 0)
   { uint8_t cc[16]; // CC = encryption of last full plaintext block

     // Step 1: Encrypt the last full plaintext block with current tweak
     for (j = 0; j < 16; ++j)
       block[j] = in[16*nblocks + j] ^ tweak[j];
     ref_aes256_encrypt_block(block, cc, &ek1);
     for (j = 0; j < 16; ++j) cc[j] ^= tweak[j];

     // Step 2: Advance tweak for the composite block
     ref_gf128_mul_x(tweak);

     // Step 3: Steal - the partial final ciphertext is first 'tail' bytes of CC
     //         Build composite plaintext from tail input + rest of CC
     for (j = 0; j < 16; ++j) block[j] = cc[j];
     for (j = 0; j < tail; ++j)
      { out[16*nblocks + 16 + j] = cc[j];          // C[m]: partial final output
        block[j] = in[16*nblocks + 16 + j];         // steal from partial input
      }

     // Step 4: Encrypt composite block with the advanced tweak
     for (j = 0; j < 16; ++j) block[j] ^= tweak[j];
     ref_aes256_encrypt_block(block, block, &ek1);
     for (j = 0; j < 16; ++j) out[16*nblocks + j] = block[j] ^ tweak[j];
   }
}

// ***************************************************************************
// AES-256-XTS decrypt: IEEE 1619, Section 5.4.2
// ***************************************************************************

// Takes raw 32-byte keys (not pre-expanded).
// Uses the standard encryption key schedule internally for ref_aes256_decrypt_block.

static void ref_aes_xts_decrypt(const uint8_t *in, uint8_t *out, size_t len,
                                const uint8_t key1[32],
                                const uint8_t key2[32],
                                const uint8_t iv[16])
{ s2n_bignum_AES_KEY ek1, ek2;
  uint8_t tweak[16], block[16];
  size_t nblocks, tail, i, j;

  if (len < 16) return;

  ref_aes256_expand_key(key1, &ek1);  // encryption schedule for decrypt_block
  ref_aes256_expand_key(key2, &ek2);

  // Encrypt IV with key2 to produce initial tweak (always encrypt, per IEEE 1619)
  ref_aes256_encrypt_block(iv, tweak, &ek2);

  tail = len % 16;
  nblocks = len / 16;
  if (tail != 0) --nblocks; // reserve last full block for stealing

  // Decrypt full blocks with sequential tweaks
  for (i = 0; i < nblocks; ++i)
   { for (j = 0; j < 16; ++j) block[j] = in[16*i + j] ^ tweak[j];
     ref_aes256_decrypt_block(block, block, &ek1);
     for (j = 0; j < 16; ++j) out[16*i + j] = block[j] ^ tweak[j];
     ref_gf128_mul_x(tweak);
   }

  // Ciphertext stealing for partial final block (IEEE 1619 Section 5.4.2)
  if (tail != 0)
   { uint8_t tweak_m1[16]; // T[m-1]: tweak for penultimate position
     uint8_t tweak_m[16];  // T[m]:   tweak for last (partial) position
     uint8_t pp[16];       // PP: decryption of second-to-last ciphertext block

     // The current tweak is T[m-1] (for block index nblocks)
     memcpy(tweak_m1, tweak, 16);
     memcpy(tweak_m, tweak, 16);
     ref_gf128_mul_x(tweak_m);

     // Step 1: Decrypt C[m-1] with T[m] (NOT T[m-1]!) to get PP
     for (j = 0; j < 16; ++j)
       block[j] = in[16*nblocks + j] ^ tweak_m[j];
     ref_aes256_decrypt_block(block, pp, &ek1);
     for (j = 0; j < 16; ++j) pp[j] ^= tweak_m[j];

     // Step 2: Steal - P[m] is first 'tail' bytes of PP
     //         Build composite ciphertext from partial input + rest of PP
     for (j = 0; j < 16; ++j) block[j] = pp[j];
     for (j = 0; j < tail; ++j)
      { out[16*nblocks + 16 + j] = pp[j];           // P[m]: partial final output
        block[j] = in[16*nblocks + 16 + j];          // steal from partial input
      }

     // Step 3: Decrypt composite block with T[m-1]
     for (j = 0; j < 16; ++j) block[j] ^= tweak_m1[j];
     ref_aes256_decrypt_block(block, block, &ek1);
     for (j = 0; j < 16; ++j) out[16*nblocks + j] = block[j] ^ tweak_m1[j];
   }
}
