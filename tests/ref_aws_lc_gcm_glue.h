// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
// Surrounding glue for the byte-verbatim AWS-LC functions in test.c.
// The generic upstream mode receives AES block/CTR callbacks; those callbacks
// use the existing scalar C AES primitive. GHASH and GCM sequencing are AWS-LC C.
// No body copied from AWS-LC is edited or renamed: aliases live here.

#ifndef S2N_TEST_AWS_LC_GCM_GLUE_H
#define S2N_TEST_AWS_LC_GCM_GLUE_H

#define AES_KEY s2n_bignum_AES_KEY
typedef unsigned __int128 uint128_t;
typedef struct { uint64_t hi,lo; } u128;
typedef void (*block128_f)(const uint8_t[16], uint8_t[16], const AES_KEY *);
typedef void (*ctr128_f)(const uint8_t *, uint8_t *, size_t,
                         const AES_KEY *, const uint8_t[16]);
typedef void (*gmult_func)(uint8_t[16], const u128[16]);
typedef void (*ghash_func)(uint8_t[16], const u128[16], const uint8_t *, size_t);
typedef struct {
  u128 Htable[16];
  gmult_func gmult;
  ghash_func ghash;
  block128_f block;
  unsigned use_hw_gcm_crypt:1;
} GCM128_KEY;
typedef struct {
  uint8_t Yi[16], EKi[16], EK0[16];
  struct { uint64_t aad, msg; } len;
  uint8_t Xi[16];
  GCM128_KEY gcm_key;
  unsigned mres, ares;
} GCM128_CONTEXT;

#define OPENSSL_memcpy memcpy
#define CRYPTO_bswap4 __builtin_bswap32
#define CRYPTO_bswap8 __builtin_bswap64
#define CRYPTO_load_u32_be aws_lc_load_u32_be
#define CRYPTO_store_u32_be aws_lc_store_u32_be
#define CRYPTO_load_u64_be aws_lc_load_u64_be
#define CRYPTO_store_u64_be aws_lc_store_u64_be
#define gcm_mul64_nohw aws_lc_gcm_mul64_nohw
#define gcm_init_nohw aws_lc_gcm_init_nohw
#define gcm_polyval_nohw aws_lc_gcm_polyval_nohw
#define gcm_gmult_nohw aws_lc_gcm_gmult_nohw
#define gcm_ghash_nohw aws_lc_gcm_ghash_nohw
#define hw_gcm_encrypt aws_lc_hw_gcm_encrypt
#define CRYPTO_gcm128_encrypt_ctr32 aws_lc_gcm128_encrypt_ctr32

#define GCM_FUNCREF 1
#define HW_GCM 1
#define GHASH_CHUNK (3 * 1024)
#define GCM_MUL(ctx, Xi) (*gcm_gmult_p)((ctx)->Xi, (ctx)->gcm_key.Htable)
#define GHASH(ctx, in, len) \
  (*gcm_ghash_p)((ctx)->Xi, (ctx)->gcm_key.Htable, in, len)
static const size_t kSizeTWithoutLower4Bits = (size_t)-16;

// Dispatch coverage is deliberately restricted to the upstream AES128 8x
// branch: tests request hardware only at >=256 bytes with rounds == 10.
#define CRYPTO_is_ARMv8_GCM_8x_capable() 1
#define aesv8_gcm_8x_enc_128(in, len, out, Xi, iv, key, ht) \
  aes128_gcm_enc_alt(in, len, out, (uint64_t *)(void *)(Xi), iv, key, \
                     (const uint64_t *)(const void *)(ht))
#define aesv8_gcm_8x_enc_192(in, len, out, Xi, iv, key, ht) abort()
#define aesv8_gcm_8x_enc_256(in, len, out, Xi, iv, key, ht) abort()
#define aes_gcm_enc_kernel(in, len, out, Xi, iv, key, ht) abort()

#endif
