# ML-KEM in assembly: the mlkem-native API for AArch64

This directory has an implementation in assembly of the ML-KEM functions
of [mlkem-native](https://github.com/pq-code-package/mlkem-native)'s API,
for all three parameter sets:

    int mlkemL_keypair_derand(uint8_t *pk, uint8_t *sk, const uint8_t *coins)
    int mlkemL_enc_derand(uint8_t *ct, uint8_t *ss, const uint8_t *pk,
                          const uint8_t *coins)
    int mlkemL_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *sk)
    int mlkemL_check_pk(const uint8_t *pk)
    int mlkemL_check_sk(const uint8_t *sk)

for L = 512, 768, 1024, with the same results as mlkem-native's (return
values included). It is written in the style of s2n-bignum, with proofs
in HOL Light of the correctness and the constant-time and memory safety
of all its functions: the new leaves, and those listed under Proofs
below. The randomized `mlkemL_keypair` and `mlkemL_enc` are not here,
since they need a source of randomness: as in mlkem-native, they get 64
or 32 random bytes, call the deterministic function and zero the bytes.

## Structure

The work is in three layers.

 - The leaves, in `../mlkem`, standalone s2n-bignum-style functions, each
   with its own specification in its header comment:
    - mlkem-native's verified kernels, either as already in s2n-bignum
      (`mlkem_mulcache_compute`, `mlkem_reduce`, `mlkem_tomont`) or as
      `_alt` copies of mlkem-native's current code, which is faster on
      Neoverse-V2 (`mlkem_ntt_alt`, `mlkem_intt_alt`, `mlkem_tobytes_alt`,
      `mlkem_basemul_k{2,3,4}_alt`; mlkem-native has HOL Light proofs of
      these); and s2n-bignum's Keccak-f1600 kernels `sha3_keccak_f1600`
      (x1) and `sha3_keccak4_f1600_alt2` (x4);
    - new ones for what mlkem-native does in C: `mlkem_cbd2`,
      `mlkem_cbd3`, `mlkem_compress_d{4,5,10,11}`,
      `mlkem_decompress_d{4,5,10,11}`, `mlkem_frombytes`,
      `mlkem_frommsg`, `mlkem_tomsg`, `mlkem_check_encoding` (the
      modulus check of an encapsulation key), `mlkem_add_reduce`,
      `mlkem_sub_reduce`, and a faster rejection sampler
      `mlkem_rej_uniform_alt_VARIABLE_TIME` that appends to a partial
      result.
 - The middle layer, here: `mlkem_gen_matrix` (the matrix, with hash jobs
   and noise in the spare lanes of the x4 permutation), `mlkem_getnoise`
   (noise sampling in the x4 lanes), `mlkem_hash_h` and `mlkem_hash_g`
   (SHA3-256 and SHA3-512 with the x1 permutation).
 - The API: `mlkem_kem_template.S`, included by `mlkem512.S`,
   `mlkem768.S` and `mlkem1024.S` after they define the parameter set.
   Besides the API functions it has `mlkemL_pke_encrypt` and
   `mlkemL_pke_decrypt`, shared by encapsulation and decapsulation.

The functions of the upper layers call others (`bl`), so their proofs are
on the linked image of all the functions involved. The tables of
constants (the zetas and the rejection sampling table taken unchanged
from mlkem-native, and the Keccak round constants) are one read-only
block, `mlkem_native2_constants` (`mlkem_native2_constants.S`, with the
layout in `mlkem_native2_consts.h`), whose address the API functions take
with `adrp`/`add`, as `curve25519_x25519base` does for its table, and pass
to the functions below.

## Building

None of these files is in the `OBJ` list of `../Makefile` yet, so they
are not in `libs2nbignum.a` (nor in `make proofs`); the objects are built
with the usual rule, e.g. `make mlkem_native2/mlkem768.o` in `arm`. The
API for one parameter set, `mlkemL.o`, needs `mlkem_gen_matrix.o`,
`mlkem_getnoise.o`, `mlkem_hash_h.o`, `mlkem_hash_g.o` and
`mlkem_native2_constants.o` from here, the new leaves in `../mlkem` (not
all of them at each level), `mlkem_mulcache_compute`, `mlkem_reduce` and
`mlkem_tomont` in `../mlkem`, and `sha3_keccak_f1600` and
`sha3_keccak4_f1600_alt2` in `../sha3`. Every entry point has a BTI
landing pad (`AARCH64_VALID_CALL_TARGET`). The variants of the
directives for Apple platforms are there but have not been tried.

## Proofs

The functions here call others, so their proofs are about the image of
all the functions involved: the objects in `MLKEM_NATIVE2_IMAGE_OBJ` of
`../Makefile`, linked at address 0 by `mlkem_native2_image.ld` into
`mlkem_native2_image.elf` (`make mlkem_native2/mlkem_native2_image.elf`
in `arm`, with GNU ld, or `aarch64-linux-gnu-ld` when cross-assembling).
`../proofs/mlkem_native2_image.ml` reads it as one byte list and installs
the names of its symbols as in `../../common/layout.ml`, so that a proof
refers to the function f or the label f in the image as `pc + f`; the
theorems for the leaves and the Keccak permutations, about their own
code, are used for the same code in the image. The theorems are thus for
this layout of the image, and are checked again when it changes.

`make mlkem_native2_proofs` in `arm` runs the proofs:

- `mlkem_hash_h` (SHA3-256) and `mlkem_hash_g` (SHA3-512), against
  `sha3_256` and `sha3_512` of `../../common/fips202/fips202.ml`, with
  their constant-time and memory safety (`../proofs/mlkem_hash_h.ml`,
  `../proofs/mlkem_hash_g.ml`, and `../proofs/utils/mlkem_native2_sponge.ml`
  for the sponge and the use of `sha3_keccak_f1600`).
- `mlkem_gen_matrix` for the nine configurations that the API uses (k = 2,
  3, 4 in key generation, encapsulation and decapsulation, with their hash
  jobs and noise), against `mlkem_sample_ntt`, `sha3_256`, `shake256` and
  the coefficients of `mlkem_cbd` (`../proofs/mlkem_gen_matrix_k2.ml`,
  `_k3.ml` and `_k4.ml`, one file for each k as each level of the API needs
  only its own, with the code and the common parts in
  `../proofs/mlkem_gen_matrix.ml`, and
  `../proofs/utils/mlkem_native2_matrix.ml` for SampleNTT as the rejection
  sampling of whole blocks of SHAKE128 output, the seeds and the hash jobs
  as states of lanes, and the sponge by blocks, with the lemmas on FIPS 203
  of the proofs of mlkem-native's compiled C in
  `../proofs/utils/mlkem_native_fips203.ml`). Its constant-time and memory
  safety, with the events a function of the addresses and of the public seed
  rho (and, for decapsulation, whose hash check branches on it, the digest
  H(ek) of the first hash job as a result), are in
  `../proofs/mlkem_gen_matrix_k2_safe.ml`, `_k3_safe.ml` and `_k4_safe.ml`,
  with the common parts in `../proofs/utils/mlkem_native2_gm_safe.ml`, the
  tools for the callees in `../proofs/utils/mlkem_native2_safety.ml`, and
  theorems of correctness and safety in one for the callees on whose results
  the later events depend, the Keccak permutations and the rejection sampler
  (`../proofs/utils/mlkem_native2_keccak_full.ml`, with that of the core of
  the x4 permutation, from which its correctness theorem follows, in
  `../proofs/sha3_keccak4_f1600_alt2.ml`, and
  `../proofs/utils/mlkem_native2_rej_full.ml`).
- `mlkem_getnoise` for the configurations of n polynomials that the API
  uses (n = 4, 7, 8, 9 with eta1 = 2, and the first 4 of 4 or 2 of 5 with
  eta1 = 3), against `mlkem_prf` and the coefficients of `mlkem_cbd`, with
  its constant-time and memory safety (`../proofs/mlkem_getnoise.ml`, and
  `../proofs/utils/mlkem_native2_noise.ml` for the PRF as the state of a
  lane, the callees, and a simulation driver for code whose control flow
  is fixed by its parameters).
- The API functions for the three parameter sets, with the same statements
  as the proofs of mlkem-native's compiled C: the key checks
  `mlkemL_check_pk` and `mlkemL_check_sk`, with their constant-time and
  memory safety, and `mlkemL_keypair_derand`, `mlkemL_enc_derand` and
  `mlkemL_dec` against ML-KEM.KeyGen_internal, Encaps_internal (after the
  modulus check) and Decaps_internal (after the hash check), with the
  internal `mlkemL_pke_encrypt` and `mlkemL_pke_decrypt` against
  K-PKE.Encrypt and K-PKE.Decrypt, and the constant-time and memory safety
  of these five, with the events a function of the addresses and of the
  public data: rho in key generation, ek in encapsulation, and ek and its
  hash in dk in decapsulation (`../proofs/mlkem512.ml`, `mlkem768.ml` and
  `mlkem1024.ml`, each with the proofs of only the kernels of its parameter
  set, `mlkem_basemul_kK_alt` and the compression and decompression for du
  and dv, and the common parts in `../proofs/utils/mlkem_native2_api.ml`,
  `../proofs/utils/mlkem_native2_kem.ml` and
  `../proofs/utils/mlkem_native2_kem_safe.ml`, and the lemmas on K-PKE of
  the proofs of mlkem-native's compiled C in
  `../proofs/utils/mlkem_native2_kpke.ml`). Unlike those, the theorems of
  the API do not assume that SampleNTT terminates for the seeds of the
  matrix: it does for every seed of one block of SHAKE128, because
  Keccak-f1600 is a permutation, so the squeezing is periodic and comes back
  to the padded seed, whose last byte makes a 12-bit field < q
  (`SAMPLE_OK_ALL` of `../../common/fips203/properties/sampling.ml`, with
  `KECCAK_F1600_INJ` of
  `../../common/fips202/properties/keccak_permutation.ml`).

The specifications are those of `../../common/fips202/fips202.ml` and
`../../common/fips203/fips203.ml`, written by hand from FIPS 202 and FIPS
203, with their properties in the `properties` directories there;
`../../common/fips203/generated/fips203_equivalence.ml` proves that for
the three parameter sets KeyGen, Encaps, Decaps and the input checks of
the latter are those of a model generated from the pseudocode of FIPS 203
(see `../../common/fips203/generated/core/README.md`).

## Where the speed comes from

About two thirds of mlkem-native's time is in Keccak permutations, and on
Neoverse-V2 the x4 permutation costs 1390 cycles for four states against
668 for one with the x1. mlkem-native runs the long serial hashes H(pk)
and, in decapsulation, J(z || c) on the x1 permutation; here they run in
lanes of the x4 permutation beside the sampling of the matrix, which does
not depend on them. Noise is also sampled in lanes the matrix leaves idle
(for k = 3, and in decapsulation, which decrypts first so that the noise
for the re-encryption can be sampled early). Then the codecs, CBD,
frommsg/tomsg and the key checks, which mlkem-native does in C, are in
Neon assembly, 2-9 times faster each, and the rejection sampler is 1.7
times faster. The arithmetic kernels are mlkem-native's.

Cycles per call on a Neoverse-V2 (Graviton 4), against mlkem-native (main
at 9b96caa1) built with clang 18 -O3 and its native backends (the
fastest of the builds tried):

| function | mlkem-native | here | change |
|---|---|---|---|
| mlkem512_keypair_derand | 16743 | 15559 | -7.1% |
| mlkem512_enc_derand | 19809 | 16488 | -16.8% |
| mlkem512_dec | 26110 | 18770 | -28.1% |
| mlkem512_check_pk | 492 | 74 | -85.0% |
| mlkem512_check_sk | 4125 | 4092 | -0.8% |
| mlkem768_keypair_derand | 28405 | 25554 | -10.0% |
| mlkem768_enc_derand | 31391 | 23602 | -24.8% |
| mlkem768_dec | 40699 | 29132 | -28.4% |
| mlkem768_check_pk | 685 | 105 | -84.7% |
| mlkem768_check_sk | 6168 | 6142 | -0.4% |
| mlkem1024_keypair_derand | 41079 | 37783 | -8.0% |
| mlkem1024_enc_derand | 45161 | 36113 | -20.0% |
| mlkem1024_dec | 58402 | 43855 | -24.9% |
| mlkem1024_check_pk | 902 | 137 | -84.8% |
| mlkem1024_check_sk | 8206 | 8168 | -0.5% |

Key generation gains least: its H(pk) is a serial tail with nothing to
run beside it, and its Keccak schedule is otherwise already optimal; the
x1 permutation is at the throughput bound of the four integer pipelines,
and the SHA3 instructions issue only one per cycle on this core.

Stack use, in bytes (keypair_derand, enc_derand, dec): 9200, 8640, 10304
for ML-KEM-512; 13552, 13504, 15824 for ML-KEM-768; 20656, 19392, 22656
for ML-KEM-1024. The stack buffers holding secrets are zeroed before
returning.

## Constant time

Everything is constant-time in the secret data. The rejection sampling of
the matrix, and the scheduling around it, depend only on the public seed
rho; in key generation rho is computed from the secret d, and the build
for testing with valgrind (`MLKEM_CT_TESTING` defined when preprocessing
the per-level files) marks it public there with memcheck's client
request, as mlkem-native does with `MLK_CONFIG_CT_TESTING_ENABLED`. The
results of the key checks are public.

## Testing

The tests and benchmarks are in `../../tests/mlkem_native2` (see its
README). They compare
these functions with mlkem-native's portable C on random and edge-case
inputs, including the rare paths (implicit rejection, invalid keys, the
fourth block of rejection sampling), check the KAT hashes and the ACVP
and Wycheproof vectors, run under memcheck with exact-size buffers and
for constant time with the secrets undefined, check the ABI
(callee-saved registers, x18, sp) and that no secret is left on the
stack, and call the functions through pointers with BTI enforced.
