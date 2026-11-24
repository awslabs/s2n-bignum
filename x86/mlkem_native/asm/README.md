# ML-KEM in assembly: the mlkem-native API for x86_64 (AVX2)

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
values included). It is the x86_64 counterpart of `../../../arm/mlkem_native/asm`,
with the same design, for processors with AVX2 (and POPCNT; no AVX-512),
written in the style of s2n-bignum and meant to be proved in HOL Light
like the AArch64 version. The AVX-512 version, from the same sources, is
in `../asm_avx512`. The randomized `mlkemL_keypair` and
`mlkemL_enc` are not here, since they need a source of randomness: as in
mlkem-native, they get 64 or 32 random bytes, call the deterministic
function and zero the bytes (`../../../tests/mlkem_native2/randomized.c`).

## Structure

The work is in three layers, as on AArch64.

 - The leaves, in `../../mlkem`, standalone s2n-bignum-style functions, each
   with its own specification in its header comment:
    - the existing x86 kernels of s2n-bignum, which are mlkem-native's
      current AVX2 code: `mlkem_ntt_x86`, `mlkem_intt_x86`,
      `mlkem_mulcache_compute_x86`, `mlkem_basemul_k{2,3,4}`,
      `mlkem_reduce`, `mlkem_tomont`, `mlkem_frombytes` and
      `mlkem_tobytes` (which include the permutation into and out of the
      custom NTT order of mlkem-native's x86 backend) and `mlkem_unpack`
      (that permutation, for the sampled matrix); and s2n-bignum's
      Keccak-f1600 kernel `sha3_keccak4_f1600_alt` (x4);
    - a new Keccak-f1600 kernel for one state, `sha3_keccak_f1600_alt2` in
      `../../sha3` (the same function as `sha3_keccak_f1600`), of original
      design: with the lanes as the points of Z5 x Z5, pi maps each line
      through the origin onto another, so the state is in seven ymm
      registers, the six lines without the origin and the lane (0, 0),
      and pi moves lanes only within registers; it is gathered from and
      scattered back to `a[25]`;
    - mlkem-native's AVX2 compress and decompress kernels for d = 4, 5, 10
      and 11, unchanged (byte for byte, so that mlkem-native's HOL Light
      proofs of them apply), as `mlkem_compress_d4_x86` and so on: they
      take their tables from the constants block;
    - new ones for what mlkem-native does in C, with the same names,
      signatures and contracts as on AArch64: `mlkem_cbd2`, `mlkem_cbd3`,
      `mlkem_frommsg`, `mlkem_tomsg`, `mlkem_check_encoding` (the modulus
      check of an encapsulation key), `mlkem_add_reduce`,
      `mlkem_sub_reduce`, and a faster rejection sampler
      `mlkem_rej_uniform_alt_VARIABLE_TIME` that appends to a partial
      result.
 - The middle layer, here: `mlkem_gen_matrix` (the matrix, with hash jobs
   and noise in the spare lanes of the x4 permutation, and its
   polynomials permuted into the custom NTT order), `mlkem_getnoise`
   (noise sampling in the x4 lanes), `mlkem_hash_h` and `mlkem_hash_g`
   (SHA3-256 and SHA3-512 with the x1 permutation). The seventh argument
   of `mlkem_gen_matrix` and `mlkem_getnoise`, the constants block, is on
   the stack.
 - The API: `mlkem_kem_template.S`, included by `mlkem512.S`,
   `mlkem768.S` and `mlkem1024.S` after they define the parameter set.
   Besides the API functions it has `mlkemL_pke_encrypt` and
   `mlkemL_pke_decrypt`, shared by encapsulation and decapsulation.

The tables of constants (the Keccak round constants and the rho8 and rho56
tables of the x4 permutation, the qdata of the NTT kernels, the tables of
the compress and decompress kernels and the rejection sampling table, all
taken unchanged from mlkem-native's x86_64 sources) are one read-only
block, `mlkem_native2_constants` (`mlkem_native2_constants.S`, with the
layout in `mlkem_native2_consts.h`, every field 32-byte aligned). The API
functions take its address RIP-relatively and pass it to the functions
below.

## ABI

All functions follow the System V ABI. With `WINDOWS_ABI` (the Microsoft
x64 ABI), each of the 15 API functions becomes a wrapper that saves rdi,
rsi and xmm6-xmm15, moves the arguments to their System V registers and
calls the System V code: everything below the API is the same System V
code in either case, so a Windows build assembles the per-level files with
`WINDOWS_ABI=1` and all the other files with `WINDOWS_ABI=0`. (The leaves
also have the usual `#if WINDOWS_ABI` prologues of s2n-bignum, for use on
their own.) Every global function starts with endbr64 (`_CET_ENDBR`), and
every function that uses ymm registers executes vzeroupper before it
returns. The code uses only VEX-encoded vector instructions (legacy SSE
instructions are slow after AVX code that leaves the upper halves of the
registers dirty, as the existing kernels do), and no PEXT (slow on AMD
Zen 2). The polynomial buffers of the frames are 32-byte aligned, as the
existing kernels require; the API functions take any alignment of their
arguments. The new functions are 32-byte aligned, like the existing
Keccak kernels, and no branch of their hot loops crosses or ends at a
32-byte boundary, which on cores with the microcode fix for Intel's JCC
erratum would make the loop run from the legacy decoders: their speed
does not depend on where they are linked.

## Building

This is the build `asm` of `..` (see `../README.md`). None of these files
is in the `OBJ` list of `../../Makefile`, so they are not in
`libs2nbignum.a`; `proofs.mk` here, generated by
`../../../tools/native_proofs_mk.py`, which `../../Makefile` includes, adds
the objects to `MLKEM_NATIVE_OBJ` and the proofs to `MLKEM_NATIVE_PROOFS`
(so they are in `make proofs`), and the objects are built with the usual
rule, e.g. `make mlkem_native/asm/mlkem768.o` in `x86`. The API for one
parameter set, `mlkemL.o`, needs the middle layer and the constants block
from here, the leaves in `../../mlkem` and the two Keccak permutations in
`../../sha3` (the list `MLKEM_ASM_IMAGE_OBJ` of `image.mk`, the part of the
make rules that is written by hand: the list, the rule that links the
image, and that every proof of the build reads the image).

## Proofs

The functions here call others (direct calls only), so their proofs are
about the image of all the functions involved: the objects in
`MLKEM_ASM_IMAGE_OBJ` of `image.mk`, linked at address 0 by
`mlkem_native2_image.ld` into `mlkem_native2_image.elf` (`make
mlkem_native/asm/mlkem_native2_image.elf` in `x86`, with GNU ld): the code of
the objects in that order, then their read-only data, the rotation table
of `sha3_keccak_f1600_alt2` and the constants block (64-byte aligned), at
the end of the one section `.text`. The image has no relocations, every
call in it is a direct call, and the only RIP-relative references are the
18 to the constants block and the one to the rotation table. It is all
assembly, so there is no stack-protector code: no instruction uses fs or
gs, the segment registers with a base in 64-bit mode (`check_noseg.sh` in
the tests checks this), and the only segment prefixes are the CS prefixes
of some of the NOPs of the padding. `../../proofs/mlkem_native/asm/layout.ml`
reads the image as one byte list and installs the names of its symbols,
so that a proof refers to the function f or the label f in the image as
`pc + f`; the theorems for the leaves and the Keccak permutations, about
their own code, are used for the same code in the image. The theorems are
thus for this layout of the image, and are checked again when it changes.

The instructions of the image that are not in `../../allowed_asm` (the
constant-time list) are the conditional branches (on public data only),
`vpmovmskb`, `vptest`, `setcc`, `popcnt` (in the rejection sampler, whose
input is public), the byte and word forms of `mov`, `xor` and `movzx`,
and the NOPs of the padding between functions. All are in the x86 model.

The proofs are done as those of the compiled build (see `../README.md`,
"Spec and proof files"), in `../../proofs/mlkem_native/asm`: each function
`f` has a spec file `f_spec.ml`, which states its theorems and loads the
spec files of its callees, and a proof file `f_proof.ml`, which proves
them relative to the contracts of the callees (`../../../common/relative.ml`).
So the proofs of a function run once, whichever functions call it, and
`link.ml`, generated by `../../../tools/native_link.py mlkem_native asm`,
runs all the proof files as jobs, one after the other or in parallel, and
discharges the contracts with the proved theorems: the check of the whole
build is `make mlkem_native/asm/link.correct` in `x86`, or the same with
`HOL_PAR=1` (see "Running proofs in parallel" in `../../../README.md`).
The files, named by the function as in the compiled build:

- the API functions for the three parameter sets, `check_pk_k2`,
  `check_sk_k2`, `keypair_derand_k2`, `enc_derand_k2` and `dec_k2`, and
  the same with `k3` and `k4` (ML-KEM-512, 768 and 1024), and the internal
  `pke_encrypt_k2` and `pke_decrypt_k2` (and `k3`, `k4`), with the same
  statements as the proofs of mlkem-native's compiled C, the results as
  those of ML-KEM.KeyGen_internal, Encaps_internal (after the modulus
  check) and Decaps_internal (after the hash check) and K-PKE.Encrypt and
  K-PKE.Decrypt of FIPS 203, and the constant-time and memory safety of
  all, with the events a function of the addresses and of the public data:
  rho in key generation, ek in encapsulation, and ek and its hash in dk in
  decapsulation. As on AArch64, no theorem assumes that SampleNTT
  terminates for the seeds of the matrix, so the build has no `fips203.ml`.
  The frames of the API functions are realigned to 32 bytes below the
  return address, so the theorems allow any alignment of the stack pointer,
  and in the safety theorems the offset of the frame is a function of the
  stack pointer.
- `hash_h` (SHA3-256) and `hash_g` (SHA3-512), against `sha3_256` and
  `sha3_512` of `../../../common/fips202/fips202.ml`, with their
  constant-time and memory safety, and `sponge_spec.ml` for the sponge and
  the use of `sha3_keccak_f1600_alt2`
  (`MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_CORRECT` and so on).
- `gen_matrix_k2`, `gen_matrix_k3` and `gen_matrix_k4` for the nine
  configurations that the API uses (k = 2, 3, 4 in key generation,
  encapsulation and decapsulation, with their hash jobs and noise), against
  `mlkem_sample_ntt` (in the order of the coefficients of the x86 NTT
  domain, as `mlkem_unpack` leaves them), `sha3_256`, `shake256` and the
  coefficients of `mlkem_cbd`, with the common parts in
  `gen_matrix_common_spec.ml` and `matrix_spec.ml`, and the lemmas on FIPS
  203 of the proofs of mlkem-native's compiled C in
  `../../proofs/utils/mlkem_native_fips203.ml`; their constant-time and
  memory safety, with the events a function of the addresses and of the
  public seed rho (and, for decapsulation, the digest H(ek) of the first
  hash job as a result), in `gen_matrix_k2_safe` and so on, with the common
  parts in `gm_safe_spec.ml`. The theorems are named
  `MLKEM_NATIVE_GEN_MATRIX_K3_NOISE_ASM_IMAGE_SUBROUTINE_CORRECT` and so on.
- `getnoise` for the configurations that the API uses (n = 4, 7, 8, 9 with
  eta1 = 2, and the first 4 of 4 or 2 of 5 with eta1 = 3), against
  `mlkem_prf` and the coefficients of `mlkem_cbd`, with its constant-time
  and memory safety (`noise_spec.ml` has the common parts).
- Files for the tools that several functions use, with the lemmas that
  they prove as jobs of their own: `api`, `kem` and `kem_safe` (the
  tactics for the API functions and the theorems for the kernels in the
  forms that the callers need), `kpke` (the lemmas on K-PKE),
  `keccak_full` and `rej_full` (correctness and safety in one theorem for
  the Keccak permutations and the rejection sampler).
- The leaves, `ntt_x86`, `intt_x86`, `mulcache_compute_x86`,
  `basemul_k2` to `k4`, `reduce`, `tomont`, `frombytes`, `tobytes`,
  `unpack`, `compress_d4_x86` and so on, `cbd2`, `cbd3`, `frommsg`,
  `tomsg`, `check_encoding`, `add_reduce`, `sub_reduce`,
  `rej_uniform_alt_VARIABLE_TIME`, `sha3_keccak_f1600_alt2` and
  `sha3_keccak4_f1600_alt`: their standalone proofs in `../../proofs`
  (`mlkem_ntt.ml` and so on) are unchanged, so that the kernels also have
  proofs of their own. The spec file of a leaf loads its standalone proof
  with every proof assumed (`relative_assuming` of
  `../../../common/relative.ml`), after the files that it loads itself, so
  that its definitions, tactics and theorems, which the callers use, are
  contracts; its proof file loads the file again (`loadt`), which proves
  them, once, inside its job. The theorems of a leaf are about its own code
  at its own address, and the callers use them for the same code in the
  image, at `pc + f`. The forms in which the callers need them (the
  theorems about the kernels with the tables in the image, the safety
  theorems with the frames of the correctness theorems, the theorems of
  correctness and safety in one) are made, and proved once, in the files
  of the tools: `kem`, `kem_safe`, `api`, `noise`, `matrix`, `sponge`,
  `keccak_full`, `rej_full` and `gm_safe`.

The theorems are named as in the compiled build, with `ASM_IMAGE` for
the image of this one. Before the conversion the proof of each parameter
set was one file (`mlkem512.ml`, `mlkem768.ml`, `mlkem1024.ml`), the
others `mlkem_hash_h.ml` and so on, and the theorems were named:

| before | now |
|---|---|
| `MLKEM<n>_<F>_SUBROUTINE_CORRECT` and `_SAFE` | `MLKEM_NATIVE_<F>_K<k>_ASM_IMAGE_SUBROUTINE_CORRECT` and `_SAFE` |
| `MLKEM_HASH_G_SUBROUTINE_CORRECT`, `MLKEM_HASH_H_`, `MLKEM_GETNOISE_` | `MLKEM_NATIVE_HASH_G_ASM_IMAGE_SUBROUTINE_CORRECT`, `MLKEM_NATIVE_HASH_H_`, `MLKEM_NATIVE_GETNOISE_` |
| `MLKEM_GEN_MATRIX_K<k><C>_SUBROUTINE_CORRECT` and `_SAFE` | `MLKEM_NATIVE_GEN_MATRIX_K<k><C>_ASM_IMAGE_SUBROUTINE_CORRECT` and `_SAFE` |

with `<n>` = 512, 768, 1024 for `<k>` = 2, 3, 4, `<F>` one of `CHECK_PK`,
`CHECK_SK`, `KEYPAIR_DERAND`, `ENC_DERAND`, `DEC`, `PKE_ENCRYPT` and
`PKE_DECRYPT`, and `<C>` the configuration of the matrix (empty for k = 2,
`_HASH`, `_HASHES`; `_NOISE`, `_HASH`, `_HASHES_NOISE` for k = 3, 4): for
example `MLKEM768_KEYPAIR_DERAND_SUBROUTINE_CORRECT` is now
`MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_IMAGE_SUBROUTINE_CORRECT`, and
`MLKEM_GEN_MATRIX_K3_HASHES_NOISE_SUBROUTINE_SAFE` is now
`MLKEM_NATIVE_GEN_MATRIX_K3_HASHES_NOISE_ASM_IMAGE_SUBROUTINE_SAFE`. The
statements are unchanged. The `T_STMT` of each theorem `T` is renamed
with it, and the lemmas keep their names.

The specifications are those of `../../../common/fips202/fips202.ml` and
`../../../common/fips203/fips203.ml`, as on AArch64 (see
`../../../arm/mlkem_native/asm/README.md` for the model of FIPS 203 generated
from its pseudocode, which is proved equivalent to the latter).

The proofs of the AVX-512 version (`../asm_avx512`) are copies
of these, with their own parts for its Keccak permutations (see its README).

There are no AT&T versions of these files, or of the new leaves and of
`sha3_keccak_f1600_alt2`, in `../../../x86_att`.

## Where the speed comes from

On the machine measured, a Xeon Platinum 8259CL (Cascade Lake), the x4
permutation costs 1723 cycles for four states against 1087 for one with
the x1 permutation (1063 with `sha3_keccak_f1600_alt`, the round of
OpenSSL's AVX2 Keccak, 1260 with s2n-bignum's scalar `sha3_keccak_f1600`,
1399 for mlkem-native's x1 in C): an x4 call pays as soon as two of its
lanes are useful, and so all Keccak work that can run in parallel does.
mlkem-native runs H(ek), J(z || c) and G on the x1 permutation; here
H(ek), and in decapsulation J(z || c), run in lanes of the x4 permutation
beside the sampling of the matrix (at every level), and noise is sampled
in lanes the matrix leaves idle. For ML-KEM-768 decapsulation this means
13 x4 calls and 1 x1 call against 8 x4 and 22 x1. Then the codecs, CBD,
frommsg/tomsg and the key check, which mlkem-native does in C, are in AVX2
assembly (frommsg 42 cycles against 1532, tomsg 44 against 399, CBD2 62
against 165, CBD3 106 against 308, the key check for k = 3 159 against
651), and the rejection sampler is 1.8 times faster (213 cycles against
391 for 504 bytes, 48 bytes per step while there is room for 32 more
entries). The arithmetic kernels are mlkem-native's.

Cycles per call (the median of 31 runs of 200 calls on one core, with the
clock measured after each run since it varies with the AVX frequency
licences, and the median of 11 such measurements, alternating with those
of mlkem-native; the same clock as for mlkem-native, so the speedup in
cycles is the speedup in time), against mlkem-native (main at 9b96caa1)
built with clang 18 -O3 and its native backends (the fastest of the
builds tried):

| function | mlkem-native | here | speedup |
|---|---|---|---|
| mlkem512_keypair_derand | 24922 | 20327 | 1.23x |
| mlkem512_enc_derand | 29189 | 19902 | 1.47x |
| mlkem512_dec | 39618 | 21602 | 1.83x |
| mlkem512_check_pk | 423 | 100 | 4.23x |
| mlkem512_check_sk | 8726 | 6727 | 1.30x |
| mlkem768_keypair_derand | 43050 | 33388 | 1.29x |
| mlkem768_enc_derand | 46256 | 28279 | 1.64x |
| mlkem768_dec | 61364 | 33991 | 1.81x |
| mlkem768_check_pk | 642 | 143 | 4.49x |
| mlkem768_check_sk | 13023 | 10186 | 1.28x |
| mlkem1024_keypair_derand | 58874 | 49280 | 1.19x |
| mlkem1024_enc_derand | 64496 | 43995 | 1.47x |
| mlkem1024_dec | 84380 | 52544 | 1.61x |
| mlkem1024_check_pk | 865 | 185 | 4.68x |
| mlkem1024_check_sk | 17292 | 13523 | 1.28x |

Key generation gains least: its H(pk) is a serial tail on the x1
permutation, with nothing to run beside it. (check_pk takes 100-210
cycles, and its time varies by about 10% from one build to another.)

Stack use, in bytes (keypair_derand, enc_derand, dec): 9824, 8768, 10432
for ML-KEM-512; 14176, 13416, 16416 for ML-KEM-768; 21312, 19304, 22568 for
ML-KEM-1024 (224 more through the Windows wrappers). The stack buffers
holding secrets are zeroed before returning.

## Constant time

Everything is constant-time in the secret data. The rejection sampling of
the matrix, and the scheduling around it, depend only on the public seed
rho; in key generation rho is computed from the secret d, and the build
for testing with valgrind (`MLKEM_CT_TESTING` defined when preprocessing
the per-level files) marks it public there with memcheck's client
request, as mlkem-native does with `MLK_CONFIG_CT_TESTING_ENABLED`. The
results of the key checks are public.

## Testing

The tests and benchmarks are in `../../../tests/mlkem_native2` (see its
README), which run on x86_64 as on AArch64. They compare these functions
with mlkem-native's portable C on random and edge-case inputs, including
the rare paths (implicit rejection, invalid keys, the fourth block of
rejection sampling), check the KAT hashes and the ACVP and Wycheproof
vectors, run under memcheck with exact-size buffers and for constant time
with the secrets undefined, check the ABI (the System V callee-saved
registers and rsp, and for the Windows entries, called through
`ms_abi` function pointers, also rdi, rsi and xmm6-xmm15) and that no
secret is left on the stack, and check that every global function starts
with endbr64 (IBT cannot be enforced without CET).
