# ML-KEM in assembly: the mlkem-native API for x86_64 with AVX-512

This directory has the AVX-512 version of `../mlkem_native2`: the same
functions of mlkem-native's ML-KEM API, for all three parameter sets,

    int mlkemL_keypair_derand_avx512(uint8_t *pk, uint8_t *sk,
                                     const uint8_t *coins)
    int mlkemL_enc_derand_avx512(uint8_t *ct, uint8_t *ss,
                                 const uint8_t *pk, const uint8_t *coins)
    int mlkemL_dec_avx512(uint8_t *ss, const uint8_t *ct, const uint8_t *sk)
    int mlkemL_check_pk_avx512(const uint8_t *pk)
    int mlkemL_check_sk_avx512(const uint8_t *sk)

with the same results and the same contracts as those without the suffix
(see `../mlkem_native2/README.md`), for processors with AVX-512F,
AVX-512VL and AVX-512DQ besides AVX2. All the global symbols of the API
and of the middle layer have the suffix `_avx512`, so that both versions
link into one library and the version can be chosen at run time.

## Structure

 - The API and the middle layer are the sources of `../mlkem_native2`,
   assembled with `MLKEM_NATIVE2_AVX512` defined: `mlkemL_avx512.S` and
   `mlkem_gen_matrix_avx512.S`, `mlkem_getnoise_avx512.S`,
   `mlkem_hash_h_avx512.S` and `mlkem_hash_g_avx512.S` include them, and
   `../mlkem_native2/mlkem_native2_names.h` then gives the suffixed names
   and the Keccak-f1600 permutations below. The code is thus the same, the
   schedule of the Keccak work over the lanes included, except for the
   permutations it calls.
 - Two Keccak-f1600 permutations with AVX-512VL, generated (from a script
   kept outside the repository, like the prototypes measured for the
   design): `sha3_keccak4_f1600_avx512`, a drop-in for
   `sha3_keccak4_f1600_alt` (four separate states, transposed into and out
   of 25 ymm registers), and `sha3_keccak_f1600_avx512`, a drop-in for
   `sha3_keccak_f1600` (one state, a lane in each of 25 xmm registers).
   Both keep the whole state in registers (32 of them with AVX-512) and
   do the rotations with `vprolq` and the five-way XORs of theta and chi
   with `vpternlogq`; pi is a renaming of the registers, undone every
   four rounds.
 - The leaves and the constants block are those of `../mlkem_native2`
   (in `../mlkem`), unchanged: AVX-512 gains little over AVX2 for them on
   these processors, and the 256-bit integer multiplications of the
   arithmetic kernels keep the core at the same AVX frequency licence.

The EVEX-encoded instructions, all in the two permutations, all on ymm
or xmm registers (no zmm) and without masking: `vpternlogq`, `vprolq`,
`vmovdqa64` (register moves), `vshufi64x2`, `vpunpcklqdq`, `vpunpckhqdq`,
`vmovdqu64`, `vmovq`, `vpinsrq` and `vpextrq` (these as EVEX forms since
they use registers 16-31), `vinserti32x4`, `vextracti32x4` and `vpxorq`
with a broadcast memory operand (`{1to4}`, `{1to2}`). The EVEX forms of
`vpinsrq` and `vpextrq` need AVX-512DQ. All are in the x86 model, with
the EVEX decoding and the AVX-512 instructions of #468.

No zmm registers are used. On the processor measured, 512-bit
instructions together with the 256-bit integer multiplications of the
arithmetic kernels, which every ML-KEM operation runs, put the core at
its lowest AVX frequency licence (2.39 GHz instead of 2.69 GHz), for every
instruction around them. Earlier versions of the x1 permutation and of
the rejection sampler on zmm registers (732 cycles against 949, and 140
against 213 for 504 bytes) were therefore faster in cycles but slower in
time: encapsulation and decapsulation took 7-8% longer.

## Building and the image

None of these files is in the `OBJ` list of `../Makefile`. The image for
the proofs is `mlkem_native2_avx512_image.elf` (`make
mlkem_native2_avx512/mlkem_native2_avx512_image.elf` in `x86`), linked at
address 0 by `mlkem_native2_avx512_image.ld` from the objects in
`MLKEM_NATIVE2_AVX512_IMAGE_OBJ` of `../Makefile`: this directory's, the
leaves of `../mlkem` and the constants block of `../mlkem_native2`. As for
the AVX2 version, it has no relocations, every call in it is a direct call
and the constants block is at the end, addressed RIP-relatively. The ABI
is the same too (System V, with Microsoft x64 wrappers of the API
functions under `WINDOWS_ABI`).

## Speed

On a Xeon Platinum 8259CL (Cascade Lake) the x4 permutation costs 1040
cycles against 1723 for `sha3_keccak4_f1600_alt`, and the x1 949 against
1087 for `sha3_keccak_f1600_alt2` of the AVX2 version (1260 for
`sha3_keccak_f1600`), both at the base AVX frequency licence (they use no
heavy or 512-bit instructions). Cycles per call, measured as for the AVX2
version and with it (the median of 31 runs of 200 calls on one core, with
the clock measured after each run, and the median of 11 such
measurements; the same clock as for mlkem-native, so the speedup in
cycles is the speedup in time):

| function | mlkem-native | AVX2 version | here | speedup |
|---|---|---|---|---|
| mlkem512_keypair_derand | 24922 | 20327 | 16442 | 1.52x |
| mlkem512_enc_derand | 29189 | 19902 | 14599 | 2.00x |
| mlkem512_dec | 39618 | 21602 | 16366 | 2.42x |
| mlkem512_check_sk | 8726 | 6727 | 5863 | 1.49x |
| mlkem768_keypair_derand | 43050 | 33388 | 26354 | 1.63x |
| mlkem768_enc_derand | 46256 | 28279 | 20998 | 2.20x |
| mlkem768_dec | 61364 | 33991 | 25459 | 2.41x |
| mlkem768_check_sk | 13023 | 10186 | 8917 | 1.46x |
| mlkem1024_keypair_derand | 58874 | 49280 | 38367 | 1.53x |
| mlkem1024_enc_derand | 64496 | 43995 | 32665 | 1.97x |
| mlkem1024_dec | 84380 | 52544 | 39168 | 2.15x |
| mlkem1024_check_sk | 17292 | 13523 | 11817 | 1.46x |

(check_pk is as in the AVX2 version.) Stack use, in bytes (keypair_derand,
enc_derand, dec): 9080, 8552, 10216 for ML-KEM-512; 13432, 13416, 15720 for
ML-KEM-768; 20520, 19304, 22568 for ML-KEM-1024 (224 more through the
Windows wrappers), a little less than the AVX2 version since the
permutations use no stack.

## Proofs

`make mlkem_native2_avx512_proofs` in `x86` runs the proofs of this
version: those of the two permutations, and those of the functions of the
image, the same theorems as for the AVX2 version (see
`../mlkem_native2/README.md`) about the image of this one.

- The permutations, against `keccak 24` of
  `../proofs/utils/keccak_spec.ml`, with their constant-time and memory
  safety: `../proofs/sha3_keccak4_f1600_avx512.ml` and
  `../proofs/sha3_keccak_f1600_avx512.ml`, with the common parts in
  `../proofs/utils/keccak_avx512.ml`, and the theorems of correctness and
  safety in one for the callers in the image in
  `../proofs/utils/keccak_avx512_full.ml`. As for the AVX2 permutations,
  each round is simulated with the lanes of the registers as variables and
  each lane of the new state is compared with that of `keccak_round` by
  bit-blasting; the model gives `vpternlogq` as the disjunction of the
  minterms of its immediate, which the simulation turns into the XOR and
  AND-NOT forms first.
- The functions of the image, in copies of the files of the AVX2 version
  with `_avx512` added to their names, the names of the functions in them,
  and those of the theorems about the image
  (`MLKEM768_ENC_DERAND_AVX512_SUBROUTINE_CORRECT` etc.):
  `../proofs/mlkem_native2_avx512_image.ml`,
  `../proofs/mlkem_hash_h_avx512.ml`, `mlkem_hash_g_avx512.ml`,
  `mlkem_getnoise_avx512.ml`, `mlkem_gen_matrix_avx512.ml`,
  `mlkem_gen_matrix_k2_avx512.ml` to `mlkem_gen_matrix_k4_safe_avx512.ml`,
  `mlkem512_avx512.ml`, `mlkem768_avx512.ml` and `mlkem1024_avx512.ml`,
  and `../proofs/utils/mlkem_native2_avx512_*.ml`. Up to the permutations,
  the image is the AVX2 one byte for byte, but for the displacements of
  the three calls of the x4 permutation and of the references to the
  constants block (which follows the permutations), so the proofs are the
  same but for the parts about the permutations, in
  `../proofs/utils/mlkem_native2_avx512_sponge.ml` (x1), `_noise.ml` (x4)
  and `_keccak_full.ml`. The utilities that are not about an image
  (`../proofs/utils/mlkem_native2_tools.ml`, `mlkem_native2_kpke.ml` and
  `mlkem_native2_rej_full.ml`) and the proofs of the leaves are shared
  with the AVX2 version. The copies are kept in step by hand: a change to
  the proofs of one version is to be made to the other's too.
- The x4 permutation is called as `sha3_keccak4_f1600_alt` is in the AVX2
  version, with pointers to the two rotation tables of the latter (which
  it does not read), and with the 0x31f bytes below its return address
  that the latter uses as its stack (it uses none). Its theorems are given
  the forms of those of `sha3_keccak4_f1600_alt` (in
  `../proofs/utils/mlkem_native2_avx512_noise.ml`, by weakening its own),
  so that the proofs of its callers are copies too; the theorems of this
  version thus have the stack bounds of the AVX2 version, larger than the
  stack use given above by up to about 800 bytes.

## Constant time and testing

As for the AVX2 version: everything is constant-time in the secret data,
with the same schedule. The tests of `../../tests/mlkem_native2` run on
this version with `VARIANT=avx512 ./build.sh`, which builds it into
`work/obj_avx512` with the suffix removed from the names of the API and
the middle layer, so that the tests and the benchmarks use it unchanged.
valgrind does not run EVEX code, so the steps under memcheck (memcheck and
the constant-time check) do not apply: `VALGRIND= CTLIBS=none ./gate.sh
avx512 work/obj_avx512/*.o` runs the rest of the gate.
