# The gcc 12 -O2 reduced-RAM build

This directory is for mldsa-native's `libmldsa.so` built with gcc 12 and
`-O2` in the reduced-RAM configuration, `MLD_CONFIG_REDUCE_RAM`: the x86-64
`binaries/reduced-ram/multilevel/gcc12/O2/libmldsa.so` of the
`binary-v2.1` branch of mldsa-native, at commit `c817bc7df` ("binaries:
Build the ML-DSA v2.1.0 matrices"). The gcc12_O2 build (see `../README.md`)
is the same sources and compiler in the default configuration.

## Source of the code

As recorded in `binaries/builds.json` of the `binary-v2.1` branch at
that commit, the binary was built by `scripts/build-binaries` from the
v2.1.0 release of mldsa-native, commit `c9999d775`, as the one of the
gcc12_O2 build (see "Source of the code" in `../README.md`), with
`-DMLD_CONFIG_REDUCE_RAM` added to the flags, where
`scripts/build-binaries` puts the defines of a configuration:

```
-O2 -g -gdwarf-4 -gsplit-dwarf -fPIC -fno-stack-protector
-DMLD_CONFIG_REDUCE_RAM
```

As for the gcc12_O2 build, the stack protector is off; this binary does
not call `memset` either (gcc zeroes the small structures of this
configuration with inlined stores), so it imports only `memcpy` and
`randombytes`.

The SHA-256 hash of the binary used, which is that in
`binaries/SHA256SUMS` of commit `c817bc7df`, is:

```
reduced-ram/multilevel/gcc12/O2/libmldsa.so
  c1df0b4681f295240a6a17da75b312b93a5f523f783e570170ac78ab7e47f0ad
```

The image starts at address 0, so it includes the dynamic string table,
where the linker records the directory of the build as `RUNPATH`
(`/tmp/native-binary-v2.1-single.ZcXVDkyZ/mldsa-source/outputs/out/lib`
for this binary). A binary built from the same source in another directory
therefore differs there, and in the split debug information, but its code
and read-only data are the same.

`libmldsa.S` transcribes the image, from address 0 to the end of the
read-only data at `libmldsa_size` = 0xc820, and is the same as the binary
byte for byte; `keccakf1600_permute.S` is the code of
`mldsa_keccakf1600_permute` alone, as for gcc12_O2
(`check_transcription.py` checks it against the binary), and
`../../proofs/mldsa_native/gcc12_O2_reduced_ram/` has the layout, the
definition of the image and the proofs.

To regenerate the files of the build, in the `x86` directory, with
`<build>` the `binaries` directory of a checkout of mldsa-native at commit
`c817bc7df` of the `binary-v2.1` branch (see "Source of the code" in
`../README.md` for the x86-64 `as` that the first command needs):

```
python3 mldsa_native/gen_libmldsa_s.py \
  <build>/reduced-ram/multilevel/gcc12/O2/libmldsa.so \
  mldsa_native_libmldsa_gcc12_O2_reduced_ram \
  "gcc 12, -O2, MLD_CONFIG_REDUCE_RAM" \
  reduced-ram/multilevel/gcc12/O2/libmldsa.so $PWD/../include \
  > mldsa_native/gcc12_O2_reduced_ram/libmldsa.S
python3 mldsa_native/gen_layout.py \
  --name reduced-ram/multilevel/gcc12/O2/libmldsa.so \
  <build>/reduced-ram/multilevel/gcc12/O2/libmldsa.so \
  > proofs/mldsa_native/gcc12_O2_reduced_ram/layout.ml
python3 ../tools/native_proofs_mk.py mldsa_native gcc12_O2_reduced_ram \
  > mldsa_native/gcc12_O2_reduced_ram/proofs.mk
python3 ../tools/native_link.py mldsa_native gcc12_O2_reduced_ram \
  > proofs/mldsa_native/gcc12_O2_reduced_ram/link.ml
```

## Compared with the gcc 12 -O2 build

The image has 176 functions, with the same names as the AArch64
reduced-RAM binary of the `binary` branch, against 192:

 - 149 functions have the same code as in the gcc12_O2 build, up to
   addresses. For 113 of them the stack frame is also the same, and the
   proofs are those of the gcc12_O2 build, renamed. The other 36 call
   functions that use less stack, so their frames are smaller, and 33 of
   them no longer depend on `memset`; their proofs are those of the
   gcc12_O2 build with the frame and the contracts adapted.
 - 13 functions have new code: `unpack_sk`, `compute_pack_t0_t1`,
   `verify_internal` and `signature_internal` for each parameter set, and
   `mldsa_shake256x4_absorb_once`, into which gcc inlines
   `mld_keccak_absorb_once_x4`.
 - 14 functions are new: `polyvec_matrix_expand_lazy`,
   `polyvec_matrix_pointwise_montgomery_row_lazy`,
   `polyvec_matrix_pointwise_montgomery_yvec_lazy` and `polyveck_reduce` for
   each parameter set, and `poly_uniform_gamma1` for ML-DSA-44 and -87 (for
   ML-DSA-65 it is also in the gcc12_O2 build).
 - 30 functions of the gcc12_O2 build are not here: the eager matrix
   expansion and products, `polyvecl_pointwise_acc_montgomery`,
   `polyvecl_uniform_gamma1`, `poly_uniform_gamma1_4x`, `polyveck_ntt`,
   `polyveck_unpack_eta`, `poly_uniform_4x` and the `shake128x4` functions.

The stack that the API functions need is between 3 and 7 times smaller,
e.g. 16228 bytes for ML-DSA-87 signing, against 112756.

## The algorithm

In this configuration (`mldsa/src/polyvec_lazy.[ch]`) the large vectors and
the matrix of the default configuration are not kept in memory:

 - The matrix A is never expanded. `polyvec_matrix_expand_lazy` only copies
   rho into a structure that also holds one polynomial, and the products
   with A sample each entry when they need it: row by row in key generation
   and verification (`..._row_lazy`), column by column in signing
   (`..._yvec_lazy`). Each entry is multiplied by the polynomial of the
   vector with a Montgomery reduction of its own, the products are added up
   and the sum is reduced, whereas the default configuration accumulates
   the products of a row in 64 bits and reduces once.
 - The vector y of a signing attempt is not stored: its polynomials are
   sampled again where they are needed, in the product A * y and in
   z = y + c s1.
 - s1, s2 and t0 are not unpacked and transformed once for all attempts:
   `unpack_sk` only records where they are in the secret key, and signing
   unpacks and transforms each polynomial when it needs it.

The lazy products are specified in `../../../common/mldsa_native_lazy.ml`,
following the C code, as for the AArch64 reduced-RAM build
(`../../../arm/mldsa_native/gcc12_O2_reduced_ram/README.md`):
`mld_polyvec_matrix_row_lazy`, `mld_polyvec_matrix_yvec_lazy` and
`mld_compute_t_lazy`. They give different integers from the default ones,
but congruent modulo q and within q of 0, and since the code always applies
the inverse NTT and makes the coefficients nonnegative afterwards, the
results of key generation, signing and verification are the same.
`../../proofs/mldsa_native/gcc12_O2_reduced_ram/lazy_eq_spec.ml` states,
and `lazy_eq_proof.ml` proves (with
`../../../common/fips204/properties/mldsa_native_lazy.ml`), that these give
the values of the gcc12_O2 specifications: t (`mld_compute_t`), w after
caddq (`mld_sign_w`) and the rows of the verification, for coefficients
within the bounds that the unpacking of the secret key and of z, the NTT
and the pointwise products ensure. These are the statements of the AArch64
build, and so is the theorem for `mld_compute_pack_t0_t1`, against
`mld_compute_t` for s1hat within the bound of the NTT, which key generation
and `pk_from_sk` prove before the call. The proofs of the callers use the
statements as contracts (see `../../../common/relative.ml`), and `link.ml`
closes them with `lazy_eq_proof.ml`. So the theorems of the API functions
are those of the gcc12_O2 build, up to the stack frames, the contracts of
`memset` and, for ML-DSA-65, the read-only constants of the eager matrix
expansion, and so are the FIPS 204 theorems (`fips204*.ml`, whose tactics
also accept a CORRECT theorem without contracts).

Three utils are for the code of this build, in `../../proofs/utils`:
`mldsa_native_lazy_matrix.ml` (the lazy products, the x86-64 counterpart
of the AArch64 util of the same name), `mldsa_native_top_rr.ml`
(`pk_from_sk` without `memset`) and `mldsa_native_signing_rr.ml` (the
signing attempts).
