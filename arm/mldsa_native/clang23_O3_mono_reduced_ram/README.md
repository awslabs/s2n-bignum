# The clang 23 -O3 monolithic reduced-RAM build

This directory is for mldsa-native's `libmldsa.so` built with clang 23 and
`-O3`, in the monolithic layout and the reduced-RAM configuration
`MLD_CONFIG_REDUCE_RAM`:
`binaries/reduced-ram/multilevel-mono/clang23/O3/libmldsa.so` in the
`binary` branch of mldsa-native (commit `65f9995`, "binaries: Rebuild the
AArch64 matrix from main"), built from mldsa-native `d38418ea3d4c`, which
is also the source of the gcc 12 builds (see `../README.md` and
`../gcc12_O2_reduced_ram/README.md`). The C code is that of the
gcc12_O2_reduced_ram build, and so are the statements, with the changes
that the code forces (see "Compared with the gcc 12 -O2 reduced-RAM
build").

## Source of the code

In the monolithic layout (`multilevel-mono`), `scripts/build-binaries`
compiles the single translation unit
`examples/monolithic_build_multilevel/mldsa_native_all.c`, which has the
code shared by the three parameter sets once, with the namespace `mldsa_`,
and the rest once per parameter set, with
`-O3 -g -gdwarf-4 -gsplit-dwarf -fPIC -DMLD_CONFIG_REDUCE_RAM`, and links
it into `libmldsa.so` as for the other layout (see "Source of the code" in
`../README.md`). `binaries/builds.json` records this and the compiler,
clang 23.1.3, which the `.comment` section of the binary also records. As
for the gcc 12 binaries, the stack protector is on: 53 functions read the
guard `__stack_chk_guard` through the GOT and call `__stack_chk_fail` if
it changed. The binary imports these two, `memcpy`, `memset` and
`randombytes`.

The SHA-256 hash of the binary, which matches that recorded in
`binaries/SHA256SUMS` of mldsa-native, is:

```
binaries/reduced-ram/multilevel-mono/clang23/O3/libmldsa.so
  ac8b3ba9260ccb2a222158edf5ec2f3dbb2b742b502e52275004c5d9ec9cfc72
```

`libmldsa.S` transcribes the image, from address 0 to the end of the
read-only data at `libmldsa_size` = 0x3cbf0. The 12 pointers to the
entries of the table `oid_map` of `mld_get_hash_oid`, which the dynamic
loader relocates, are not in the image but in `.data.rel.ro` after it, at
0x4fdd8: the statements of the functions that read them assume their
relocated contents, as for the GOT entries of the C library functions
(see `prepare_domain_separation_prefix_44_spec.ml`).
`../../proofs/mldsa_native/clang23_O3_mono_reduced_ram/` has the layout,
the definition of the image and the proofs.

To regenerate the files of the build, in the `arm` directory:

```
python3 mldsa_native/gen_libmldsa_s.py \
  <mldsa-native>/binaries/reduced-ram/multilevel-mono/clang23/O3/libmldsa.so \
  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram \
  "clang 23, -O3, monolithic, reduced RAM" \
  binaries/reduced-ram/multilevel-mono/clang23/O3/libmldsa.so $PWD/../include \
  > mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.S
python3 mldsa_native/gen_layout.py --dwarf \
  --name reduced-ram/multilevel-mono/clang23/O3/libmldsa.so \
  <mldsa-native>/binaries/reduced-ram/multilevel-mono/clang23/O3/libmldsa.so \
  > proofs/mldsa_native/clang23_O3_mono_reduced_ram/layout.ml
python3 ../tools/native_proofs_mk.py mldsa_native clang23_O3_mono_reduced_ram \
  > mldsa_native/clang23_O3_mono_reduced_ram/proofs.mk
python3 ../tools/native_link.py mldsa_native clang23_O3_mono_reduced_ram \
  > proofs/mldsa_native/clang23_O3_mono_reduced_ram/link.ml
```

With `--dwarf`, `gen_layout.py` reads the split debug information
`libmldsa.so.dwp` next to the binary and also names the calls that clang
has inlined (`in_g` and `in_g_end` for an inlined call of `g`), which the
proofs use to state lemmas for these regions.

## Compared with the gcc 12 -O2 reduced-RAM build

clang inlines almost every function into its callers, so the image has 67
functions, against 176:

 - the 14 external API functions of each parameter set (42 in all);
 - `mld_H` and `mld_compute_pack_t0_t1`, and `polyvecl_chknorm`,
   `poly_challenge`, `poly_uniform_eta_4x` and
   `polyvec_matrix_pointwise_montgomery_row_lazy`, of each parameter set;
 - `polyeta_unpack` of ML-DSA-44 and -87;
 - `mldsa_keccakf1600_permute`, `mldsa_poly_ntt`,
   `mldsa_poly_invntt_tomont`, `mldsa_poly_uniform` and
   `mldsa_polyt0_pack`.

Each has a spec file and a proof file, as in the gcc builds, and
`lazy_eq_spec.ml` and `lazy_eq_proof.ml` are those of the
gcc12_O2_reduced_ram build. The statements of the functions are those of
that build, with the functional postconditions and the FIPS 204 theorems
unchanged. What differs is what the code forces:

 - the stack frames, which are those of the clang code. Some functions
   save d8-d15, and the code uses x18 as a scratch register, which
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI` does not cover, so the
   statements add `MAYCHANGE [X18]`;
 - the realignment of the stack: 52 functions align their frame to 32
   bytes by rounding the stack pointer down;
 - the stack probes: clang reads the stack at the bottom of a new frame
   (`ldr xzr, [sp]`). The 12 functions that allocate more than a page,
   `keypair_internal`, `pk_from_sk`, `signature_internal` and
   `verify_internal`, do so page by page, in a loop that ends on a signed
   comparison of the stack pointer with the bottom of the frame. Their
   statements assume `32768 <= val stackpointer` and
   `val stackpointer < 2 EXP 63`, so that these comparisons are decided,
   and those of the API functions, which call them,
   `33792 <= val stackpointer`; so do the FIPS 204 theorems;
 - the contracts of the C library: clang calls `memcpy` in more places, for
   example to copy the output of the inlined SHAKE squeezes, so the
   statements of `mld_H`, `compute_pack_t0_t1`, `poly_uniform`,
   `polyvec_matrix_pointwise_montgomery_row_lazy`, key generation,
   `pk_from_sk` and `verify_internal` also assume `memcpy_full_contract`
   (see "Hypotheses" in `../README.md`);
 - the pointers to `oid_map` outside the image (see above), for
   `prepare_domain_separation_prefix` and the pre-hash functions that call
   it.

The instructions of this build that the model did not decode before are
LDPSW, LDP and STP of S registers, LDUR and STUR of B registers and NEG
(vector).

The code of a function inlined into its callers cannot be proved once, as a
subroutine. As for mlkem-native's monolithic build
(`../../mlkem_native/gcc12_O2_mono/README.md`), the proofs state lemmas for
the inlined regions of code, from the head of a loop or region to its exit,
with the registers and stack slots as parameters, and use them in the
caller as a subroutine theorem is used. These lemmas are in the files
`inline_*.ml`, `*_inline.ml` and `*_stages.ml` of the proof directory,
which the proof files load; many are stated once for a shape of code and
instantiated for each parameter set. `inline_eta4x_main.ml` is part of the
three proofs of `poly_uniform_eta_4x`, which load it with `loadt` after
binding the names it uses, and is not a proof of its own.

`link.ml` loads all proof files and the FIPS 204 files `fips204.ml`,
`fips204_sign.ml`, `fips204_verify.ml` and `fips204_safe.ml` in one
session, as for the other builds (see "What is proved" in `../README.md`).
It states, proves and closes 212 contracts, and gives the FULL, CORRECT
and SAFE theorems of the 42 API functions and the 78 FIPS 204 theorems
with no assumptions. The lemma files that only one proof file loads run
inside its job; the others are loaded, and their lemmas proved, one after
the other before the jobs. The link took 8814 s with `HOL_PAR=1` on 8
domains of CPUs 0-31 of the machine of the reference configuration in
`../../../README.md`, of which the 68 jobs took 6603 s.
