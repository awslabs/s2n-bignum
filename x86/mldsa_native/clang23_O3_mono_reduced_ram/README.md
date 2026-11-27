# The clang 23 -O3 monolithic reduced-RAM build

This directory is for mldsa-native's `libmldsa.so` built with clang 23 and
`-O3`, in the monolithic layout and the reduced-RAM configuration
`MLD_CONFIG_REDUCE_RAM`: the x86-64
`binaries/reduced-ram/multilevel-mono/clang23/O3/libmldsa.so` of the
`binary` branch of mldsa-native, at commit `01be6a9` ("binaries: Rebuild
x86-64 ML-DSA without stack protection"), the commit of the binaries of the
gcc12_O2 and gcc12_O2_reduced_ram builds (see `../README.md` and
`../gcc12_O2_reduced_ram/README.md`). The C code is that of the
gcc12_O2_reduced_ram build, and so are the statements, with the changes
that the code forces (see "Compared with the gcc 12 -O2 reduced-RAM
build").

## Source of the code

The binary is from the same run of `scripts/build-binaries` as the gcc 12
binaries of that commit: the linker recorded the same directory as
`RUNPATH`
(`/tmp/native-x86-no-stack-protector.16lXCUsN/mldsa-source/outputs/out/lib`).
In the monolithic layout (`multilevel-mono`), the script compiles the
single translation unit
`examples/monolithic_build_multilevel/mldsa_native_all.c`, which has the
code shared by the three parameter sets once, with the namespace `mldsa_`,
and the rest once per parameter set, and links it into `libmldsa.so` as for
the other layout (see "Source of the code" in `../README.md`), with `-O3`
and `-DMLD_CONFIG_REDUCE_RAM`. The compiler is clang 23.1.3, as the
`.comment` section of the binary records. As for the gcc 12 binaries, the
stack protector is off: the code does not read the guard at offset 0x28 of
the FS segment, and the binary does not import `__stack_chk_fail`. It
imports `memcpy`, `memset` and `randombytes`.

The SHA-256 hash of the binary used is:

```
reduced-ram/multilevel-mono/clang23/O3/libmldsa.so
  38c2db03432e1f0384bb05a2fc3c0e85f612e3122c4a19773cbc0070b3ba8d49
```

`libmldsa.S` transcribes the image, from address 0 to the end of the
read-only data at `libmldsa_size` = 0x25960, and is the same as the binary
byte for byte. The table `oid_map` of `mld_get_hash_oid`, 12 pointers that
the dynamic loader relocates, is not in the image but in `.data.rel.ro`
after it, at 0x27df0: the statements of the functions that read it assume
its relocated contents, as for the GOT entries of the C library functions
(see `../../proofs/mldsa_native/clang23_O3_mono_reduced_ram/oid_map.ml`).
`../../proofs/mldsa_native/clang23_O3_mono_reduced_ram/` has the layout,
the definition of the image and the proofs.

To regenerate the files of the build, in the `x86` directory, with
`<build>` the `binaries` directory of a checkout of mldsa-native at commit
`01be6a9` of the `binary` branch (see "Source of the code" in
`../README.md` for the x86-64 `as` that the first command needs):

```
python3 mldsa_native/gen_libmldsa_s.py \
  <build>/reduced-ram/multilevel-mono/clang23/O3/libmldsa.so \
  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram \
  "clang 23, -O3, monolithic, reduced RAM" \
  reduced-ram/multilevel-mono/clang23/O3/libmldsa.so $PWD/../include \
  > mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.S
python3 mldsa_native/gen_layout.py \
  --name reduced-ram/multilevel-mono/clang23/O3/libmldsa.so \
  <build>/reduced-ram/multilevel-mono/clang23/O3/libmldsa.so \
  > proofs/mldsa_native/clang23_O3_mono_reduced_ram/layout.ml
python3 ../tools/native_proofs_mk.py mldsa_native clang23_O3_mono_reduced_ram \
  > mldsa_native/clang23_O3_mono_reduced_ram/proofs.mk
python3 ../tools/native_link.py mldsa_native clang23_O3_mono_reduced_ram \
  > proofs/mldsa_native/clang23_O3_mono_reduced_ram/link.ml
```

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

 - the stack frames, which are those of the clang code;
 - the contracts of the C library: clang calls `memset` through the
   procedure linkage table where gcc zeroes with inlined stores, and
   `memcpy` in more places, so the theorems of the API functions assume
   `memset_full_contract` and `memcpy_full_contract`, and those of
   `compute_pack_t0_t1`, `poly_challenge`, `poly_uniform` and
   `poly_uniform_eta_4x` the contracts of what they call (see
   "Hypotheses" in `../README.md`);
 - the realignment of the stack: 49 functions align it to 32 bytes with
   `and rsp, -32`;
 - the table `oid_map` outside the image (see above), for
   `prepare_domain_separation_prefix` and the functions into which it is
   inlined.

The code of a function inlined into its callers cannot be proved once, as a
subroutine. As for mlkem-native's monolithic build on AArch64
(`../../../arm/mlkem_native/gcc12_O2_mono/README.md`), the proofs state
lemmas for the inlined regions of code, from the head of a loop or region
to its exit, with the registers and stack slots as parameters, and use them
in the caller as a subroutine theorem is used. These lemmas are in the
files `inline_*.ml`, `*_inline.ml`, `*_lemmas.ml` and `*_stages.ml` of the
proof directory, which the proof files load; many are stated once for a
shape of code and instantiated for each parameter set.

`link.ml` loads all proof files and the FIPS 204 files `fips204.ml`,
`fips204_sign.ml`, `fips204_verify.ml` and `fips204_safe.ml` in one
session, as for the other builds (see "What is proved" in `../README.md`).
It states, proves and closes 212 contracts, and gives the FULL, CORRECT
and SAFE theorems of the 42 API functions and the 78 FIPS 204 theorems
with no assumptions. The lemma files that only one proof file loads run
inside its job; the others are loaded, and their lemmas proved, one after
the other before the jobs. The link took 9967 s with `HOL_PAR=1` on 8
domains of CPUs 0-31 of the machine of the reference configuration in
`../../../README.md`, of which the 68 jobs took 2399 s.
