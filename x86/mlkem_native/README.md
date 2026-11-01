# Compiled code from mlkem-native

This directory contains x86-64 code compiled from the portable C
implementation in [mlkem-native][1], for the same operations as some of the
hand-written kernels in `../mlkem`, as `../../arm/mlkem_native` does for
AArch64. The code here is only used for the proofs and is not part of the
library.

[1]: https://github.com/pq-code-package/mlkem-native

The proofs in `../proofs` are done in the same way as for the AArch64 code,
with the same specifications, which are those of the hand-written AArch64
kernels. Some of these differ from the specifications of the hand-written
x86 kernels, e.g. `forward_ntt` rather than `avx2_forward_ntt` in
`../../common/mlkem_mldsa.ml`, since the AVX2 code in mlkem-native keeps
the coefficients in a different order, but the C code uses the same order
on all platforms.

## Source of the code

The `binary` branch of mlkem-native (commit `83fb34a`) only has binaries
for AArch64, so the code is transcribed from the disassembly of a binary
built in the same way on an x86-64 Linux machine. Following its
`scripts/build-binaries`, as recorded in `binaries/builds.json` there, the
"multilevel" build (`examples/multilevel_build`) of mlkem-native commit
`03392e41` was compiled in the nix shell `.#gcc12` (gcc 12.3.0 and binutils
2.41) with `CFLAGS` set to `-O2 -g -gdwarf-4 -gsplit-dwarf -fPIC` and
`-fdebug-prefix-map` for the source directory. The object files were
archived with `ar rcsD`, in the sorted order of their paths, and the
archive was linked with `ld -shared -Bsymbolic -soname libmlkem.so`, using
the version script `binaries/libmlkem.map`, to give `libmlkem.so`. The test
program of the example passes with it. The file
`mlkem_native_<function>_gcc12_O2.S` contains the code of the function
`mlkem_<function>` in this binary.

| File                                          | Compiler     |
|-----------------------------------------------|--------------|
| mlkem_native_poly_mulcache_compute_gcc12_O2.S | gcc 12.3.0   |
| mlkem_native_poly_reduce_gcc12_O2.S           | gcc 12.3.0   |
| mlkem_native_poly_tobytes_gcc12_O2.S          | gcc 12.3.0   |

The SHA-256 hash of the binary used is:

```
multilevel/gcc12/O2/libmlkem.so
  ed13c628dfb86048ffe7163833052ad933ab63c1aa3b8110025ed0cf4f5b5e89
```

A binary built in another directory has a different hash, since the split
debug information records the paths of its files, but the contents of its
loaded segments are the same.

## Checking a transcription

After building the object file, `check_transcription.py` checks that its
code is byte-for-byte identical to the function in the binary, e.g. in the
`x86` directory:

```
make mlkem_native/mlkem_native_poly_reduce_gcc12_O2.o
python3 mlkem_native/check_transcription.py \
  mlkem_native/mlkem_native_poly_reduce_gcc12_O2.o \
  mlkem_native_poly_reduce_gcc12_O2 \
  <build>/multilevel/gcc12/O2/libmlkem.so \
  mlkem_poly_reduce
```

Some functions use constant tables, which are transcribed into a read-only
data section and referenced with RIP-relative addressing, giving
relocations in the object file. For these, pairs of data symbols in the
object file and the binary are given as additional arguments, e.g.
`mlk_zetas mlk_zetas` for `mlkem_native_poly_mulcache_compute_gcc12_O2`.
The script then checks that the tables are identical and that the relocated
displacements in the binary give the addresses of the tables there.

## The compiled code

Unlike the hand-written code, the compiled code uses the legacy SSE2 forms
of vector instructions rather than the AVX2 ones, and 16-bit forms of
scalar instructions, some of which have been added to the x86 model in
`../proofs` for it.
