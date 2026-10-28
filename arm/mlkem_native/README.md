# Compiled code from mlkem-native

This directory contains AArch64 code compiled from the portable C
implementation in [mlkem-native][1], for the same operations as some of the
hand-written kernels in `../mlkem`. The proofs in `../proofs` are done in
the same way as for those kernels, with the same specifications. The aim is
to explore what is involved in verifying compiler-generated rather than
hand-written code. The code here is only used for the proofs and is not
part of the library.

[1]: https://github.com/pq-code-package/mlkem-native

## Source of the code

The code is transcribed from the disassembly of the pre-built binaries in
the `binary` branch of mlkem-native (commit `83fb34a`). These were built
from mlkem-native commit `03392e41` by its `scripts/build-binaries`, as
recorded in `binaries/builds.json` there. We use the "multilevel" builds
(`examples/multilevel_build`), compiled with `CFLAGS` set to
`-O<level> -g -gdwarf-4 -gsplit-dwarf -fPIC`. The file
`mlkem_native_<function>_<compiler>_<level>.S` contains the code of the
function `mlkem_<function>` in the binary
`binaries/multilevel/<compiler>/<level>/libmlkem.so`, except that the
`basemul_k2`, `basemul_k3` and `basemul_k4` files are for
`mlkem512_polyvec_basemul_acc_montgomery_cached`,
`mlkem768_polyvec_basemul_acc_montgomery_cached` and
`mlkem1024_polyvec_basemul_acc_montgomery_cached` respectively.

| File                                          | Compiler     |
|-----------------------------------------------|--------------|
| mlkem_native_basemul_k2_gcc12_O2.S            | gcc 12.3.0   |
| mlkem_native_basemul_k3_gcc12_O2.S            | gcc 12.3.0   |
| mlkem_native_basemul_k4_gcc12_O2.S            | gcc 12.3.0   |
| mlkem_native_poly_invntt_tomont_gcc12_O2.S    | gcc 12.3.0   |
| mlkem_native_poly_mulcache_compute_gcc12_O2.S | gcc 12.3.0   |
| mlkem_native_poly_ntt_gcc12_O2.S              | gcc 12.3.0   |
| mlkem_native_poly_reduce_clang17_O2.S         | clang 17.0.6 |
| mlkem_native_poly_reduce_gcc12_O2.S           | gcc 12.3.0   |
| mlkem_native_poly_tobytes_gcc12_O2.S          | gcc 12.3.0   |
| mlkem_native_poly_tomont_gcc12_O2.S           | gcc 12.3.0   |

The SHA-256 hashes of the binaries used, which match those recorded in
`binaries/builds.json`, are:

```
binaries/multilevel/clang17/O2/libmlkem.so
  b7589e6e7ae228dd0dfa30424b0375e99a281979f70a5a40e6d163058fb50955
binaries/multilevel/gcc12/O2/libmlkem.so
  ed9a4710c0ec93ef1eab794f3e854dfadf92b45e08c76101cffdf1a36b035692
```

## Checking a transcription

After building the object file, `check_transcription.py` checks that its
code is byte-for-byte identical to the function in the binary, e.g. in the
`arm` directory:

```
make mlkem_native/mlkem_native_poly_reduce_gcc12_O2.o
python3 mlkem_native/check_transcription.py \
  mlkem_native/mlkem_native_poly_reduce_gcc12_O2.o \
  mlkem_native_poly_reduce_gcc12_O2 \
  <mlkem-native>/binaries/multilevel/gcc12/O2/libmlkem.so \
  mlkem_poly_reduce
```

Some functions use constant tables, which are transcribed into a read-only
data section and referenced with relocations, as for the hand-written code
in s2n-bignum: ADRP and ADD compute the address of a table, or ADRP and an
LDR of a Q register load a vector from it. For these, pairs of data symbols
in the object file and the binary are given as additional arguments, e.g.
`mlk_zetas mlk_zetas` for `mlkem_native_poly_mulcache_compute_gcc12_O2` and
`mlkem_native_poly_ntt_gcc12_O2`. Where the data in the binary has no
symbol, its address there can be given in hexadecimal instead, e.g.
`mlkem_native_poly_tomont_gcc12_O2_constants 0x6220` for
`mlkem_native_poly_tomont_gcc12_O2`. The script then checks that the tables
are identical and that the relocated instructions in the binary compute the
addresses of the tables there.
