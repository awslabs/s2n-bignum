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
`basemul_k2` files are for `mlkem512_polyvec_basemul_acc_montgomery_cached`.

| File                                  | Compiler     | libmlkem.so SHA-256 |
|---------------------------------------|--------------|---------------------|
| mlkem_native_basemul_k2_gcc12_O2.S    | gcc 12.3.0   | ed9a4710c0ec93ef... |
| mlkem_native_poly_reduce_clang17_O2.S | clang 17.0.6 | b7589e6e7ae228dd... |
| mlkem_native_poly_reduce_gcc12_O2.S   | gcc 12.3.0   | ed9a4710c0ec93ef... |
| mlkem_native_poly_tobytes_gcc12_O2.S  | gcc 12.3.0   | ed9a4710c0ec93ef... |

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
