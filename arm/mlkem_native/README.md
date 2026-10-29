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
`mlkem1024_polyvec_basemul_acc_montgomery_cached` respectively, and the
`rej_uniform` file is for `mlk_rej_uniform_c.constprop.0` (see below).

| File                                          | Compiler     |
|-----------------------------------------------|--------------|
| mlkem_native_basemul_k2_gcc12_O2.S            | gcc 12.3.0   |
| mlkem_native_basemul_k3_gcc12_O2.S            | gcc 12.3.0   |
| mlkem_native_basemul_k4_gcc12_O2.S            | gcc 12.3.0   |
| mlkem_native_keccakf1600_permute_gcc12_O2.S   | gcc 12.3.0   |
| mlkem_native_poly_invntt_tomont_gcc12_O2.S    | gcc 12.3.0   |
| mlkem_native_poly_mulcache_compute_gcc12_O2.S | gcc 12.3.0   |
| mlkem_native_poly_ntt_gcc12_O2.S              | gcc 12.3.0   |
| mlkem_native_poly_reduce_clang17_O2.S         | clang 17.0.6 |
| mlkem_native_poly_reduce_gcc12_O2.S           | gcc 12.3.0   |
| mlkem_native_poly_tobytes_gcc12_O2.S          | gcc 12.3.0   |
| mlkem_native_poly_tomont_gcc12_O2.S           | gcc 12.3.0   |
| mlkem_native_rej_uniform_gcc12_O2.S           | gcc 12.3.0   |

The rejection sampling in mlkem-native is done by the static function
`mlk_rej_uniform_c`, which has the target number of coefficients as an
argument as well as an offset from which to start. In the binary, gcc has
replaced it by a specialized copy `mlk_rej_uniform_c.constprop.0` with the
target fixed at 256, which is what `mlkem_poly_rej_uniform` and
`mlkem_poly_rej_uniform_x4` call, so this takes the arguments `r`,
`offset`, `buf` and `buflen`. Since the callers all pass a buffer length
of 168 or 504, the compiler has also dropped the initial check that there
is at least one group of 3 bytes in the buffer, so the specification
requires `3 <= buflen`. The callers also set X3 only once for several
calls, relying on it not being changed, which the ABI would allow, so the
specifications state exactly which registers may be changed. As for the
hand-written kernel, there is a proof of memory safety but not of
constant time, since the control flow depends on the values sampled.
Correctness and memory safety are proved together, since the simulation
of the loop is the same.

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

## The whole binary

For proofs about functions that call others, and eventually about the API
functions, `mlkem_native_libmlkem_gcc12_O2.S` is a transcription of the
start of the first loadable segment of the gcc 12 `-O2` binary, from
address 0 up to the end of the read-only data at 0x6480. This covers the
procedure linkage table, all the code and the constant tables. It was
generated from the disassembly, with the ELF header and other data as
`.quad` directives, and it assembles to exactly the bytes in the binary,
with no relocations. Since the ADRP instructions compute addresses relative
to the page of the instruction, the code works in the same way wherever it
is loaded, as long as that is at a multiple of 4096. To check it, the
symbol is given as `-` and the binary symbol as the address 0x0:

```
make mlkem_native/mlkem_native_libmlkem_gcc12_O2.o
python3 mlkem_native/check_transcription.py \
  mlkem_native/mlkem_native_libmlkem_gcc12_O2.o - \
  <mlkem-native>/binaries/multilevel/gcc12/O2/libmlkem.so 0x0
```

The proof file `../proofs/mlkem_native_libmlkem_gcc12_O2.ml` defines the
image, and has tools to transfer the theorems for the individual functions
to the same code in the image, at `pc + <address>` when the image is loaded
at `pc`. When `pc` is a multiple of 4096, and the image does not wrap around
the end of the address space, the relocated instructions in the individual
transcriptions are the same as those in the image, so the code of each
function and its data are parts of the image.

The proof for each function ends with the versions of its theorems for the
code in the image, `..._IMAGE_SUBROUTINE_CORRECT` and
`..._IMAGE_SUBROUTINE_SAFE`. For use in the proofs of callers, the
theorems of constant time and memory safety keep the frames of the
correctness theorems, as for the subroutines of other functions in
s2n-bignum.

Functions that call others are verified directly in the image, using those
theorems for the calls. So far this is done for
`mlkem_keccakf1600x4_permute`, at address 0x33a0, which calls
`mlkem_keccakf1600_permute` four times, the last time as a tail call, and
for the functions `mlkem768_polyvec_<op>` that apply `mlkem_poly_<op>` to
each polynomial of a vector, for `<op>` one of `add`, `frombytes`,
`invntt_tomont`, `mulcache_compute`, `ntt`, `reduce`, `tobytes` and
`tomont` (in the files `mlkem_native_polyvec_<op>_k3_gcc12_O2.ml`). As in
`common/fips203.ml`, a vector of k polynomials is given by its 256 * k
coefficients, of which those of polynomial j are `\i. x(256 * j + i)`.

The functions without transcriptions of their own are also verified
directly in the image, in the files
`../proofs/mlkem_native_<function>_gcc12_O2.ml` for `mlkem_<function>`. So
far these are `mlkem_poly_add`, `mlkem_poly_sub`, `mlkem_poly_frombytes`,
`mlkem_poly_decompress_d4`, `mlkem_poly_decompress_d10`,
`mlkem_poly_frommsg` and `mlkem_poly_tomsg`. As in `mlkem_decode` in
`common/fips203.ml`, the contents of a byte array are given as a number, so
that coefficient i of the result of `mlkem_poly_frombytes` is bits 12 * i
to 12 * i + 11 of the number given by the 384 bytes. The compression and
decompression of coefficients are given by the same arithmetic as
`mlkem_compress` and `mlkem_decompress` there, e.g. (3329 * y + 8) DIV 16
for decompression from 4 bits, but without using `common/fips203.ml`, which
takes several minutes to load.
