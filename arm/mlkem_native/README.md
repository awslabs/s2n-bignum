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
Likewise `mlkem768_polyvec_compress_du` and
`mlkem768_polyvec_decompress_du` apply `mlkem_poly_compress_d10` and
`mlkem_poly_decompress_d10` to each polynomial. Similarly
`mlkem_keccakf1600x4_extract_bytes` and `mlkem_keccakf1600x4_xor_bytes`
apply `mlkem_keccakf1600_extract_bytes` and `mlkem_keccakf1600_xor_bytes`
(see below) to each of four consecutive Keccak states.

The functions without transcriptions of their own are also verified
directly in the image, in the files
`../proofs/mlkem_native_<function>_gcc12_O2.ml` for `mlkem_<function>`. So
far these are `mlkem_poly_add`, `mlkem_poly_sub`, `mlkem_poly_frombytes`,
`mlkem_poly_compress_d4`, `mlkem_poly_compress_d10`,
`mlkem_poly_decompress_d4`, `mlkem_poly_decompress_d10`,
`mlkem_poly_frommsg`, `mlkem_poly_tomsg`, `mlkem_poly_cbd2`,
`mlkem_keccakf1600_extract_bytes` and `mlkem_keccakf1600_xor_bytes`. As in
`mlkem_decode` in `common/fips203.ml`, the contents of a byte array are
given as a number, so that coefficient i of the result of
`mlkem_poly_frombytes` is bits 12 * i to 12 * i + 11 of the number given by
the 384 bytes. The compression and decompression of coefficients are given
by the same arithmetic as `mlkem_compress` and `mlkem_decompress` there,
e.g. (3329 * y + 8) DIV 16 for decompression from 4 bits, but without using
`common/fips203.ml`, which takes several minutes to load. Likewise, as for
`mlkem_cbd 2`, coefficient i of the result of `mlkem_poly_cbd2` is the
number of 1 bits among bits 4 * i and 4 * i + 1 of the number given by the
128 bytes, minus the number among bits 4 * i + 2 and 4 * i + 3, but as a
16-bit integer rather than modulo 3329.

For the Keccak functions, the state is a 1600-bit word S, as in
`common/fips202.ml`, which is `read (memory :> wbytes a) s` for the 200
bytes at its address a. Then `mlkem_keccakf1600_extract_bytes` gives bytes
off to off + len - 1 of the state, which as a number are
(val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len), and
`mlkem_keccakf1600_xor_bytes` XORs len bytes of data, as a number m, into
the state from byte off, giving word_xor S (word(2 EXP (8 * off) * m)). For
off = 0 and len the rate, this is the XOR of a block into the state in
`keccak_absorb` there.

The permutation `keccak 24` of `../proofs/utils/keccak_spec.ml`, the
specification of the Keccak code in s2n-bignum, is shown to be
`keccak_f1600` of `common/fips202.ml` on the state as a 1600-bit word in
`../proofs/utils/keccak_fips202.ml`, and the theorem for
`mlkem_keccakf1600_permute` is restated in that form at the end of its
proof, as
`MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600`.

These are used by the static function `mlk_keccak_absorb_once`, at 0x23b0
in the image, which absorbs a whole message into a state for the SHA-3 and
SHAKE functions, and is verified in
`../proofs/mlkem_native_keccak_absorb_once_gcc12_O2.ml`. As in
`keccak_sponge` in `common/fips202.ml`, a message of mlen bytes, as a
number M, is padded to the number
P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad r p mlen), which is
mlen DIV r + 1 blocks of r bytes, for the rate r and the first byte p of
the padding. The final state is then keccak_absorb r P (mlen DIV r), after
the whole blocks of the message, XORed with the last block of P, so that
keccak_f1600 of it is keccak_absorb r P (mlen DIV r + 1), the state in
`keccak_sponge` after absorbing. In mlkem-native, that last permutation is
the first step of squeezing.

The SHAKE128 functions `mlkem_shake128_init`, `mlkem_shake128_absorb_once`,
`mlkem_shake128_squeezeblocks` and `mlkem_shake128_release` work on a
context of 224 bytes, of which the first 200 are the state.
`mlkem_shake128_absorb_once` calls `mlk_keccak_absorb_once` with r = 168
and p = 0x1F, as for `shake128`. For a state S,
`mlkem_shake128_squeezeblocks` outputs nblocks blocks of 168 bytes, block i
being the first 168 bytes of keccak_squeeze (i + 1) S, and leaves the state
keccak_squeeze nblocks S, so that after `mlkem_shake128_absorb_once` these
are the bytes of the output of `shake128`. Finally `mlkem_shake128_init`
does nothing and `mlkem_shake128_release` zeroes the context.

For `mlkem_sha3_256` and `mlkem_sha3_512`, the input is given as a list of
bytes, and the result, as a number, is that of `sha3_256` or `sha3_512` in
`common/fips202.ml`, using the lemmas about `keccak_sponge` at the end of
`../proofs/utils/keccak_fips202.ml`. They keep the state on the stack.

Some of these functions, such as `mlkem_poly_compress_d4` and
`mlkem_sha3_256`, have a stack protector: they copy the stack guard to the
stack and check it before returning. They read the address of the guard
from the global offset table (GOT) at 0x1fff8, in the read-write segment of
the binary, which is not part of the image. So their specifications have
the GOT entry as a precondition,
`read (memory :> bytes64 (word(pc + 0x1fff8))) s = guard`, and require that
neither the GOT entry nor the guard is overwritten, so that the check
succeeds and `__stack_chk_fail` is never called. The specifications of
functions that call them, such as `mlkem768_polyvec_compress_du`, have the
same conditions.
