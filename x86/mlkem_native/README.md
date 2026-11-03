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
built in the same way on an x86-64 Linux machine, except for the stack
protector (see below). Following its `scripts/build-binaries`, as recorded
in `binaries/builds.json` there, the "multilevel" build
(`examples/multilevel_build`) of mlkem-native commit `03392e41` was
compiled in the nix shell `.#gcc12` (gcc 12.3.0 and binutils 2.41) with
`CFLAGS` set to `-O2 -g -gdwarf-4 -gsplit-dwarf -fPIC -fno-stack-protector`
and `-fdebug-prefix-map` for the source directory. The object files were
archived with `ar rcsD`, in the sorted order of their paths, and the
archive was linked with `ld -shared -Bsymbolic -soname libmlkem.so`, using
the version script `binaries/libmlkem.map`, to give `libmlkem.so`. The test
program of the example passes with it. The file
`mlkem_native_<function>_gcc12_O2.S` contains the code of the function
`mlkem_<function>` in this binary, except that the `basemul_k2`,
`basemul_k3` and `basemul_k4` files are for
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
| mlkem_native_poly_reduce_gcc12_O2.S           | gcc 12.3.0   |
| mlkem_native_poly_tobytes_gcc12_O2.S          | gcc 12.3.0   |
| mlkem_native_poly_tomont_gcc12_O2.S           | gcc 12.3.0   |
| mlkem_native_rej_uniform_gcc12_O2.S           | gcc 12.3.0   |

The rejection sampling in mlkem-native is done by the static function
`mlk_rej_uniform_c`, which has the target number of coefficients as an
argument as well as an offset from which to start. In the binary, as for
AArch64, gcc has replaced it by a specialized copy
`mlk_rej_uniform_c.constprop.0` with the target fixed at 256, which is what
`mlkem_poly_rej_uniform` and `mlkem_poly_rej_uniform_x4` call, so this
takes the arguments `r`, `offset`, `buf` and `buflen`. Since the callers
all pass a buffer length of 168 or 504, the compiler has also dropped the
initial check that there is at least one group of 3 bytes in the buffer, so
the specification requires 3 <= buflen. As for AArch64, the specifications
state exactly which registers may be changed, and there is a proof of
memory safety but not of constant time, since the control flow depends on
the values sampled. Correctness and memory safety are proved together,
since the simulation of the loop is the same. For the callers, whose input
is the output of SHAKE128 from a public seed, there is also a combined
theorem `..._IMAGE_SUBROUTINE_FULL`, as for AArch64, whose events are a
function of the arguments and of the list of 12-bit fields.

The SHA-256 hash of the binary used is:

```
multilevel/gcc12/O2/libmlkem.so
  864eca00b2123faab8a1c54caffbb4bee4c7ed5e3905a84c9f32bc4d522cb388
```

A binary built in another directory has a different hash, since the split
debug information records the paths of its files, but the contents of its
loaded segments are the same.

Unlike the AArch64 binaries, this one is built without gcc's stack
protector, which the nix shell otherwise enables. On x86-64 Linux, the
stack protector reads the guard at offset 0x28 from the base of the FS
segment, in thread-local storage, rather than through the global offset
table as on AArch64, and the x86 model has no segment bases. With the stack
protector, 44 functions copy the guard to the stack and check it before
returning. The other functions, including all of those here, are the same
in both binaries apart from their addresses, and the read-only data is at
the same addresses. This is a provisional choice, which may be revisited.

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
`mlk_zetas mlk_zetas` for `mlkem_native_poly_mulcache_compute_gcc12_O2` and
`mlkem_native_poly_ntt_gcc12_O2`. Where the data in the binary has no
symbol, its address there can be given in hexadecimal instead, e.g.
`mlkem_native_poly_tomont_gcc12_O2_constants 0x8070` for
`mlkem_native_poly_tomont_gcc12_O2`, and
`mlkem_native_poly_invntt_tomont_gcc12_O2_constants 0x8080 mlk_zetas
mlk_zetas` for `mlkem_native_poly_invntt_tomont_gcc12_O2`, which uses both
kinds of table. The script then checks that the tables are identical and
that the relocated displacements in the binary give the addresses of the
tables there.

## The compiled code

Unlike the hand-written code, the compiled code uses the legacy SSE2 forms
of vector instructions rather than the AVX2 ones, and 16-bit forms of
scalar instructions, some of which have been added to the x86 model in
`../proofs` for it.

The compiled code also uses the "red zone", the 128 bytes below the stack
pointer, which the System V ABI allows a function to use for data that is
not needed across calls, without moving the stack pointer. For example
`mlkem768_polyvec_basemul_acc_montgomery_cached` spills a 32-bit register
there, and `mlkem_poly_ntt` keeps its count of the layers there. The
subroutine forms of the theorems include the slot used in the stack region
that the function may change, and the theorems for the code after the
pushes of the callee-saved registers have its address as their
`stackpointer` parameter.

## The whole binary

For proofs about functions that call others, and eventually about the API
functions, `mlkem_native_libmlkem_gcc12_O2.S` is a transcription of the
binary as it is loaded, from address 0 up to the end of the read-only data
at 0x82a0. This covers its first two loadable segments, one with the ELF
header and dynamic linking information and one with the procedure linkage
table and all the code, the start of the third, with the constant tables,
and the padding between them. It was generated from the disassembly, with
the data as `.quad` directives, and it assembles to exactly these bytes,
with no relocations. To check it, the symbol is given as `-` and the binary
symbol as the address 0x0, and the whole `.text` section of the object file
is then compared with the contents of memory from that address when the
binary is loaded:

```
make mlkem_native/mlkem_native_libmlkem_gcc12_O2.o
python3 mlkem_native/check_transcription.py \
  mlkem_native/mlkem_native_libmlkem_gcc12_O2.o - \
  <build>/multilevel/gcc12/O2/libmlkem.so 0x0
```

The proof file `../proofs/mlkem_native_libmlkem_gcc12_O2.ml` defines the
image, and has tools to transfer the theorems for the individual functions
to the same code in the image, at `pc + <address>` when the image is loaded
at `pc`. The code refers to other code and data in the image only by
displacements from the instruction pointer, so the relocated displacements
in the individual transcriptions are then the same as those in the image,
wherever it is, and the code of each function and its data are parts of the
image. The theorems about the image only assume that `pc` is a multiple of
16, since the vectors of constants read by SSE instructions must be
aligned. Unlike those for AArch64, they do not assume that it is at a
multiple of 4096, as it is when the dynamic loader loads it, or that it
does not wrap around the end of the address space.

The proof for each function ends with the versions of its theorems for the
code in the image, `..._IMAGE_SUBROUTINE_CORRECT` and
`..._IMAGE_SUBROUTINE_SAFE`, and for `mlkem_keccakf1600_permute` also
`..._IMAGE_SUBROUTINE_FULL`. As on AArch64, the safety theorems keep the
frames of the correctness theorems, for use in the proofs of callers.

Functions that call others are verified directly in the image, using those
theorems for the calls. So far this is done for
`mlkem_keccakf1600x4_permute`, at address 0x4740, which calls
`mlkem_keccakf1600_permute` four times, the last time as a tail call, for
`mlkem_keccakf1600x4_extract_bytes` and `mlkem_keccakf1600x4_xor_bytes`,
which do the same with the functions for one state and take their seventh
argument on the stack, and for the functions `mlkem<n>_polyvec_<op>` that
apply `mlkem_poly_<op>` to each polynomial of a vector, for `<op>` one of
`add`, `frombytes`, `invntt_tomont`, `mulcache_compute`, `ntt`, `reduce`,
`tobytes` and `tomont` and `<n>` one of 512, 768 and 1024 (in the files
`mlkem_native_polyvec_<op>_k<k>_gcc12_O2.ml` for vectors of k = 2, 3 or 4
polynomials), and for `mlkem<n>_polyvec_compress_du` and
`mlkem<n>_polyvec_decompress_du`, which apply `mlkem_poly_compress_d10` and
`mlkem_poly_decompress_d10` for 512 and 768 and `mlkem_poly_compress_d11`
and `mlkem_poly_decompress_d11` for 1024 (with `<op>` `compress_du` and
`decompress_du` in the file names), six of which are compiled as loops over
the polynomials, unrolled in the proofs. As in `common/fips203.ml`, a
vector of k polynomials is given by its 256 * k coefficients, of which
those of polynomial j are `\i. x(256 * j + i)`. As for the functions they
call, the theorems give the stack used, below the return address, and the
stack pointer after the return, which callers need, and in the theorems of
constant time and memory safety the stack that may be read includes the
return address.

The functions without transcriptions of their own are also verified
directly in the image, in the files
`../proofs/mlkem_native_<function>_gcc12_O2.ml` for `mlkem_<function>`. So
far these are `mlkem_poly_add`, `mlkem_poly_sub`, `mlkem_poly_frombytes`,
`mlkem_poly_frommsg`, `mlkem_poly_tomsg`, `mlkem_poly_decompress_d4`,
`mlkem_poly_decompress_d5`, `mlkem_poly_decompress_d10`,
`mlkem_poly_decompress_d11`, `mlkem_poly_compress_d4`,
`mlkem_poly_compress_d5`, `mlkem_poly_compress_d10`,
`mlkem_poly_compress_d11`, `mlkem_keccakf1600_extract_bytes`,
`mlkem_keccakf1600_xor_bytes`, `mlkem_poly_cbd2` and `mlkem_poly_cbd3`. The
compiler has vectorized `mlkem_poly_add` and `mlkem_poly_sub` with aligned
SSE loads and stores, so their specifications require the polynomials to be
aligned, as they are in mlkem-native, as do those of `mlkem_poly_tomont`
and of the functions that call these. Likewise `mlkem_poly_decompress_d11`
uses aligned stores for its output and `mlkem_poly_compress_d11` aligned
loads for its input, so their specifications require those polynomials to
be aligned, as do those of `mlkem1024_polyvec_decompress_du` and
`mlkem1024_polyvec_compress_du`, which call them. As for
`mlkem_keccakf1600_permute`, there are also combined theorems
`..._IMAGE_SUBROUTINE_FULL` for the functions that extract bytes from
Keccak states and XOR bytes into them, one or four states at a time, for
callers whose events depend on the results.

The SHA-3 and SHAKE functions are also verified directly in the image, with
the same specifications as on AArch64 (see
`../../arm/mlkem_native/README.md`) apart from the stack, starting with the
static function `mlk_keccak_absorb_once`, at 0x32b0 in the image, which
absorbs a whole message into a state. For these, the permutation
`keccak 24` of `../proofs/utils/keccak_spec.ml` is shown to be
`keccak_f1600` of `common/fips202.ml` on the state as a 1600-bit word in
`../proofs/utils/keccak_fips202.ml`, as for AArch64, and the theorem for
`mlkem_keccakf1600_permute` is restated in that form at the end of its
proof. gcc zeroes the state with REP STOSQ, as an inline memset, so the
specifications of `mlk_keccak_absorb_once` and of the functions that call
it assume that the direction flag DF is clear, as the ABI requires on
entry. Since the state is not known to be aligned, the inline memset stores
zero quadwords at the two ends of the state and clears the quadwords in
between from the first multiple of 8 above its start, and the tactics
`MEMSET_PREP_TAC`, `MEMSET_STEP_TAC` and `MEMSET_DONE_TAC` in
`../proofs/mlkem_native_libmlkem_gcc12_O2.ml` put the parts together for
any alignment. The same is done for `mlkem_shake128_absorb_once`,
`mlkem_shake128_squeezeblocks`, `mlkem_shake128_init`,
`mlkem_shake128_release`, `mlkem_sha3_256`, `mlkem_sha3_512` and
`mlkem_shake256`, of which `mlkem_shake128_release` zeroes the context in
the same way, and the hash functions keep the state on the stack, where
`mlkem_shake256` aligns it to 32 bytes, so that its offset in the stack
frame depends on the stack pointer, which the proof keeps symbolic. Where
the hypotheses are the same, the correctness and safety theorems are
derived from the combined ones `..._IMAGE_SUBROUTINE_FULL`.

The functions for four states at once are verified in the same way, with
the theorem for `mlkem_keccakf1600x4_permute` also restated for the states
as 1600-bit words, starting with the static function
`mlk_keccak_absorb_once_x4`, specialized by gcc to the first byte 0x1F of
the padding as `mlk_keccak_absorb_once_x4.constprop.0`, at 0x35d0 in the
image. As on AArch64, the four states must be zero at the start, since its
callers zero them. Its seventh argument, the length of the messages, is on
the stack, and it passes the seventh argument of
`mlkem_keccakf1600x4_xor_bytes` on the stack as a 64-bit word, of which the
callee reads 32 bits, in the form given by `STACK_ARG32_TAC` in
`../proofs/mlkem_native_libmlkem_gcc12_O2.ml`. The same is done for
`mlkem_shake128x4_absorb_once`, which zeroes the context of 800 bytes with
an inline memset as above before calling it,
`mlkem_shake128x4_squeezeblocks`, `mlkem_shake128x4_init` and
`mlkem_shake128x4_release`, which zeroes the context in the same way.
Finally `mlkem_shake256x4` realigns its stack frame to 32 bytes, as
`mlkem_shake256` does its state, and where the code for AArch64 calls
`memset` and `memcpy` gcc inlines them: the rest of each output is copied
from a buffer on the stack with REP MOVSQ for the quadwords between the
first and the last 8 bytes, or with smaller moves for fewer than 8 bytes.
Each of the four copies is a lemma in the proof, for correctness and for
the events, of which the latter gives the events of the copy as a function
of the addresses and the length, and the simulation of a REP MOVSQ of a
symbolic number of quadwords is completed by `MEMCPY_MOVSQ_STEP_TAC` in the
proof.

`mlkem_poly_rej_uniform`, which samples a polynomial uniformly modulo q
from a seed of 34 bytes using `mlkem_shake128_absorb_once`,
`mlkem_shake128_squeezeblocks` and `mlk_rej_uniform_c`, is verified in the
image with the same specification as on AArch64 apart from the stack, and
with the same theorem of constant time and memory safety, by which its
events depend only on the addresses and on the seed, which is public,
through the samples and the number of iterations of the loop. Like
`mlkem_shake256`, it realigns its stack frame to 32 bytes, so the addresses
of the state and the buffer in it depend on the stack pointer, which the
proof keeps symbolic, and it zeroes the buffer with REP STOSQ, so its
specification assumes that DF is clear. The same is done for
`mlkem_poly_rej_uniform_x4`, which samples four polynomials from four seeds
64 bytes apart using the fourfold SHAKE128 functions. Its loop test
combines the comparisons of three of the numbers of samples with 255 by
SETBE and OR, and compares the fourth only if the first three are complete,
so the template of its events gives those of the first test and of each
iteration of the loop by two functions, for the two cases.

`mlkem512_gen_matrix`, `mlkem768_gen_matrix` and `mlkem1024_gen_matrix`,
which generate the matrix or its transpose from a seed by sampling its
entries four at a time with `mlkem_poly_rej_uniform_x4`, and the last of
the nine for ML-KEM-768 with `mlkem_poly_rej_uniform`, from copies of the
seed with the indices of the entries in four buffers on the stack, are
verified in the image with the same specifications as on AArch64 apart from
the stack, and with the same theorems of constant time and memory safety,
by which their events depend only on the addresses, the seed and the flag
for the transpose. They also align the buffers to 32 bytes, and the proofs
give the addresses in them and in the stack of the callees below them as
constant offsets from a variable for the bottom of the stack of
`mlkem_poly_rej_uniform_x4`, with the facts about its alignment and its
position in the frame.
