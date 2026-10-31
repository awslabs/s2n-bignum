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
`tomont` (in the files `mlkem_native_polyvec_<op>_k3_gcc12_O2.ml`), and
likewise for `mlkem512_polyvec_<op>` and `mlkem1024_polyvec_<op>` (in the
files `..._k2_gcc12_O2.ml` and `..._k4_gcc12_O2.ml`), some of which are
compiled as loops over the polynomials, unrolled in the proofs. As in
`common/fips203.ml`, a vector of k polynomials is given by its 256 * k
coefficients, of which those of polynomial j are `\i. x(256 * j + i)`.
Likewise `mlkem768_polyvec_compress_du` and
`mlkem768_polyvec_decompress_du` apply `mlkem_poly_compress_d10` and
`mlkem_poly_decompress_d10` to each polynomial, as do the ML-KEM-512
versions, while the ML-KEM-1024 ones use `mlkem_poly_compress_d11` and
`mlkem_poly_decompress_d11`. Similarly
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
`mlkem_keccakf1600_extract_bytes` and `mlkem_keccakf1600_xor_bytes`, and
for ML-KEM-512 and ML-KEM-1024 also `mlkem_poly_compress_d5`,
`mlkem_poly_compress_d11`, `mlkem_poly_decompress_d5`,
`mlkem_poly_decompress_d11` and `mlkem_poly_cbd3`. As in
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
16-bit integer rather than modulo 3329, and similarly for
`mlkem_poly_cbd3` with three bits each from 192 bytes.

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

The functions for four SHAKE128 states at once, used to generate the
matrix, work on a context of 800 bytes, the four states one after another.
The static function `mlk_keccak_absorb_once_x4`, at 0x27a0 in the image,
which gcc specializes to p = 0x1F, absorbs four messages of the same length
into the four states as `mlk_keccak_absorb_once` does into one, using
`mlkem_keccakf1600x4_xor_bytes` and `mlkem_keccakf1600x4_permute`, except
that its callers zero the states first. For it and its callers, the theorem
for `mlkem_keccakf1600x4_permute` is also restated for 1600-bit words, as
`MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600`.
Then `mlkem_shake128x4_squeezeblocks` outputs nblocks blocks of 168 bytes
from each state into four buffers, as `mlkem_shake128_squeezeblocks` does
for one, and `mlkem_shake128x4_init` does nothing.

For `mlkem_sha3_256` and `mlkem_sha3_512`, the input is given as a list of
bytes, and the result, as a number, is that of `sha3_256` or `sha3_512` in
`common/fips202.ml`, using the lemmas about `keccak_sponge` at the end of
`../proofs/utils/keccak_fips202.ml`. They keep the state on the stack.
Likewise, for `mlkem_shake256` with an output of outlen bytes, the result is
that of `list_of_seq (shake256 inp) outlen`. It extracts
MIN (outlen - 136 * i) 136 bytes of the state in iteration i of its loop,
and it aligns the state on the stack to 32 bytes, so its address depends on
whether the stack pointer is a multiple of 32.

Using these, `mlkem768_check_sk`, and likewise `mlkem512_check_sk` and
`mlkem1024_check_sk`, is the hash check of the decapsulation key in
FIPS 203. With the encapsulation key in it as a list of bytes ek and the
hash stored after it as a number h, it returns 0 if h is
`num_of_bytelist(sha3_256 ek)` and -5 otherwise, comparing them in constant
time. The functions `mlkem512_poly_getnoise_eta2` and
`mlkem1024_poly_getnoise_eta2` sample a polynomial with eta = 2 from a seed
and a nonce, as PRF and SamplePolyCBD in FIPS 203: the result is that of
`mlkem_poly_cbd2` on the first 128 bytes of `shake256` of the seed followed
by the nonce.

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

Most of the functions above the hash layer call memset and memcpy from the
C library, and randombytes, through the PLT and GOT of the binary, which
are not part of the image. (The binary also calls `__stack_chk_fail`, but
only when the check of the stack guard fails, which the proofs show never
happens.) Their behaviour is assumed, as notional high-level contracts in
`../proofs/utils/mlkem_native_libc.ml` that are hypotheses of the theorems
for their callers. For example, `memset_contract mf ea el ev` states the
behaviour of memset at the address mf, which the caller reads from the GOT,
in any state where the region (ea,el), containing its code and data, has
the contents ev, which the caller must not overwrite: it sets the len bytes
at dst to the low byte of c, and may change the registers that the ABI
allows and X18 and X30, but no other memory. memcpy copies len bytes
between regions that do not overlap, and randombytes writes len bytes, with
no assumption about their values or about its result. For constant time and
memory safety, `memset_safety_contract` and the others state that the
events of a call are a function of its arguments and that it only accesses
those regions, and the events of the callers are given in terms of those
functions. So far, these are used for `mlkem_shake128x4_absorb_once`, which
zeroes the context with memset before calling `mlk_keccak_absorb_once_x4`
with r = 168 and p = 0x1F, as for `shake128`, for
`mlkem_shake128x4_release`, which zeroes it, and for `mlkem_shake256x4`,
which computes SHAKE256 of four inputs of the same length, with the results
as for `mlkem_shake256`. It absorbs them with `mlk_keccak_absorb_once_x4`
with r = 136 into a context on the stack, which it zeroes with memset
before and after, squeezes the whole blocks of 136 bytes directly into the
outputs, and the rest into buffers on the stack, from which it copies them
with memcpy. Its last two arguments, the fourth input and the length of the
inputs, are on the stack, so its specification has them as
`read (memory :> bytes64 stackpointer) s = in3` and
`read (memory :> bytes64 (word_add stackpointer (word 8))) s = word inlen`.

Using it, `mlkem512_poly_getnoise_eta1_4x`, `mlkem768_poly_getnoise_eta1_4x`
and `mlkem1024_poly_getnoise_eta1_4x` sample four noise polynomials with
eta = eta1 from a seed and four nonces, as PRF and SamplePolyCBD in
FIPS 203. As for `mlkem512_poly_getnoise_eta2`, each result is that of
`mlkem_poly_cbd3` (for ML-KEM-512) or `mlkem_poly_cbd2` on the first 192
or 128 bytes of `shake256` of the seed followed by the nonce. Similarly,
`mlkem512_poly_getnoise_eta1122_4x` samples two polynomials with eta = 3
and two with eta = 2. The fourth nonce is on the stack. The functions
`mlkem*_poly_getnoise_eta1_4x` skip the fourth polynomial if its pointer is
null, which the callers for ML-KEM-768 use, so their specifications only
give the fourth result if the pointer is not null, and its region in the
frame is empty if it is null: a caller giving a buffer there must show
that it is not at address 0.

`mlkem_poly_rej_uniform` samples a polynomial uniformly modulo q from a
seed of 34 bytes, as SampleNTT in FIPS 203 does for one entry of the
matrix, using `mlkem_shake128_absorb_once`, `mlkem_shake128_squeezeblocks`
and `mlk_rej_uniform_c`. Its loop squeezes one more block of 168 bytes
until there are 256 samples, so its specification has the hypothesis that
there are at least 256 samples, 12-bit fields below 3329, among the first
504 + 168 * k bytes of `shake128` of the seed for some k, and the result
is the first 256 of them. It has no constant-time and memory safety proof
yet: since the number of iterations depends on the output of SHAKE128
(which is public), such a proof would need theorems for the hash functions
that combine their correctness and their events.

`mlkem_poly_rej_uniform_x4` samples four polynomials in the same way from
four seeds 64 bytes apart, using the fourfold SHAKE128 functions. Its loop
squeezes one more block of each until all four have 256 samples, so its
specification has the same hypothesis for each seed, with the same k, and
it has no constant-time and memory safety proof yet either.

`mlkem512_gen_matrix`, `mlkem768_gen_matrix` and `mlkem1024_gen_matrix`
generate the matrix of a parameter set from a seed of 32 bytes. Entry
(i,j) is sampled as above from the seed followed by the bytes j and i, as
for the matrix in FIPS 203, or i and j for the transposed matrix if the
flag is nonzero, four entries at a time with `mlkem_poly_rej_uniform_x4`
and the last one for ML-KEM-768 with `mlkem_poly_rej_uniform`. Their
specifications have the hypothesis that there are at least 256 samples for
each entry within the first 504 + 168 * k bytes, with the same k for all
entries. They have no constant-time and memory safety proofs yet either.

`mlkem512_check_pk`, `mlkem768_check_pk` and `mlkem1024_check_pk` do the
modulus check of FIPS 203 on an encapsulation key: they decode the vector
in its first 384 * k bytes, reduce it, encode it again and compare the
result with the key in constant time, so they return 0 if all the 12-bit
fields of those bytes are below q = 3329, and -4 otherwise.

`mlkem768_indcpa_keypair_derand` is the key generation of K-PKE for
ML-KEM-768, and its specification is in terms of FIPS 203 itself: the
public key and the secret key that it writes are those of `kpke_keygen
mlkem768 d` in `common/fips203.ml`, for the seed `d` of 32 bytes. It has
the hypothesis that SampleNTT terminates for each entry of the matrix
(`mlkem_samplentt_terminates`), that is, that the output of SHAKE128 for it
eventually has 256 fields below q, which gives a k as in the specification
of `mlkem768_gen_matrix`. The lemmas relating the specifications of the
functions it calls (congruences modulo q and bounds on coefficients,
numbers for byte arrays and lists of words) to the definitions of FIPS 203
and to the forms of K-PKE in the NTT domain in `common/fips203_theory.ml`
are in `arm/proofs/utils/mlkem_native_fips203.ml`. It has no constant-time
and memory safety proof yet either.

`mlkem768_indcpa_enc` is the encryption of K-PKE for ML-KEM-768, and its
specification is in terms of FIPS 203 too: the ciphertext of 1088 bytes
that it writes is `kpke_encrypt mlkem768 ek msg r` for the encryption key
`ek` of 1184 bytes and the message `msg` and the randomness `r` of 32
bytes each. It has the same hypothesis on SampleNTT, for the matrix from
the last 32 bytes of `ek`, and the hypothesis that the stack does not
contain address 0, since it passes a buffer in its stack frame as the
fourth output of `mlkem768_poly_getnoise_eta1_4x`, which skips that output
if the pointer is null. The key is not checked, and the code computes with
its 12-bit fields as they are, which gives the result of FIPS 203 for any
key since FIPS 203 decodes them modulo q. The tactics for these functions,
which call many others on buffers in their stack frames, are in
`arm/proofs/utils/mlkem_native_indcpa.ml`. It has no constant-time and
memory safety proof yet either.

`mlkem768_indcpa_dec` is the decryption of K-PKE for ML-KEM-768: the
message of 32 bytes that it writes is `kpke_decrypt mlkem768 dk ct` for
the decryption key `dk` of 1152 bytes and the ciphertext `ct` of 1088
bytes, again for any key, since FIPS 203 decodes its 12-bit fields modulo
q. It has no constant-time and memory safety proof yet either.

The K-PKE functions for ML-KEM-512 and ML-KEM-1024
(`mlkem512_indcpa_keypair_derand`, `mlkem512_indcpa_enc`,
`mlkem512_indcpa_dec` and those with `mlkem1024`) have the same
specifications for `mlkem512` and `mlkem1024`. The hypothesis that the
stack does not contain address 0 is needed whenever a buffer in the stack
frame is the fourth output of `poly_getnoise_eta1_4x`: for ML-KEM-512 by
the key generation but not by the encryption, which uses
`mlkem512_poly_getnoise_eta1122_4x` and `mlkem512_poly_getnoise_eta2`, and
for ML-KEM-1024 by both. For ML-KEM-1024 the products of the rows of the
matrix and the vector are computed in a loop, which the proofs unroll.

`mlkem768_keypair_derand` is the key generation of ML-KEM-768 with the
randomness as an argument, and its specification is in terms of the
internal ML-KEM algorithms of FIPS 203: the keys that it writes are those
of `mlkem_keygen mlkem768 d z` for its 64 bytes of coins `d` and `z`. It
has the same hypothesis as `mlkem768_indcpa_keypair_derand`. The lemmas
and tactics for the ML-KEM functions are in
`arm/proofs/utils/mlkem_native_kem.ml`.

`mlkem768_enc_derand` is the encapsulation with the message as an
argument, including the input check of FIPS 203: if the encapsulation key
`ek` passes it (`mlkem_ek_check`), the function returns 0 and writes the
shared secret and the ciphertext of `mlkem_encaps_internal mlkem768 ek m`
for the message `m`, and otherwise it returns -4. It has the same
hypotheses as `mlkem768_indcpa_enc`.

`mlkem768_dec` is the decapsulation, including the input check of FIPS
203: if the decapsulation key `dk` and the ciphertext `c` pass it
(`mlkem_decaps_check`), the function returns 0 and writes the shared
secret of `mlkem_decaps_internal mlkem768 dk c`, including the implicit
rejection, and otherwise it returns -5. The comparison of the ciphertexts
and the selection of the shared secret are loops in constant time, which
are verified with invariants. It has the same hypotheses as
`mlkem768_indcpa_enc`, for the matrix from the seed in `dk`.

`mlkem768_keypair` and `mlkem768_enc` get their randomness with
`randombytes`, for which there is a contract like those of the C library
functions, which writes its buffer with no assumption about the values and
returns a status. Their specifications say that either `randombytes` fails
and they return -3, or they behave as `mlkem768_keypair_derand` and
`mlkem768_enc_derand` for some seeds or message of 32 bytes. For
`mlkem768_keypair` this needs the hypothesis that SampleNTT terminates for
the matrix from any seed. None of these functions has constant-time and
memory safety proofs yet.
