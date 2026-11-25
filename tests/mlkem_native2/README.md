# Tests and benchmarks of the ML-KEM API in assembly

This directory has the tests and benchmarks used to develop the functions
in `arm/mlkem_native/asm` and the new leaves in `arm/mlkem`. They compare the
functions with mlkem-native's portable C, which serves as the reference,
and are separate from s2n-bignum's own tests and from the build: nothing
here is built by the Makefiles.

They run on an AArch64 Linux machine with the SHA3 extension, and need
git, gcc (or another C compiler as `CC`), python3 and, to build valgrind,
curl and the usual tools for building C programs. Everything downloaded
or built goes under `work/` here (or `WORK`; see `env.sh` for this and
the other settings).

They also run on x86_64 Linux, for `x86/mlkem_native/asm` and the new
leaves in `x86/mlkem`: the scripts choose the settings for the machine
they run on (`ARCH` in `env.sh`). There the system's valgrind (3.22 or
later) runs the AVX2 code; the ABI check uses `abi_stub_x86.S` and also
checks the Microsoft x64 entries (the API built with `WINDOWS_ABI`, which
`build.sh` renames with the prefix `ms_`); and since IBT cannot be
enforced without CET, `check_endbr.sh` checks instead that every global
function starts with endbr64. `check_noseg.sh` checks that no
instruction of the assembly uses fs or gs, as the stack protector of
compiled C does (the x86 model has no segmentation).

## Setup

    ./setup.sh

fetches mlkem-native at the commit the tests are pinned to (9b96caa1),
fetches the ACVP (v1.1.0.43) and Wycheproof vectors with mlkem-native's
own clients, and builds the reference library: mlkem-native's portable C
for all three parameter sets with the namespace prefix `ref`.

The steps under valgrind need one that can run the SHA3 instructions
BCAX, RAX1 and XAR, which valgrind 3.28.0 cannot (of the four, it only
decodes EOR3). With `VALGRIND_PATCH` set to a patch for 3.28.0 that adds
them (not included here), `setup.sh` also builds that valgrind into
`work/valgrind`, where the scripts find it; `VALGRIND` selects another.
Without one, those steps are skipped.

## Running the tests

    ./build.sh && CTFLAGS=-DMLKEM_CT_TESTING ./build.sh
    CTLIBS="$(ls work/obj_ct/*.o)" ./gate.sh asm work/obj/*.o
    ./leafmid.sh

`build.sh` builds the objects with the rules of `arm/Makefile` into
`work/obj`, and with `CTFLAGS` into `work/obj_ct`, where the per-level
files are preprocessed with `MLKEM_CT_TESTING` defined, which marks rho
public after key generation derives it. Both add `randomized.c`, the
randomized `mlkemL_keypair` and `mlkemL_enc` in C on top of the
deterministic functions.

`gate.sh NAME LIB...` is the gate for any library with the API (about 10
seconds here; results in `work/build/NAME`):

 - test_api: differential tests of keypair_derand, enc_derand, dec,
   check_pk and check_sk (and of the randomized keypair and enc if
   present) against the reference, by default 8 shards of 2000
   iterations per level, with random inputs and the rare paths: implicit
   rejection, invalid public keys (a coefficient >= q), invalid secret
   keys (a wrong H(pk) or embedded pk), secret vectors with coefficients
   >= q (which dec must accept), and all-0 and all-0xff seeds. Outputs
   sit between guard bytes, and inputs must be unchanged. It also counts
   the matrix polynomials that needed a fourth SHAKE128 block (about
   0.8%).
 - KAT: the SHA-256 of mlkem-native's KAT output, against its META.yml.
 - ACVP and Wycheproof, with mlkem-native's clients and drivers.
 - memcheck: test_api with heap buffers of the exact sizes.
 - constant time: test_ct under memcheck with the secrets undefined, using
   the libraries in `CTLIBS` (the build with `MLKEM_CT_TESTING`).
 - ABI: test_abi calls each function through abi_stub.S with random
   x8-x29 (x18 too) and q0-q31 and its own stack; x19-x29, d8-d15, sp and
   x18 must survive, and no 16-byte window of a secret (the coins, the
   seeds derived from them, the secret vector, the shared secret, z) may
   be left on the stack. It reports the stack depth and the bytes left
   there (`work/build/NAME/abi.log`). On x86_64 the stub (abi_stub_x86.S)
   randomizes all the registers but rsp; rbx, rbp, r12-r15 and rsp must
   survive, and for the Microsoft x64 entries also rdi, rsi and the low
   halves of xmm6-xmm15.
 - BTI: test_api and test_abi again, linked so that the kernel enforces
   BTI (`bti_start.S` explains how), which checks that every function
   reached by an indirect call has a landing pad. On x86_64 instead:
   every global function must start with endbr64 (`check_endbr.sh`).

On x86_64, `VARIANT=avx512 ./build.sh` builds the AVX-512 version
(`x86/mlkem_native/asm_avx512`) into `work/obj_avx512` instead, with the
suffix `_avx512` removed from the names of its API and middle layer, so
that all the scripts here run on it unchanged. valgrind does not run its
EVEX code, so give it `VALGRIND=` (and `CTLIBS=none` for gate.sh).

`leafmid.sh [OBJDIR]` tests the new leaves (test_leaf: each against the
reference, exhaustively over the values of each coefficient or byte
where the input space allows) and the middle layer (test_mid:
mlkem_gen_matrix with its hash jobs and noise, mlkem_getnoise,
mlkem_hash_h and mlkem_hash_g, when the build has it), natively, under
memcheck and with BTI enforced (on x86_64, the endbr64 check, and the
check that no instruction uses fs or gs). On x86_64 the compress and
decompress kernels are mlkem-native's, which take their tables from the
constants block (`mlkem_compress_d4_x86` and so on), and
`mlkem_frombytes` and `mlkem_tobytes` include the permutation into the
custom NTT order of the x86 backend, so test_leaf checks them against
the reference composed with `mlkem_unpack`, itself checked to be a fixed
reordering. The rejection sampler also runs with its buffer and output
next to pages without access, which catches reads and writes out of
bounds, and the Keccak-f1600 permutations on one state that are linked
(on x86_64 also `sha3_keccak_f1600_alt2`, which the build adds although
mlkem_native2 does not use it) are checked against the reference
permutation.

`mutants.sh` checks the tests themselves, with a library that forwards
to the reference with one deliberate fault at a time (`mutants.c`): each
fault must be caught and the harmless changes must pass.

## Benchmarks

    ./baseline.sh clang-18
    ./bench.sh asm work/obj/*.o

`baseline.sh` builds mlkem-native's multilevel library with its native
backends, as its `examples/multilevel_build_native` does, and measures
it; `bench.sh` measures a library and compares it with that baseline.
The cycle counts come from a fixed-rate counter and a measured clock
(there may be no access to the performance counters), as medians of 31
runs of 200 calls; `CORE` pins the run to a core. On AArch64 the counter
is the virtual counter and the clock is measured once. On x86_64 it is
the TSC, and the clock is measured right after each run, since it
varies with the turbo and the AVX frequency licences (on a Cascade Lake
Xeon, for example, 3.1 GHz for scalar code, 2.7 GHz while 256-bit
multiplications run): each line also gives the time per call in ns and
the clock of the run.

`perf_kit.sh` makes the comparison on any machine, with more builds of
mlkem-native, and needs nothing but itself (see its header):

    curl -O https://raw.githubusercontent.com/awslabs/s2n-bignum/native-unify/tests/mlkem_native2/perf_kit.sh
    bash perf_kit.sh ~/mlkem-perf

It fetches s2n-bignum (the branch native-unify, or uses the checkout
`S2N_DIR`) and mlkem-native, and builds the assembly (on x86_64 with
AVX-512 also its AVX-512 version) and mlkem-native at the pinned commit
and at main, with gcc and with clang, as its multilevel and its
monolithic build, with the flags of its examples and with
`-march=native`, and on x86_64 with AVX-512 with and without AVX-512.
It measures all of them in turn with `bench_api.c`, in 11 rounds, and
reports for each function the fastest mlkem-native build on the machine
and the speedup over it: the AVX2 assembly against the builds without
AVX-512, the AVX-512 one against all of them.
