# Binary-level verification of snappy 1.3.1 (AArch64, gcc 12 -O2)

This directory holds the pinned build of [google/snappy][1] 1.3.1 whose
AArch64 machine code is verified here: the transcription of `libsnappy.so`
(`gcc12_O2/libsnappy.S`), and the documentation of the proofs, which are in
`arm/proofs/snappy` with the ISA-independent specification in
`common/snappy`.

[1]: https://github.com/google/snappy

## 1. Status

All the proofs are done, and the link of the build closes all of them: `make
snappy/gcc12_O2/link.correct` (in `arm/`) runs every proof file of
`arm/proofs/snappy/gcc12_O2` in one session and ends with

```
relative: 155 contracts stated, 155 proved and closed
```

and 95 theorems without assumptions, the `_CORRECT` and `_SAFE` theorems
(`SNAPPY_<F>_GCC12_O2_IMAGE_SUBROUTINE_{CORRECT,SAFE}`) of the functions in
section 3. On 16 OCaml 5 domains the link takes about 11 minutes.
No axiom is added: no `new_axiom`, `mk_thm` or `CHEAT_TAC` in any proof.

In short (section 5 has the exact statements and hypotheses):

- the C API (`snappy_compress`, `snappy_compress_with_level`,
  `snappy_uncompress`, `snappy_max_compressed_length`,
  `snappy_uncompressed_length`, `snappy_validate_compressed_buffer`) and the
  C++ functions under it are functionally correct (with termination) and
  memory safe;
- decompression and validation against a HOL model of the format, for any
  input bytes; compression byte for byte against a HOL model of the
  compressor, whose output is proved to decompress to the input and to fit
  in `MaxCompressedLength`;
- the compressor without a caller workspace through an abstract allocator
  (`operator new` / `operator delete` through the PLT), with no leak.

## 2. The fixed build

| Item | Value |
|---|---|
| Source | google/snappy tag `1.3.1`, `9c28114a38866f6deeaa826db918293bc28ae410` (the later #266 fix, f28c420, only matters for 32-bit `size_t`: the AArch64 `.text` built from the main tip is byte-identical) |
| Translation units | `snappy.cc`, `snappy-sinksource.cc`, `snappy-stubs-internal.cc`, `snappy-c.cc` (the CMake `snappy` library target) |
| Compiler | g++ (GCC) 12.4.0, official image `gcc@sha256:fa4be2f0a762fb14cc745289227d29aa32f0b55057c301d0d61a5eba46c85d99` (arm64) |
| Linker | GNU ld (GNU Binutils for Debian) 2.40, from the same image |
| Target | AArch64 Linux, default `-march` (armv8-a: no CRC32, so the hash is the multiplicative one), NEON on |
| Compile flags | `-std=c++11 -O2 -fPIC -fno-exceptions -fno-rtti -mbranch-protection=none -fno-stack-protector -g -gdwarf-4 -DNDEBUG -DHAVE_CONFIG_H -Wall -Wextra -Wno-sign-compare -frandom-seed=<tu> -ffile-prefix-map=/src=.` |
| Link flags | `-shared -Wl,-Bsymbolic -Wl,-z,now -Wl,-z,relro -Wl,-soname,libsnappy.so -Wl,--build-id=none` |
| Configuration | `config.h` here (CMake's result on AArch64 Linux with no optional libs); `snappy-stubs-public.h` generated as CMake does (version 1.3.1, `HAVE_SYS_UIO_H` = 1) |
| Artifact | `libsnappy.so`, sha256 `40fdb95ecc036b431be3e62869fa2b4f9f8504c5fc1c69cc3b65374a3a849c86` (see `gcc12_O2/SHA256SUMS`) |

`build.sh <snappy-checkout> <out-dir>` reproduces it with no network inside
the container; two runs give identical hashes for the `.so` and all `.o`
files. The flags follow upstream's CMake (`-std=c++11`, `-fno-exceptions`,
`-fno-rtti`, `-DNDEBUG` of a release build) plus what the proofs need:

- `-mbranch-protection=none`: the AL2023 system gcc emits PACIASP/AUTIASP,
  which the AArch64 model does not have; gcc 12.4 does not by default, so
  this only makes it explicit.
- `-fno-stack-protector`: snappy has no use for it and it removes the guard
  hypotheses of the mlkem-native proofs. (Dropping this flag is cheap to
  revisit: the precedent already handles the guard.)
- non-split DWARF and `-frandom-seed`: `-gsplit-dwarf` made the `.o` files
  differ between runs (random `dwo_id`); the code was identical.
- `-Bsymbolic`: calls within the library are direct, so only the imports go
  through the PLT.
- `-z now -z relro`: the loader resolves every GOT/PLT slot before the
  library runs and then makes the relocated data read-only, so "the slot
  holds the imported function's address" is true from the start (with lazy
  binding it would first hold the resolver's address), and nothing can
  write the vtables or the GOT.

The binary: 37188 bytes of text, 109 functions, no jump tables (every `br`
outside the PLT is in the CRT stubs or is a tail call through a function
pointer). gcc 12 -O2 matches the main build of the precedent; a clang build
can be added later as a second `<build>` directory.

## 3. What is verified

Common hypotheses: the image is loaded at a 4096-aligned `pc` with its
relocations applied, the stack pointer is aligned as the function needs,
the stack frame and the outputs are disjoint from each other, from the
inputs, from the image and from the regions of the external contracts, and
the external functions meet their contracts (section 5). The properties are
**functional correctness** (`_CORRECT`, an `ensures`, so also termination)
and **memory safety** (`_SAFE`: correctness together with every memory
access inside the regions listed and every write inside the outputs; no
constant-time claim, since snappy's control flow depends on the data by
design).

The specifications (`common/snappy/`):

- `snappy_format.ml`: the format of `format_description.txt` as this
  implementation accepts it, `snappy_header : byte list -> num option` (the
  varint, at most 5 bytes and below 2^32) and `snappy_decode : byte list ->
  byte list option` (literals, copies with 1-, 2- and 4-byte offsets; a copy
  needs 1 <= offset <= bytes produced; the output must have exactly the
  header length; the input must be consumed exactly);
- `snappy_compress.ml`: `snappy_compress level input`, the model of
  `CompressFragment` (level 1) and `CompressFragmentDoubleHash` (level 2)
  and of the block loop of `InternalCompress`;
- `snappy_roundtrip.ml`: for inputs shorter than 2^32 and level 1 or 2,
  `snappy_decode (snappy_compress level x) = SOME x` and `LENGTH
  (snappy_compress level x) <= snappy_max_compressed_length (LENGTH x)`.

The functions with theorems (layout names of
`arm/proofs/snappy/gcc12_O2/layout.ml`; `c_` for the C API):

| Group | Functions | Property |
|---|---|---|
| C API | `snappy_compress`, `snappy_compress_with_level` (also the BUFFER_TOO_SMALL and INVALID_LEVEL results), `snappy_uncompress`, `snappy_max_compressed_length`, `snappy_uncompressed_length`, `snappy_validate_compressed_buffer` | as the C++ functions below; the status codes as documented in `snappy-c.h` |
| Lengths | `MaxCompressedLength`, `GetUncompressedLength(const char*, size_t, size_t*)` | `32 + n + n DIV 6`; true iff `snappy_header in = SOME m`, then `*result = m` |
| Decompression | `RawUncompress(const char*, size_t, char*)`, `RawUncompress(Source*, char*)`, `DecompressAllTags<SnappyArrayWriter>`, `DecompressBranchless<char*>`, `IncrementalCopy`, `MemCopy64` | for any input: true iff `snappy_decode in = SOME x`, and then the output holds `x`; writes only the `m` bytes of the header length |
| Validation | `IsValidCompressedBuffer`, `InternalUncompress<SnappyDecompressionValidator>`, `DecompressAllTags<SnappyDecompressionValidator>`, `DecompressBranchless<size_t>`, `RefillTag` (empty and window cases) | true iff `snappy_decode in <> NONE`; writes no memory but its stack and the decompressor object |
| Compression with a workspace | `RawCompress(..., CompressionOptions, CompressionContext*)`, `Compress(Source*, Sink*, CompressionOptions, CompressionContext*)`, `InternalCompress`, `CompressFragment`, `CompressFragmentDoubleHash`, `WorkingMemory(size_t, char*)`, `WorkingMemory::GetHashTable`, the `CompressionContext` methods (constructors, move, assignment, `Reset`, `WorkspaceSize`, destructor) | the output is `snappy_compress level input` (levels 1 and 2), of length at most `MaxCompressedLength n`; writes only the output and the workspace |
| Compression with the heap | `RawCompress(const char*, size_t, char*, size_t*)`, `RawCompress(..., CompressionOptions)`, `Compress(Source*, Sink*, CompressionOptions)`, `WorkingMemory(size_t)`, `~WorkingMemory` | the same, with one block allocated and freed: the abstract heap is the same afterwards |
| Objects | `ByteArraySource::Available`, `Peek`, `Skip` | as in `snappy-sinksource.cc` |

The `Source*`/`Sink*` functions are proved for snappy's own
`ByteArraySource` and `UncheckedByteArraySink` (as the `char*` entry points
use them), not for user-supplied objects.

Decisions: gcc 12.4.0 -O2 and the flags of section 2 (D1); snappy 1.3.1
(D2); `operator new` is assumed to return (D3: a hypothesis of the theorems
with the heap); the round trip and the length bound are the top-level
properties of compression, with the HOL model of the compressor as the
intermediate specification (D4).

Out of scope: the `std::string` entry points, user `Source`/`Sink` objects,
`RawCompressFromIOVec`, `RawUncompressToIOVec`, the test, benchmark and
fuzzer translation units, the framing format (not in the library).

## 4. Running the proofs

Requirements: HOL Light built for OCaml 5 with `HOLLIGHT_USE_MODULE=1` and
a kernel that is safe on several domains (jrh13/hol-light PR 214; see the
header of `common/par_domains.ml`), and the usual s2n-bignum toolchain. In
`arm/`, with `HOLDIR` the HOL Light directory:

```
# the whole build: every proof file as a job, the theorems closed
S2N_PAR_DOMAINS=16 make HOLDIR=$HOLDIR HOL_PAR=1 snappy/gcc12_O2/link.correct

# one proof file (relative to the contracts of its callees)
make HOLDIR=$HOLDIR HOL_PAR=1 snappy/gcc12_O2/<name>_proof.correct
```

`make clean` is needed when changing `HOL_PAR` or `HOLDIR`. A proof file
alone takes a few minutes, about 90 s of it loading the libraries. The link
runs its jobs costliest first, by `link_costs.tsv`.

After adding or removing a file of `arm/proofs/snappy/gcc12_O2`, regenerate
the make rules and the link file, and after a link the costs:

```
python3 ../tools/native_proofs_mk.py snappy gcc12_O2 > snappy/gcc12_O2/proofs.mk
python3 ../tools/native_link.py snappy gcc12_O2 > proofs/snappy/gcc12_O2/link.ml
python3 ../tools/link_costs.py snappy gcc12_O2 snappy/gcc12_O2/link.correct
```

The transcription and the generated image files come from the binary of
section 2 with the generic tools of `tools/`:

```
SO=<snappy-build>/gcc12_O2/libsnappy.so
python3 ../tools/elf_transcribe.py --title "snappy 1.3.1, gcc 12 -O2" \
  --source "libsnappy.so of snappy 1.3.1 built by arm/snappy/build.sh (see arm/snappy/README.md)" \
  --copyright "Copyright 2005-2011 Google Inc. All Rights Reserved." \
  --copyright "Copyright 2011 Martin Gieseking <martin.gieseking@uos.de>." \
  --license "BSD-3-Clause AND (Apache-2.0 OR ISC OR MIT-0)" \
  $SO snappy_libsnappy_gcc12_O2 $PWD/../include > snappy/gcc12_O2/libsnappy.S
python3 ../tools/elf_layout.py --lib libsnappy --name "gcc 12 -O2" \
  --project "snappy 1.3.1 (see arm/snappy/README.md)" \
  --strip-namespace snappy::internal --strip-namespace snappy --c-prefix c_ \
  $SO > proofs/snappy/gcc12_O2/layout.ml
python3 ../tools/elf_relocs.py --title "snappy 1.3.1, gcc 12 -O2, see arm/snappy/README.md" \
  $SO snappy_libsnappy_gcc12_O2 > proofs/snappy/gcc12_O2/relocs.ml
python3 ../tools/native_proofs_mk.py snappy gcc12_O2 > snappy/gcc12_O2/proofs.mk
python3 ../tools/native_link.py snappy gcc12_O2 > proofs/snappy/gcc12_O2/link.ml
```

and checked with

```
make snappy/gcc12_O2/libsnappy.o
python3 ../tools/elf_check_transcription.py snappy/gcc12_O2/libsnappy.o - $SO 0x0
make HOLDIR=... snappy/gcc12_O2/image_decodes.correct snappy/gcc12_O2/link.correct
```

and are checked with `python3 ../tools/elf_check_transcription.py
snappy/gcc12_O2/libsnappy.o - $SO 0x0` (by hand: the binary is not in the
repository) and `make snappy/gcc12_O2/image_decodes.correct` (every word of
the code decodes).

### Files

- `arm/snappy/`: `build.sh` and `config.h` (section 2), `gcc12_O2/`
  (`libsnappy.S`, `SHA256SUMS`, `compiler.txt`, the generated `proofs.mk`),
  this file, `DESIGN.md`, `REFLECTIONS.md` and `doc/`.
- `common/snappy/`: the specification (format, compressor model, round
  trip), the lemmas that the machine-code proofs share (decompressor state,
  slow path, validator, memory of byte lists, words), the evaluation tests
  of the models, `difftest/` (the differential tests against the library)
  and `FINDINGS.md` (the edge cases found).
- `arm/proofs/snappy/gcc12_O2/`: per function `<f>_spec.ml` (the contract)
  and `<f>_proof.ml` (its proof relative to the contracts of the callees;
  see `common/relative.ml`), the pieces of the long proofs as spec/proof
  pairs of their own (`compress_fragment_seg*`,
  `compress_fragment_double_hash_<piece>`, `decompress_branchless_near*`,
  `..._array_writer_t_{b,s}_<class>`, `..._validator_t_{b,s}_<class>`), the
  libraries of those proofs (`*_lib.ml`), the lemmas proved in jobs of their
  own (`*_lemmas_proof.ml`), the generated `layout.ml`, `relocs.ml`,
  `libsnappy.ml`, `link.ml` and `link_costs.tsv`, and `image_decodes.ml`.
- `arm/proofs/snappy/`: tools independent of the build: `relative.ml`, the
  objects of the image (`objects.ml`, `decompressor_objects.ml`), memory
  events (`events.ml`, `events_inset.ml`), branches decided by arithmetic
  (`bstep_decide.ml`), the array writer and validator paths
  (`array_writer.ml`, `validator_tactics.ml`, `validator_segment_tools.ml`,
  `dat_validator_lib.ml`).
- Generic files used by the proofs: `common/elf_image.ml` (loaded images),
  `common/libc_contracts.ml` and `arm/proofs/libc.ml` (C library
  contracts), `arm/proofs/heap.ml` and `arm/proofs/heap_plt.ml` (the
  abstract heap and calls through the PLT), `common/bstep.ml` and
  `arm/proofs/bstep.ml` (symbolic execution), `common/ensures_measure.ml`
  (cut points with a measure), `common/par.ml` and `common/par_domains.ml`
  (the parallel link).

## 5. What the theorems say, and what they assume

The final theorems are the `SNAPPY_<F>_GCC12_O2_IMAGE_SUBROUTINE_{CORRECT,SAFE}`
theorems printed by `arm/proofs/snappy/gcc12_O2/link.ml`
(`make snappy/gcc12_O2/link.correct`). `_CORRECT` is functional correctness
(an `ensures`, so it includes termination); `_SAFE` adds that every memory
access event lies in the listed regions and every write in the listed outputs
(`memaccess_inbounds`, or `memaccess_inset` where the heap footprint is a set).

### Specifications

- **Decompression** is specified by `snappy_decode : byte list -> byte list
  option` (`common/snappy/snappy_format.ml`), the format of
  `format_description.txt` exactly as snappy 1.3.1 accepts it: varint header
  (at most 5 bytes, below 2^32), literals, copies with 1-, 2- and 4-byte
  offsets (1 <= offset <= bytes produced), output length exactly the header,
  input fully consumed. `snappy_uncompress`, `RawUncompress`,
  `IsValidCompressedBuffer`, `snappy_validate_compressed_buffer`,
  `GetUncompressedLength` and `snappy_uncompressed_length` are proved against
  it for **any** input bytes.
- **Compression** is specified by a HOL model of the compiled algorithm,
  `snappy_compress level input` (`common/snappy/snappy_compress.ml`); the
  machine code is proved to produce exactly its bytes. Independently of how
  faithful the model is, `common/snappy/snappy_roundtrip.ml` proves for every
  input of length < 2^32 and level 1 or 2:
  `snappy_decode (snappy_compress level x) = SOME x` and
  `LENGTH (snappy_compress level x) <= snappy_max_compressed_length (LENGTH x)`.
- Both models were checked by evaluation against vectors produced by the real
  library and differentially against `libsnappy.so` (about 60k decoder
  streams, about 3300 compressor inputs at both levels and the test data);
  `common/snappy/FINDINGS.md` lists the edge cases found (none is a
  functional bug).

### Trusted base

- HOL Light's kernel (with `check_axioms` run by every proof build; no
  `mk_thm`, `new_axiom` or `CHEAT_TAC` in any proof) and OCaml. The parallel
  link runs proof jobs on several OCaml 5 domains (HOL Light PR 214); it is
  sound only if that kernel is domain-safe (see `common/par_domains.ml`).
- The AArch64 model of s2n-bignum (`arm/proofs/{arm,instruction,decode}.ml`),
  including the instructions added for this work (RBIT, PRFM/PRFUM as
  no-ops without a memory event, BLR, LDUR/STUR of B/H registers), which are
  tested by cosimulation on hardware, not proved. A consequence of modelling
  prefetches without an event: memory-safety theorems say nothing about
  prefetch addresses (snappy prefetches past its buffers).
- That `arm/snappy/gcc12_O2/libsnappy.S` is the code of the built
  `libsnappy.so` (checked byte for byte by `tools/elf_check_transcription.py`,
  run by hand), and that the `.so` was built as in section 2 (reproducible
  with `build.sh`).
- The dynamic loader: the image is mapped at a base `pc` with the relocations
  of `relocs.ml` applied (`-z now`: GOT/PLT resolved before any code runs;
  `-z relro`: the relocated data is read-only afterwards).

### Hypotheses of the theorems

- The image is loaded at a 4096-aligned `pc` with `pc + libsnappy_size <=
  2^64`, and its relocated data is as `elf_relocated_data` states (imports
  resolved to `imp "memcpy"`, `imp "_Znwm"`, ...). The writable segment is
  not written by the code (disjointness hypotheses).
- **C library:** `memcpy`, `memmove` and `memset` meet their contracts
  (`arm/proofs/libc.ml`): they do their job, return to X30, change only
  ABI-volatile registers and their output, use no stack and read only their
  arguments and their own code/data region (ea,el), which callers do not
  write. The `_SAFE` theorems use the memory-safety-only forms.
- **Heap** (compression without a caller workspace): `operator new` and
  `operator delete` meet `heap_model heap_ok heap_fp heap_room stk`
  (`arm/proofs/heap.ml`, DESIGN §3): an abstract invariant over the
  allocator's own memory, fresh disjoint blocks, a stack use of at most
  `stk <= 1024` bytes, and `heap_room H n` for the one allocation of
  `snappy_working_memory_size n` bytes (decision D3 of section 3: `new` returns; the
  `bad_alloc` path is excluded by this hypothesis). The model is shown
  non-vacuous by a slab allocator proved to meet it (`arm/heap`). The
  theorems also assume single-threaded use of the allocator during the call.
  Results include `heap_ok H` with the same `H` afterwards (no leak).
- **Buffers and stack** are disjoint from each other, from the image, from the
  heap footprint and from (ea,el) as stated, and do not reach the top of the
  address space (e.g. `val out + m + 64 <= 2^64`; the stack pointer at least
  the frame size). Several functions compare pointers unsigned and would
  misbehave on wrap-around (FINDINGS F10 and DESIGN §7b/§7e).
- **Sizes:** compression input length < 2^32; decompression input length <
  2^63; validator input length < 2^58 (FINDINGS F2). Compression level 1 or 2
  for the C++ entry points (other levels are undefined behaviour there,
  FINDINGS F8; the C entry point checks the level and its INVALID_LEVEL and
  BUFFER_TOO_SMALL results are proved too).
- Function-specific alignment conditions where the code needs them (e.g. a
  16-aligned stack pointer, an 8-aligned decompressor object), as stated in
  each theorem.

### Not covered

- The `Source`/`Sink` C++ entry points with user-supplied objects (tier T4)
  and the `std::string` entry points (tier T3), `RawCompressFromIOVec` and
  `RawUncompressToIOVec`.
- Constant time (snappy is not constant time by design).
- The `_SAFE` forms of the BUFFER_TOO_SMALL / INVALID_LEVEL results of the C
  compression entry points (their `_CORRECT` forms are proved).

## 6. External interfaces: what is generic, what is snappy's

The imports of `libsnappy.so` (`nm -D --undefined-only`) are `memcpy`,
`memmove`, `memset`; `operator new`, `operator new[]`, `operator delete`,
`operator delete[]`; `std::string::resize` and `std::string::_M_append`
(libstdc++, cxx11 ABI); `std::__throw_length_error`, `__throw_bad_alloc`,
`__throw_out_of_range_fmt`; and `__cxa_finalize`, `__gmon_start__` and
`_ITM_*`, which only the CRT constructors and destructors use (no entry
point reaches them). Calls also leave the code through pointers: the
virtual methods of `Source` and `Sink`, and the `deleter` callback of
`AppendAndTakeOwnership` (on the `Sink` paths, not covered).

The general method is in `doc/external_interfaces.md` of the repository. For snappy we made these choices:

| What `libsnappy.so` depends on | How it is handled | Generic or snappy-specific |
|---|---|---|
| The loader: 49 filled-in slots (vtables, GOT) | Generated slot list `relocs.ml`; we link with `-z now -z relro` so it holds from the start | Method and tools generic; the slot list and the link flags are snappy's |
| `memcpy`, `memmove`, `memset` | Fixed contracts, called through the PLT | Generic |
| `operator new` / `operator delete` | The abstract heap; snappy allocates one working-memory block per call and frees it, so its theorems keep `H` unchanged (no leak) | Heap model generic; the block size `snappy_working_memory_size` and the no-leak statements are snappy's |
| Allocation failure (`std::__throw_bad_alloc`) | Excluded by the `heap_room` hypothesis (decision D3), and the size-check path proved unreachable | Snappy-specific decision |
| `std::__throw_length_error`, `__throw_out_of_range_fmt` | Not reached on the proved paths | Snappy-specific |
| Virtual calls on `Source` / `Sink` | Only snappy's own `ByteArraySource` and `UncheckedByteArraySink` occur on the proved paths; their methods are in the binary and proved like any other function | Mechanism generic; the objects are snappy's (`arm/proofs/snappy/objects.ml`, `decompressor_objects.ml`) |
| User-supplied `Source` / `Sink`, `std::string` (`resize`, `_M_append`) | Not handled; those entry points are out of scope (section 5) | — |

## 7. How it was built

`DESIGN.md` records the designs of the proofs (loaded images, contracts,
the heap, the specification, the cut points and invariants of the long
proofs) and the pitfalls met; `REFLECTIONS.md` what went well and badly
and what to carry to the next library; `doc/` the notes kept while the
proofs were developed, and the measurements of the two rounds of
performance work that brought the link from about 70 minutes to 11.
