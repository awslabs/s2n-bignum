# Findings from specifying snappy 1.3.1

Results of reading `snappy.cc` (tag 1.3.1) to fix the acceptance
conditions of `snappy_decode` in `snappy_format.ml`. For the flat-buffer
entry points (`RawUncompress`, `IsValidCompressedBuffer`,
`RawUncompressToIOVec`, and so the C API) there is **no disagreement**
between the fast path (`DecompressBranchless`) and the slow path, nor
between the array writer and the validator. The points below are
behaviours the machine-code proofs must take into account; none of them
changes the set of accepted streams.

## Validation of the model

A Python transcription of the HOL definitions (`difftest/snappy_model.py`,
run by `difftest/difftest.py`) was compared with the actual `libsnappy.so` (the `gcc12_O2` build, run natively on an AArch64 host via
`ctypes`) on `snappy_uncompress`, `snappy_validate_compressed_buffer` and
`snappy_uncompressed_length`:

- 362 valid streams (snappy's own output at levels 1 and 2 for slices of
  the test data of 0..70000 bytes, so the fast path runs);
- 20000 mutations of them (byte changed, truncated, junk appended, header
  changed, random bytes);
- 40000 random tag sequences (up to 200 tags, literals of 1..300 bytes
  with all long-literal length widths, all copy kinds, offsets biased to
  0, the exact output length and one more, headers equal to or off by one
  from the output length).

Acceptance and output agreed in every case. The HOL definitions themselves
are checked by evaluation (`Compute.CBV_CONV`) against 260 vectors produced
by the library, including hand-made edge cases (`snappy_format_tests.ml`).

## F1. Validator fast path: off-by-one in the offset bound (harmless)

`SnappyDecompressionValidator::GetBase` returns `1`, so `DecompressBranchless`
runs for the validator with `op_base = 1` and relative position
`op = produced - 1`; its guard `delta = op - offset < 0` thus rejects
`offset == produced`, which is a valid copy, accepted by the slow path
(`AppendFromSelf`: `produced <= offset - 1u` fails). A fast-path rejection
only falls back to the slow path (`goto break_loop`), so the result is the
same; only the path differs. Concrete input (header 244; a 60-byte
literal; a copy-2 of length 64 with offset 60 = bytes produced so far; two
more 60-byte literals, so that more than 130 input bytes remain when the
copy is reached):

```
f401 ec <41..5a 41..5a 41..48> fe3c00 ec <same 60 bytes> ec <same 60 bytes>
```

(the literal is `ABC...ZABC...ZABCDEFGH`). The library accepts it (both
`snappy_validate_compressed_buffer` and `snappy_uncompress` return OK), as
does the spec.

## F2. Validator fast path: output not bounded by the header (harmless)

For the validator `op_limit_min_slop` is `PTRDIFF_MAX - kSlopBytes + 1`, so
`DecompressBranchless` keeps decoding beyond the declared length `m`. As
`produced` only grows, every later `Append`/`AppendFromSelf` and the final
`CheckLength` then fail: still "invalid". This relies on `produced` (a
`size_t`) not wrapping. In the fast path each input byte adds at most
64/3 < 22 bytes of output, so `produced < 22 * n`, which is below 2^63 for
any input of fewer than 2^58 bytes (any buffer in a 48-bit address space).
**Hypothesis needed by the machine proof of the validator: compressed
length < 2^58** (or any bound making `22 * n < 2^63`).

## F3. The literal length 2^32 is rejected only implicitly (as intended)

The tag `0xFC` with length bytes `FF FF FF FF` gives literal length
`0xFFFFFFFF + 1 = 2^32` as a `size_t` (the source acknowledges this and
does not check it). Both writers reject it because `m < 2^32` (array
writer: `space_left < len`; validator: `produced + len > expected`). The
spec computes the length as a number and needs no special case (the
condition "output + len <= m" fails). Example: `05 FC FF FF FF FF 68 65 6C
6C 6F` is invalid (tested).

## F4. Output written on failure

When `RawUncompress` (and `snappy_uncompress`) fails, the output buffer may
have been written: tags before the failing one in full, plus slop bytes
of the fast path, plus a literal that runs past the end of the input is
first appended as far as the input goes (`Append(ip, avail)` in the
literal loop) before decoding stops. All writes are within `[out, out+m)`.
The spec says nothing about the output on failure; the memory-safety
theorem must allow writes to all of `[out, out+m)`. `snappy_uncompress`
writes `*uncompressed_length` only when it returns `SNAPPY_OK`.

## F5. Headers: the two parsers agree

`Varint::Parse32WithLimit` (used by `GetUncompressedLength(const char*,..)`,
`snappy_uncompressed_length` and the first check of `snappy_uncompress`) and
`SnappyDecompressor::ReadUncompressedLength` (used by `RawUncompress` /
`IsValidCompressedBuffer`, which parse the header again) accept the same
byte strings with the same value: at most 5 bytes, bytes 1-4 continue iff
bit 7 is set, the 5th byte must be `< 16` (`ReadUncompressedLength`:
`LeftShiftOverflows(val, 28)` rejects `val >= 16`, and a 5th byte with bit 7
set fails at `shift >= 32`), and non-canonical encodings are accepted
(e.g. `80 00` is the header 0). `snappy_varint` models this; `snappy_header`
is its value.

## F6. No trailing bytes; truncation

Every tag appends at least one byte and must not take the output past `m`,
so once the output has `m` bytes the stream must end
(`SNAPPY_DECODE_TAGS_FULL`): "trailing bytes" are tags and fail. A tag whose
bytes are not all present (tag, offset or length bytes, literal data)
fails: `RefillTag` returns false without setting `eof_`, or the literal
loop's `Peek` returns 0 without setting `eof_`; success requires `eof_`,
i.e. the input ends exactly at a tag boundary.

## F7. Scatter/gather output (`RawUncompressToIOVec`)

`SnappyIOVecWriter` has no fast path (`GetBase` returns `nullptr`); its
`Append`/`AppendFromSelf` checks (`offset - 1u >= total_written_`,
`len > output_limit_ - total_written_`) are those of the validator, and it
additionally fails when it needs more space than the iovecs have left,
which happens iff the header length exceeds the iovecs' total length. So
it returns true iff `snappy_decode l = SOME x` and `LENGTH x` is at most the
total iovec length (`snappy_iovec_ok`). This was established by reading the
code; the iovec path was not tested against the library.

## Compressor

The models of `CompressFragment` and `CompressFragmentDoubleHash`
(`snappy_compress.ml`) were written first in Python, phase by phase as
in HOL, and compared byte for byte with `snappy_compress_with_level` of
`libsnappy.so` at levels 1 and 2 on 3000 inputs (slices of the test data,
random bytes, low-entropy text over 1-4 letters, runs of `a`/`ab`/`abc`/`\0`
of up to 70000 bytes, prefixes of the test files; 0 to 140000 bytes, so
across fragment boundaries) and on all 14 test data files: all equal. The
first version of the level-2 hashes was wrong (`TableEntry4ByteMatch` and
`TableEntry8ByteMatch` take bits 18.. and 50.. after `& mask` and `/ 2`, not
17.. and 49..); the comparison caught it. The HOL definitions agree with
the library on 48 short vectors by evaluation (`snappy_compress_tests.ml`).

## F8. Compression levels other than 1 and 2 are undefined behaviour (C++ API)

`snappy::CompressionOptions{level}` does not clamp `level`, and
`InternalCompress` only `assert`s `level == 1 || level == 2`. With `NDEBUG`
any other level leaves `end = nullptr`, and `writer->Append(dest, end - dest)`
then gets a huge length. `snappy_compress_with_level` (C API) rejects such
levels before compressing. **Hypothesis of the machine proofs of
`RawCompress(.., CompressionOptions, ..)`: level 1 or 2**; the model
(`snappy_compress_fragment`) treats every level other than 1 as 2, and the
top-level lemmas assume `level = 1 \/ level = 2`.

## F9. Facts the compressor proofs need that hold but are not checked in release builds

- After `FindMatchLength(candidate + 4, ip + 4, ip_end, &data)` the low 5
  bytes of `data` are the input bytes at the new `ip` whenever the code
  uses them (`assert`ed only in debug builds). In all three return paths
  `*data` is loaded at or after the end of the match (`a2 >> (shift & 24)`
  with `a2` from `s2` or `s2 + 4`; `Load64(s2)` in the byte loop). When it
  is not written (the byte loop with `s2 > s2_limit - 8`, or the end of
  the input reached) the new `ip` is `>= ip_limit` and `data` is not used.
  The model reads the input bytes directly, so the machine proof of
  `CompressFragment` has to prove this property of `FindMatchLength`.
- All positions stored in the `uint16_t` tables are below 65536, since a
  fragment has at most 65536 bytes and the stored positions are at most
  `n - 13`. So there is no truncation and the model's tables of numbers
  are exact.
- The `skip` counters (`uint32_t`) do not wrap. Level 1: `skip - 32` is the
  total advance of the search, at most 65536. Level 2: `skip` grows by 1
  per probe, at most 65536 times.
- The literal and copy encodings rely on the output's 32 bytes of slack
  (`MaxCompressedLength`) for their over-long stores (`UnalignedCopy128`,
  `Store32`). Semantically these are the plain encodings (tag, length
  bytes, data); the bytes past the end of each tag are overwritten later
  or lie beyond the final length.

## F10. The search loops compute pointers beyond the end of the input

In `CompressFragment` (and `CompressFragmentDoubleHash`) the search loop
computes `next_ip = ip + bytes_between_hash_lookups` and only then compares
it with `ip_limit` (`if (next_ip > ip_limit) goto emit_remainder`). With
`skip >> 5` this can be up to about `n / 32 + 2` bytes beyond `ip_limit`,
i.e. beyond the end of the input (formally undefined behaviour in C++ when
it is more than one past the end, but harmless in practice). The compiled
code compares the pointers unsigned, so it behaves as the source only if
that pointer does not wrap around the top of the address space. **Hypothesis
of the machine proofs of the fragment compressors:
`val src + LENGTH inp + 65536 < 2 EXP 64`** (true of every user-space
address on AArch64 Linux).

