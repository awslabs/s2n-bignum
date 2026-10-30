# AES-128-GCM x8 import provenance

## Current implementation

The current `aes128_gcm_enc_alt.S` and its HOL Light proof adapt the AES-256
encryption implementation at s2n-bignum commit
`330672965f9ee29eaa27df14c484806d7b8ef0bc`. They retain its instruction scheduling,
bulk loop, drain and short-message paths, and proof organization. The required
AES-128 changes use ten rounds, eleven round keys and a 176-byte key schedule,
with corresponding instruction addresses and zero-key constants.

The current assembly SHA256 is
`b8c73093377de01a49a048239f8cee850ffffabcb1422f351a4be57811b0b345`.
Its executable code occupies 5,588 bytes with BTI and 5,584 bytes without BTI.
The proof SHA256 is
`d924ed9b989270191fc18c47d9548043781d8d5cef44b7a8c6e2cfac7e13625c`.

The current native tests share the AES-128 KAT and Wycheproof drivers across
the existing encrypt/decrypt kernels and this encrypt alternative. They use
all 18 nonempty whole-block, full-tag records from AWS-LC's
`aes_128_gcm_tests.txt`, plus all 21 valid nonempty whole-block AES-128,
128-bit-tag records from its vendored Wycheproof `aes_gcm_test.json`.
The headers are the same vector sets used by the AES-128 decrypt alternative
in s2n-bignum PR #482 at `8914d805effbabf66a70b1ad225c8f8f83eafa66`.
`tests/verify_aes128_gcm_import.py` checks every field and complete eligible
record set against the original corpora, alongside the eleven verbatim
AWS-LC C reference bodies. The independent random differential, counter
rollover and no-access guard tests remain in place.

The sections below describe the original October 26, 2026 AWS-LC import
baseline, including its historical hashes, instruction addresses and native
checks. They establish the import's lineage; their 3,756/3,752-byte sizes and
ELF offsets describe that baseline rather than the current implementation.

## Original AWS-LC import baseline

Imported `aesv8_gcm_8x_enc_128` as `aes128_gcm_enc_alt` from AWS-LC
revision `532ff2339`, source
`crypto/fipsmodule/modes/asm/aesv8-gcm-armv8-unroll8.pl`.
Only this encryption symbol was imported.

| Artifact | SHA256 |
| --- | --- |
| AWS-LC Perl generator | `51e2827d584d7ea4d5c04ebfb87ae599e72684b39102483fc2d0af59fc731b65` |
| Complete generated `linux64` output | `416c31f043cc6690bee1e925fbc84f2fec6520678b03eac4e851309bf14ea363` |
| Imported `.S` | `403b2c59acffb558b8aa3eb264563b574dc78c55d578346bb8b1aca2747f526a` |
| Default assembled `.o` | `b56b80f5e8716f0f704516292125b9e426d25e1948ed8de4a7ad8fb99c280274` |

Generate within the target repository so the reference repository remains
read-only:

```sh
mkdir -p .import-001
perl ../aws-lc/crypto/fipsmodule/modes/asm/aesv8-gcm-armv8-unroll8.pl \
  linux64 .import-001/aesv8-gcm-armv8-unroll8.S
```

The concrete AES128 encryption function occupies generated lines 16–1299.
Exclude its optional `BORINGSSL_DISPATCH_TEST` block. Its normal generated
body has 952 instructions, including the initial BTI.

## Source adjustments

- Replace AWS-LC includes, preprocessor architecture guards and symbol
  directives with the internal ARM header and house directives. Rename the
  exported symbol and `.L128_enc_*` labels to `L128_enc_*`; retain the latter
  as local symbols. Declare `.arch armv8.2-a+crypto+sha3`.
- Remove optional dispatch-test instrumentation.
- Add `tst x1, #127; b.ne L128_enc_ret` after the existing zero-length
  check. Both rejected cases branch before any stack or buffer access.
- Replace the generated stack save/restore instructions with CFI-annotated
  macros that expand to the same instructions: `CFI_PUSH2N(d8,d9,80)`,
  three `CFI_STACKSAVE2X` pairs, three `CFI_STACKLOAD2` pairs and
  `CFI_POP2N(d8,d9,80)`. Enclose the function with `CFI_START` and the final
  rejected-path `CFI_RET`.
- At `L128_enc_blocks_less_than_1`, delete the 14 instructions beginning
  with `and x1, x1, #127` and ending with
  `and v9.16b, v9.16b, v0.16b`. This removes the partial-bit mask and the
  existing-output load. Also delete `bif v9.16b, v26.16b, v0.16b`.
  Accepted lengths always end with a complete block, so the retained
  ciphertext store and GHASH update need no partial-block mask.
- Retain all other generated instructions in order, including the raw
  `.inst` encodings for EOR3.

An independent disassembly comparison assembled the isolated generated
function, removed the 15 documented tail instructions from that instruction
list, and removed the two added guard instructions from the import.
The resulting lists both contain 937 instructions in the same order.
All non-branch instruction words match exactly; all branches preserve their
mnemonic and destination label. Branch displacement words differ because
the two additions and fifteen deletions change code offsets.

## Assembly, ABI and CFI checks

The family rule assembles successfully:

```sh
make -C arm/aes_gcm aes128_gcm_enc_alt.o
readelf --debug-dump=frames arm/aes_gcm/aes128_gcm_enc_alt.o
readelf -n arm/aes_gcm/aes128_gcm_enc_alt.o
objdump -d arm/aes_gcm/aes128_gcm_enc_alt.o
```

Default `.text` length is `0xeac` bytes (939 instructions). Entry is BTI at
offset `0`; the zero-length and whole-block guards are at `0x4`, `0x8` and
`0xc`; the first memory access is the stack save at `0x10`.
The success epilogue restores at `0xe90`, `0xe94`, `0xe98`, `0xe9c` and
returns at `0xea0`. The rejected path writes zero to `w0` at `0xea4` and
returns at `0xea8`.

The frame is 80 bytes: 64 bytes save d8–d15, and the final 16 bytes contain
the reduction constant. No callee-saved GPR is modified. The key loads read
exactly bytes `[0,176)` via pairs at offsets 0, 32, 64, 96, 128 and a
16-byte load at 160. All H-table accesses remain within `[0,192)`, with the
largest single-vector offset 176. Every memory operation through the output
pointer x2 is a store.

`readelf --debug-dump=frames` confirms CFA offset 80 after the first save;
d8–d15 are described at CFA offsets -80 through -24, and their restores
return CFA to offset zero at `0xea0`. The rejected-path label physically
follows the complete epilogue, so its unwind state is also the original
caller frame. GNU property notes advertise BTI.

The `NO_IBT=1` plus `S2N_BN_HIDE_SYMBOLS=1` preprocessing/assembly variant
also passes:

```sh
cd arm/aes_gcm
cc -E -DNO_IBT=1 -DS2N_BN_HIDE_SYMBOLS=1 \
  -I../../include aes128_gcm_enc_alt.S |
  as -o ../../.import-001/aes128-noibt-hidden.o -
```

That symbol is global hidden, has `.text` length `0xea8` (one fewer
instruction), starts with the zero-length guard, and has no BTI property
note. Its CFI describes the same frame and restores, shifted down four
bytes. The default object was preserved for the native import gate.

Functional, KAT and guard results are recorded in the session checklist and
summary; this document records assembly provenance and the independent
instruction/CFI audit.

## Verbatim reference and import gate

AWS-LC has no standalone C counterpart for the fused kernel. The complete
`CRYPTO_gcm128_encrypt_ctr32` definition from
`crypto/fipsmodule/modes/gcm.c:596` is copied byte-for-byte into `tests/test.c`,
along with the unchanged AArch64 `hw_gcm_encrypt` definition at line 106.
For lengths at least 256 bytes, two copies of the context run the same
enclosing function with `use_hw_gcm_crypt` disabled or enabled. The enabled
case reaches the exact upstream AES128 substitution call at `gcm.c:122`.
Surrounding aliases map that call to the imported symbol. The C path uses
the complete upstream nohw GHASH internals from `gcm_nohw.c`, and both paths
receive the existing scalar AES C callbacks. For shorter messages the
imported kernel is additionally compared directly with the upstream C mode.

Four upstream endian helpers, five complete nohw GHASH functions, the
AArch64 dispatch and the enclosing mode give eleven verbatim definitions.
Their source locations are marked beside the definitions. No copied
function body is edited; all required types, aliases and callback glue are
outside the bodies.

Ten nonempty, whole-block AES128 records are copied from AWS-LC
`crypto/cipher_extra/test/aes_128_gcm_tests.txt`, at KEY lines
116, 228, 340, 440, 447, 486, 502, 510, 526 and 534. The source SHA256 is
`e7160786d8de188416b6e04cf45b9c516c5030c95f08bd92b4ff5085940ffdb8`;
the full source revision is `532ff233935aa07b45f8e1fd83f5dc0c9b95c049`.
All six fields of each complete record are preserved, with upstream `""`
represented as the empty byte string. The records cover 16–256-byte
messages, 12- and 64-byte IVs, and empty and nonempty AAD.

Native import checks passed on 2026-10-26:

```sh
make -C arm/aes_gcm -B aes128_gcm_enc_alt.o
make -C arm -j4 libs2nbignum.a
make -C tests test
make -C benchmarks benchmark
python3 tests/verify_aes128_gcm_import.py ../aws-lc
cd tests
./test -500 aes128_gcm_enc_alt
./test -1 'known value tests for aes128_gcm_enc_alt'
./test -50 aes128_gcm_
./test -1 'known value tests for aes256_gcm_'
./test -1 'Wycheproof vectors for aes256_gcm_'
```

The first selected run passes four drivers: 66 deterministic
boundary/rollover cases plus 500 random cases against verbatim AWS-LC C;
32 deterministic lengths, zero and 500 random cases against the independent
AES128 reference; the existing whole-block rejection/no-access guard; and
128 explicit counter rollover cases. All ten imported KATs pass.
The existing AES128 encrypt/decrypt random tests pass, as do all 60 AES256
known-value and 68 AES256 Wycheproof cases across the four existing kernels.
Test compilation reports only the pre-existing unused-symbol warnings.

The test harness intentionally returns status 1 when selection skips other
tests, even when every selected driver passes. The successful filtered runs
end with `Skipped N but all M selected tests passed`, with no failure,
disparity or inapplicable-driver messages. Use negative repetition counts
as above to preserve the selection; positive counts enable unrelated extra
tests.

The five new benchmark entries also execute successfully. This completes
the import gate; functional and safety proofs are the subsequent pipeline
stages.
