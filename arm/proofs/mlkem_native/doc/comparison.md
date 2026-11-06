# gcc12_O2 and gcc12_O2_mono: what the proofs share and why they differ

Both builds are mlkem-native compiled by gcc 12 with `-O2`. `gcc12_O2`
compiles each source file on its own; `gcc12_O2_mono` compiles the
library as one translation unit, so gcc inlines 72 of the 116 functions
into their callers and allocates registers across calls (`-fipa-ra`).
This note compares the proofs in `arm/proofs/mlkem_native/gcc12_O2/`
and `.../gcc12_O2_mono/` at commit 19f9abc7, and sorts each difference
into *systematic* (forced by the binary) or *accidental* (a choice of
the proof's author).

63 proof files have the same name in both builds. The mono file proves
the same function, or the static kernel it became: mono `poly_ntt.ml`
proves `mlk_poly_ntt_c`, O2 `poly_ntt.ml` proves `mlkem_poly_ntt`.

## Summary

- 69% of the code lines of the 63 pairs are shared (77% of the tokens).
  25 files are the same once build name, function symbols, register
  frames and numerals are masked.
- No input, output, bound or FIPS 203 function in the statements
  differs. Of 138 pairs of `IMAGE_SUBROUTINE_{CORRECT,SAFE,FULL}`
  theorems, 18 are identical, 40 differ only in the register frame, 47
  in frames and numerals (stack sizes, buffer offsets), and 33 in more
  (preconditions, callee contracts, names of read-only constants).
- About 86% of the differing lines are systematic: glue for inlined
  wrappers, lemmas for inlined loops, exact register frames, new stack
  frames. Estimate: 12-20% are accidental, most of them from 11 O2
  kernel proofs that were done on separate object files.

**Method.** Code lines (comments stripped, build name renamed) are
matched with difflib. "Shared" is 2·matched/(lines O2 + lines mono).
"Normalised" also maps mono function symbols to their O2 names and masks
register frames and numerals.

## 1. By function group

| group (files) | code lines O2 / mono | shared | normalised | main reason for the differences |
|---|---|---|---|---|
| kernels, same code (9) | 2660 / 2689 | 96% | 99% | exact frames, symbols, a NOP, registers |
| kernels on a separate `.o` in O2 (9) | 6829 / 5797 | 77% | 78% | **accidental**: separate transcription |
| Keccak / SHA3 / SHAKE (9) | 6376 / 4789 | 36% | 38% | inlined xor/extract loops, clones, memcpy; permute **accidental** |
| sampling (9) | 5065 / 5308 | 70% | 73% | SHAKE128 inlined into `gen_matrix` k3 |
| K-PKE, check_pk, dec (12) | 11416 / 16453 | 63% | 69% | glue for inlined polyvec wrappers |
| KEM wrappers (15) | 4950 / 4956 | 96% | 100% | callee frame sizes, buffer offsets |
| **total (63)** | 37296 / 39992 | **69%** | 73% | |

O2 has 53 more files (18,200 lines) for functions that mono inlines,
such as the polyvec wrappers and `indcpa_dec`. Their content reappears
in the callers' mono proofs and in three new shared files
(`polyvec_inline.ml`, `indcpa_inline.ml`, `inline_loops.ml`).

## 2. Systematic differences

**Exact register frames.** With `-fipa-ra`, a caller may keep values in
caller-saved registers across a call to a static kernel that it knows
leaves them alone. `mlkem512_check_pk` keeps X8, X9 and Q2/Q3 live
across six kernel calls. An ABI frame would allow the kernel to destroy
them, and the caller's proof would fail. 21 mono files therefore list
the registers each function writes:

```
O2:   (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
mono: (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,     (poly_frombytes.ml)
```

Callers need exact frames for 10 of the 17 kernels (a liveness analysis
of the listings shows which); the kernels agent used them for all 17.
O2's own `rej_uniform.ml` confirms the cause: `rej_uniform` is static in
`sampling.c`, so IPA-RA applies even in O2, and that file already has
the exact frame.

**Function and constant names.** Out-of-line kernels carry the names of
their static C implementations (`mlkem_poly_frombytes` becomes
`mlk_poly_frombytes_c`). Constants loaded by inlined code are named
after the function that now contains the load, which changes the
read-only regions of 10 SAFE theorems:

```
O2:   word(pc + mlkem_poly_tomont_consts),32
mono: word(pc + mlkem512_indcpa_keypair_derand_const2),16;
      word(pc + mlk_poly_invntt_tomont_c_const2),16      (keypair_derand_k2.ml)
```

**Stack frames and buffer offsets.** 33 files state different frame
sizes, because callee frames vanish or move into the caller when code is
inlined: `check_pk_k2` 1888 → 1856, `dec_k2` 13024 → 16640 (the
`indcpa_dec` buffers now sit in `dec`'s frame), `shake256` 560 → 576.
The addresses of 32-byte-aligned buffers follow the frame size. When the
frame changes by 16 mod 32, the aligned and the unaligned value swap
roles (`enc_k2.ml`):

```
O2:   word(if aligned 32 sp then 12288 else 12272)
mono: word(if aligned 32 sp then 12288 else 12304)
```

**Specialised code, new preconditions.** gcc specialises static
functions to their only callers (`.constprop` clones), drops zero tests
and turns lengths into constants. The statements gain preconditions that
hold at every call site, e.g. `0 < mlen` in `absorb_once` and
`inlen = 33` in `shake256x4`; `shake256` now calls `memcpy` and takes a
`memcpy_contract`. These are 23 of the 33 statements that differ in more
than frames and numerals.

**Inlined wrappers become glue.** One O2 call of a polyvec function
becomes k kernel calls, plus a split of the precondition and a join of
the postconditions (`check_pk_k2.ml`):

```
O2:   LOCAL_FROMBYTES_TAC [...] 16 THEN      (* polyvec_frombytes_k2 *)
mono: POLYVEC_INLINE_SPLIT_TAC POLYVEC_FROMBYTES_SPLIT_GEN `pk:int64` 2 THEN ...
      LOCAL_FROMBYTES_TAC [...; `(n DIV 2 EXP 0) MOD 2 EXP 3072`; ...] 18 THEN
      LOCAL_FROMBYTES_TAC [...; `(n DIV 2 EXP 3072) MOD 2 EXP 3072`; ...] 23 THEN
      ... CHECKPK2_REDUCED_TAC `s29:armstate`         (* join *)
```

This is most of the 9,340 rewritten lines of the K-PKE group. Inlined
loops of `poly_add`/`sub`/`tomont` become lemmas from the loop label to
its exit, generated by `INLINE_PTR_LOOP` (`inline_loops.ml`). The
d11/d5 compress/decompress loops inlined at k4 are redone the same way,
which is why `dec_k4.ml` has 2,300 code lines against 929 in O2. The
DWARF labels for inlined calls (`<f>_in_<g>`) are proof boundaries in
only 5 files: inlined code is usually interleaved with the caller's.

**Smaller items.** A moved NOP shifts step counts (`poly_cbd2`
`(11--12)` becomes `(11--13)`). Six kernels use permuted registers (236
lines). Identical code folding lets mono `poly_getnoise_eta2_k2.ml`
restate the k4 theorem in 84 lines, where O2 proves the copy (290).

## 3. Accidental differences

**Separate transcriptions in O2.** 11 O2 files (the 9 kernels of the
table's second row, `poly_tomont` and `keccakf1600_permute`) prove the
function on its own object file (`define_assert_from_elf`) and transfer
the result to the image with `MLKEM_NATIVE_IMAGE_TAC`. They were the
first functions verified (bfb0391d to f24ad7d4, 27-28 Oct), before the
image existed; no other build does this. Evidence that this is
accidental: `poly_reduce` has the same code in O2, gcc12_O3 and mono,
and the mono file shares 93% of its lines with gcc12_O3 (100%
normalised) but only 73% with O2.

**Different proof structure for the same code.** `keccakf1600_permute`
has the same loop body in all three gcc builds. The mono file, ported
from gcc12_O3, proves FULL first and derives CORRECT and SAFE with
`ENSURES_PREPOST_WEAKEN`; O2 proves the three separately. Shared lines:
95% with gcc12_O3, 41% with O2. The same choice adds `p < 128` to the
SAFE theorem of mono `keccak_absorb_once.ml`.

**GOT numerals.** gcc12_O2 reads entries of the global offset table
(GOT) at numeric offsets from `pc`:

```
read (memory :> bytes64 (word_add (word pc) (word 131064))) s = g
```

There are 92 such numerals in 30 gcc12_O2 files. The mono ports
replaced them with layout names (`got_stack_chk_guard`, `got_memset`,
`got_memcpy`); for `check_sk` and `gen_matrix` k2/k4 that was the only
change. The shared tactics `KEM_GOT_TAC`
(`arm/proofs/utils/mlkem_native_kem.ml`) and `INDCPA_GOT_TAC`
(`mlkem_native_indcpa.ml`) matched numerals too, which worked in mono
only because its GOT happens to sit at the same offsets.

*Done since:* both tactics now use
`map layout ["got_stack_chk_guard"; ...]` (to be committed after the
benchmark run re-checks their users), which makes mono's
`INLINE_GOT_TAC` a duplicate. `check_offsets.py` now catches this form
and found 4 numerals in gcc12_O3 `shake256.ml` (fixed, rerun pending);
the merge gate fails on any offset problem.

**Duplicates under new names.** `ALIGNED_16_32_WORD_AND` has 16 copies
under 9 names in O2 and 20 copies under 16 names in mono (468 lines).
Mono `poly_getnoise_eta2_k4.ml` re-proves it as
`GETNOISE_ALIGNED_16_32`, although it `needs` `shake256.ml`, which has
it. A likely cause: the agents developed against statement-only stubs,
which lack the callees' helper lemmas.

**Size of the accidental part (estimate).** 24,292 lines differ. Of
these, 2,718 are small token changes (systematic: numerals 1,728,
frames 284, registers 236, symbols 88; accidental: transcription hex
words 204, GOT numerals 94, line breaks 84). About 3/4 of the 2,960
differing lines of the separate-transcription kernels, 90% of
`permute`'s 995, the GOT and formatting lines and about 115 lines of
renamed copies give about 3,400 accidental lines, 14%. `absorb_once`
mixes both kinds, so a fair range is 12-20%.

## 4. What both builds share

- **FIPS 203 lemmas:** all 24 `KPKE_*` lemmas (`KPKE_ENCRYPT_K2_RESULT`,
  ...) are the same up to whitespace, and so are the 11 in gcc12_O3.
  Each build holds its own copy, 2,322 lines.
- **Proof plans:** the indcpa stage tactics (`KP2_MATRIX_TAC`, ...) and
  the 41 `INDCPA_*` tactics from `utils/mlkem_native_indcpa.ml` are
  unchanged, because the mono glue rebuilds the O2 postconditions of the
  inlined wrappers. Of 1,712 top-level definitions in the 63 O2 files,
  895 (52%) are identical in mono, 551 changed, 266 gone.
- **Whole files:** 25 pairs are at least 99% the same after
  normalisation: check_sk k2-k4 and gen_matrix k2/k4 (one GOT line), the
  12 keypair/enc wrappers (frame sizes), 8 same-code kernels. Without
  inlining the top layer is shared even across vectorised kernels: O2
  and gcc12_O3 share 99-100% of `indcpa_enc_k2.ml`.
- Only gcc12_O3 and clang17_O3 use the build-independent tactic files
  `overlap.ml`, `interleave.ml`, `bitnorm.ml` and `copies.ml`.

## 5. What to clean up

1. Move the 24 `KPKE_*` lemmas (2,322 lines per build) into one shared
   file, e.g. `arm/proofs/mlkem_native/kpke.ml`. Keep one copy each of
   `ALIGNED_16_32_WORD_AND` (36 copies in the two builds), the
   BYTES128_HALVES lemma (21) and the BYTES_32_OF_HALVES lemma (15).
2. Restate the 11 O2 separate-transcription proofs in the image (the
   mono kernels agent's `sep2img.py` does this) and port `permute` from
   gcc12_O3. Estimate: about 3,000 fewer differing lines; the 9 kernels
   would differ from mono only in symbols, frames and registers.
3. Replace the 92 GOT numerals left in gcc12_O2 by layout names.
4. Turn the build-specific facts into parameters (build name in theorem
   names, an alias for the function symbol, the frame), so that each of
   the 25 near-identical pairs can become one file. This also needs one
   convention for list syntax and one for FULL-first proofs.

Harmless: comments, line breaks, list syntax (`[(st,200); (m,mlen)]`
and `[st,200; m,mlen]` are the same term), and exact frames where
callers do not need them. Generating frames, buffer offsets and read-only lists, and
the choice of frame policy, are in [automation.md](automation.md).

*Data:* line and token diffs of the proof files at 19f9abc7 (difflib
with the masking described above), a classifier for differing blocks, a
by-name comparison of top-level definitions; agent notes for the history
of single files.
