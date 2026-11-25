# Performance of the slowest snappy proofs (stream PERF-2)

No theorem statement changes. All times are in seconds, from one process per
proof file on one domain (S2N_PAR_DOMAINS=1, HOL_PAR=1), so wall time is CPU
time. "Proof" is the "Running time" of the .correct file (it includes about
90 s to load the libraries); peak memory is the largest resident set of the
process (sampled every 3 s). The breakdowns come from TIMED_TAC
(common/tactic_timing.ml, S2N_TACTIC_TIMING=1) and from a dev-only wrapper
of `prove` that printed the time of each theorem (not committed).

## Baselines (before)

| proof file | proof (s) | peak | what dominated |
|---|---|---|---|
| raw_uncompress_sourcep_charp | 3319 | 1.7 GB | 15 calls of DecompressAllTags<SnappyArrayWriter>: 2228 s, up to 1207 s for one call |
| compress_fragment_double_hash_loop5 | 1743 | 1.8 GB | the main theorem: 1606 s |
| compress_fragment (lib + seg15, seg2, seg4, seg6 + proof) | 1239 | 29.2 GB | SNAPPY_CF1_SEG4: 1057 s |
| snappy_decompressor_decompress_all_tags_snappy_array_writer | 1320 | 13.2 GB | segments T_B 724 s, T_S 463 s |
| internal_uncompress_validator | 519 | 1.7 GB | the main theorem: 434 s |
| decompress_branchless | 842 | 1.8 GB | 408 theorems, many leaf lemmas of ~18 s, the main theorem 130 s |

In the link, CompressFragment's segment files were loaded before the jobs
(they were "files that the proof file loads"), so their ~1100 s were serial,
before any job started.

## RawUncompress(Source*, char*) and InternalUncompress<Validator>

Breakdown of RawUncompress (TIMED_TAC, before): the case L >= 5 took
2812 s, the 15 calls of DecompressAllTags 2228 s. One call cost 2 s to
1207 s, growing with the number of header bytes and with what the proof
had done before (a case run alone was 2-5 times faster than inside the
full proof). Inside a call (dev copies of the call tactics): the moves of
the facts across the call (GEN_BSTEP_CALL_TAC, `after`) took all of it;
each fact needs |- orthogonal_components c d for each clause d of the
callee's frame, and for memory these go through NONOVERLAPPING_RULE,
whose integer arithmetic gets every numeric assumption
(FILTER_CANONIZE_ASSUMPTIONS, disequalities included) and splits the cases
of each disequality. The case split on LENGTH l left ~(LENGTH l = k)
twice for each k < L (ASM_CASES_TAC, then RU_CASE_TAC again), and the
header bytes read before the call (bytes8 at inp + k) were moved too, each
by up to 7.6 s.

Changes (array_writer.ml, used by both proofs): before the call,
BSTEP_DROP_NUM_DISEQS_TAC drops the numeric disequalities that do not
mention the state, and ~keep:(bstep_keep_not_bytes8_at `inp`) does not
carry the header bytes across. RawUncompress: the cases of L from one
disjunction.

| | before | after |
|---|---|---|
| RawUncompress(Source*, char*), proof | 3319 s | 188 s |
| its 15 calls of DecompressAllTags | 2228 s | ~30 s |
| case L >= 5 (dev, alone) | 2812 s (in the full proof) | 45 s |
| InternalUncompress<Validator>, proof | 519 s | 190 s |
| peak memory | 1.7 GB | 1.7 GB |

## CompressFragment

The segment files were loaded by compress_fragment_proof.ml and therefore
by the link before its jobs (serially). They are now spec/proof pairs, one
job each. Peak memory of each piece is 1.8 GB (the whole file reached
29 GB in one process; the pieces alone do not).

| piece | proof (s), one process each |
|---|---|
| compress_fragment_seg15 | 141 |
| compress_fragment_seg2 | 150 |
| compress_fragment_seg4 | 1046 |
| compress_fragment_seg6 | 136 |
| compress_fragment (from the segment contracts) | 129 |
| before: compress_fragment with all segments | 1239 (29.2 GB) |

seg4 (TIMED_TAC, 1054 s): arithmetic (SNAPPY_ARITH_TAC, already with the
relevant facts) 314 s in 2584 successful calls and 129 s in 1058 failing
ones; the bstep blocks 307 s; MOD elimination 206 s; S4_VAL_TAC 227 s; the
output merges 155 s; spread over thousands of calls, with no single cause.

## compress_fragment_double_hash_loop5

Before (TIMED_TAC over the file, 1721 s): MEMSAFE_EVENTS_TAC at the 13
leaves 930 s; CF2_ARITH_TAC 425 s (239 calls); the model steps 249 s; the
MOD elimination 159 s; bstep 26 s.

Changes: cf2_arith_prove in the model spec (arithmetic first from the
numeric assumptions connected to the goal, relevant_arith_facts of
common/arith_facts.ml, then from all as before), used by CF2_ARITH_TAC,
CF2_MOD_ELIM_TAC, CF2_INPUT_TAC, CF2_COND_EQ_TAC and two tactics of
loop5; the events at the leaves by SNAPPY_EVENTS_TAC (events.ml), then
MEMSAFE_EVENTS_TAC as before if it fails (it did not).

| | before | after |
|---|---|---|
| loop5, proof | 1721 s | 510 s |
| the other proofs of CompressFragmentDoubleHash | 41-155 s (link) | 130-222 s standalone, incl. ~95 s load |

## DecompressAllTags<SnappyArrayWriter>

Before: one process, 1320 s, 13.2 GB; segments E 6 s, L_B 11 s, L_S 12 s,
T_B 724 s, T_S 463 s; each tag class of T about 100 s (dev run with a
timer per class: lit 74 s, long240/244/248 106-108 s, ...).

Change: the lemmas and tactics in ..._snappy_array_writer_lib.ml, T by
tag class (a conjunct of the precondition) as 16 jobs, the proof file
combines them (DAT_T_FROM_CLASSES_TAC).

| piece (one process each, ~95 s of it loading) | proof (s) |
|---|---|
| proof file (E, L_B, L_S, the combination, the theorem) | 132 |
| T_B lit, copy1, copy2, copy4 | 178, 180, 175, 173 |
| T_B long240, long244, long248, long252 | 212, 213, 213, 214 |
| T_S lit, copy1, copy2 | 140, 176, 165 |
| T_S long240, long244, long248 | 172, 175, 112 |
| T_S long252, copy4 (contradictions) | 102, 103 |
| peak memory | 1.8 GB each (before 13.2 GB) |

## DecompressBranchless<char*>

Before: 842 s in one process, 408 theorems; 28 near leaves (pattern copies
by offset) of ~18 s each, the main theorem 130 s.

Change: the lemmas and tactics in decompress_branchless_lib.ml, the near
leaves as three jobs (offsets 0..10 with 1-byte offsets; 0..8 and 9..16
with 2-byte offsets), each one conjunction of leaf statements.

| piece (one process each, ~100 s of it loading) | proof (s) |
|---|---|
| decompress_branchless (the other leaves, J, E, loop, theorems) | 334 |
| near1, near2a, near2b | 320, 281, 270 |

## CompressFragment seg4 by the match length

seg4 alone was the longest job of the link (975 s). Its time is spread
over thousands of calls (above), so it is split instead: the tactics and
lemmas in compress_fragment_seg4_lib.ml (its state s4_counter,
s4_rewrites, s4_pc_extra now par_local_ref; names that other top-level
files define renamed: S4_ARITH_TAC, S4_MOD_ELIM_CONV, S4_EXEC, ...), the
segment proved in five jobs, each with a case of ML = snappy_match_length
inp (c + 4) (ip + 4) as a conjunct of the antecedent
(compress_fragment_seg4{a..e}), and compress_fragment_seg4_proof.ml
combining them (S4_FROM_CASES_TAC). The cases kill the branches of the
other cases by arithmetic, as the copy tags of EmitCopy depend on ML.

| piece (one process each, ~95 s of it loading) | proof (s) |
|---|---|
| a: ML < 8 | 221 |
| b: 8 <= ML <= 60 | 222 |
| c: 60 < ML < 64 | 265 |
| d: 64 <= ML, s4_rest <= 64 | 531 |
| e: 64 <= ML, 64 < s4_rest | 524 |
| seg4 from the cases | 128 |
| before: seg4 in one piece | 1046 |

With three cases first (ML < 8, <= 60, > 60) the last took 919 s; the
loop of 64-byte copies (ML >= 64) is most of it.

## The link before its jobs

The link loads every file that a proof file needs before the jobs start,
serially (link2: about 304 s of 1279 s). A dev profile of those files:
relative.ml (the base) 59 s, the needs of compress_fragment_lib.ml 58 s,
decompress_branchless_lib.ml 50 s, the DecompressAllTags<SnappyArrayWriter>
lib 37 s, dat_validator_lib.ml 19 s. In the two new libraries most of it
was three lemmas: SNAPPY_LMO_TABLE 31 s and DB_AND255_X 11 s (branchless),
DAW_LMO_TABLE 15 s. They are now stated with assuming_proofs
(common/relative.ml) in the libraries and proved in jobs of their own
(decompress_branchless_lemmas, ..._snappy_array_writer_lemmas: 120 s and
102 s standalone, ~95 s of it loading).

## Summary per target

"Before" and "after" standalone are the Running time of the proof file
alone (one process, one domain, ~90-100 s of it loading); "link" is the
job time in the final link (8 domains, no loading).

| target | before, standalone | before, link job | after, standalone | after, link job(s) | peak memory before / after (standalone) |
|---|---|---|---|---|---|
| RawUncompress(Source*, char*) | 3319 s | 3137 s | 188 s | 120 s | 1.7 / 1.7 GB |
| compress_fragment_double_hash_loop5 | 1721 s | 1572 s | 510 s | 388 s | 1.8 / 1.8 GB |
| CompressFragment (segments + proof) | 1239 s, one file | ~1100 s serial, before the jobs | longest piece seg4d 531 s | seg4d 411 s, seg4e 405 s, the others 0-136 s | 29.2 / 1.8 GB |
| DecompressAllTags<SnappyArrayWriter> | 1320 s | ~1284 s | longest piece 214 s | 0.4-173 s (18 jobs) | 13.2 / 1.8 GB |
| InternalUncompress<Validator> | 519 s | 427 s | 190 s | 112 s | 1.7 / 1.8 GB |
| DecompressBranchless<char*> | 842 s | ~818 s | longest piece 334 s | 204 s, 203 s, 162 s, 150 s, 43 s | 1.8 / 1.8 GB |

What dominated:
- RawUncompress, InternalUncompress: the orthogonality proofs of the facts
  moved across the call of DecompressAllTags (arithmetic over all numeric
  assumptions, splitting every disequality; duplicated disequalities).
- loop5: MEMSAFE_EVENTS_TAC at the leaves; arithmetic over all numeric
  assumptions in the model spec.
- CompressFragment: structure (serial loading in the link); seg4 itself
  spread over thousands of calls, hence split by the match length.
- DecompressAllTags<SnappyArrayWriter>, DecompressBranchless: one process
  for independent cases of about 100 s (tag classes) and 18 s (near
  leaves); split.
- The link before its jobs: two table lemmas and a BITBLAST lemma of the
  new libraries (moved into jobs).

## The link

`make snappy/gcc12_O2/link.correct` (HOL_PAR=1).

| | before (b51bb0ae) | link2 (cd9a54f3) | final (e6d65204) |
|---|---|---|---|
| domains | (as run by the caller) | 8 | 8 |
| result | passes | passes, 148 contracts proved and closed | passes, 156 contracts stated, 156 proved and closed |
| process (Running time) | ~70 min | 1279 s | 1018 s |
| all jobs | bounded by RawUncompress, 3137 s | 975 s (seg4) | 781 s (throughput: the jobs sum to 6245 s) |
| before the jobs and the closing | > 1100 s (CompressFragment's segments) | 304 s | 237 s |
| with the native build | | 1505 s | 1243 s |
| peak memory | (seg4 file alone 29 GB) | 5.2 GB | 29.9 GB |

The final link is no longer bounded by one job but by the total work on 8
domains (the longest jobs, seg4d/seg4e and loop5, take 388-411 s); with
more domains it would approach ~400 s plus ~240 s of loading. The peak of
the final link (29.9 GB, sampled RSS of the process with 8 jobs at once)
is much higher than link2's 5.2 GB; no single job exceeds 1.8 GB alone,
and it was not investigated further.
