# Notes on the mlkem-native AArch64 proofs

This folder holds notes on the HOL Light proofs of mlkem-native's
compiled AArch64 code. Each build (compiler, flags, link mode) has its
proofs in `arm/proofs/mlkem_native/<build>/` and its transcribed image
in `arm/mlkem_native/<build>/`, and all builds are proved against the
same specifications. gcc12_O2 came first; LLM agents under one
coordinator ported its proofs to the other builds. The notes describe
the state at 19f9abc7.

| build | what is different | functions verified |
|---|---|---|
| `gcc12_O2` | the precedent; one translation unit per source file | 116 / 116 |
| `gcc12_O2_mono` | whole library as one translation unit: 72 functions inlined, registers allocated across calls | 62 / 62 with code of their own |
| `gcc12_O3` | gcc 12 `-O3`: vectorised and unrolled | 98 / 115 |
| `clang17_O3` | clang 17 `-O3`: vectorised, other scheduling; paused | 77 / 116 |

## Files

- [comparison.md](comparison.md): what the gcc12_O2 and gcc12_O2_mono
  proofs share, which differences the binary forces and which are
  accidental, and what to clean up.
- [automation.md](automation.md): where money, machine time and agent
  time went, and one prioritised list of changes for writing, checking
  and organising the next port.
- [benchmarks.md](benchmarks.md): pinned timings of every gcc12_O2 and
  gcc12_O2_mono proof.

## Main findings

1. gcc12_O2 and gcc12_O2_mono share 69% of the code lines of their 63
   same-named proof files, and about 86% of the differing lines are
   forced by inlining and cross-call register allocation.
2. Most of the accidental rest (estimate: 12-20% of the differing lines)
   comes from 11 early gcc12_O2 kernel proofs done on separate object
   files instead of the image.
3. The agents and the coordinator cost $3,528 at Anthropic API list
   prices, and 51% of that paid for rewriting prompt caches after
   waits; 440 of the 864 rewrites came when the Bash tool's 10-minute
   timeout woke a waiting agent.
4. Every official run re-proves all its callees: one full run of every
   file adds up to 51.3 CPU-hours for gcc12_O2 and 29.6 for mono
   (measured), against 5.5 and 4.7 if each file were proved once; about
   191 against 25 for all four builds. Splitting statements from proofs
   (in progress) brought one gcc12_O3 wrapper from 16,175 s to 594 s.
5. Cheap mechanical edits caused the most expensive failures: a missing
   `read SP s` in one callee call cost a failed 4.5-hour make, and a
   merged GOT numeral led to a 5.8-hour stall of the coordinator.
6. Most build-specific numbers can be computed from the binary: a
   130-line stack-depth analysis reproduces all 105 frames stated in
   gcc12_O2.
7. Haiku ports same-code functions for $0.4-3 per file but does not
   catch its own mistakes; Opus, at $5.5-11 per file, is the cheapest
   choice for code without a precedent.
8. Done since the analysis: `check_offsets.py` now also catches
   `word_add (word pc) (word N)` and decimal GOT addresses, the merge
   gate fails on any offset problem, and the shared GOT tactics use
   layout names (to be committed after the benchmark run re-checks
   their users); 92 GOT numerals remain in gcc12_O2.
