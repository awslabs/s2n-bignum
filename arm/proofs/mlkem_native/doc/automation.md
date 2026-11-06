# Automating the proof work: where the time and money went

The proofs of `gcc12_O2_mono`, `gcc12_O3` and `clang17_O3` (239 proof
files so far) were written by 40 LLM agents (Claude Opus, Sonnet and
Haiku 5.5) under one coordinator session. Each agent took one function
family on its own git branch, copied the gcc12_O2 proofs and edited them
until `make` passed; the coordinator merged the branches into
`mlkem-arm` with a script that checks the proof logs. This note says
where the money, machine time and agent time went, and what to change
for the next build, most valuable first.

Dollar figures are at Anthropic API list prices per million tokens:
Opus 5.5 $4 input, $20 output; Sonnet 5.5 $2, $10; Haiku 5.5 $0.10,
$0.50; cache reads $0.20 (Haiku $0.01); 5-minute cache writes 1.25
times the input price. "Estimate:" marks numbers not measured.

## 1. Where time and money went

### Money: paying to re-read context

| | measured |
|---|---|
| total | $3,528: agents $3,040, coordinator $488 |
| by model | Opus $2,633, Sonnet $855, Haiku $40 |
| by token kind | cache writes 54%, cache reads 39%, output 7% |
| calls that rewrote more than 100k tokens of cache | 864, costing $1,783 (51%) |
| of these, 9.5-10.5 min after the previous call | 440 |

A proof run takes 5 to 300 minutes. Agents waited for it in the
foreground, e.g. with `until ...; do sleep 15; done`. The Bash tool
stops such a call after 10 minutes and the agent wakes up, but the
prompt cache expires after 5 minutes. So each wake-up wrote the whole
context again, typically 400-600k tokens, about $2.50 on Opus.
Re-priced with a 1-hour cache lifetime (writes at 2 times the input
price), the same calls cost $1,957, 45% less (simulated).

### Machine time: every run re-proves its callees

`make` runs each proof file in a fresh process, and `needs` loads and
re-proves every callee file. gcc12_O3 `indcpa_enc_k2.ml` re-proves 42
other files this way: its run takes 16996 s, its own proofs an
estimated 2550 s.

| build | full runs, summed | each file once, one process | longest run |
|---|---|---|---|
| gcc12_O2 (117 files) | 51.3 h | 5.5 h | 2.17 h |
| gcc12_O2_mono (65) | 29.6 h | 4.7 h | 1.63 h |
| gcc12_O3 (98) | 84.3 h | 8.2 h | 4.72 h |
| clang17_O3 (77) | 25.8 h | 7.0 h | 2.73 h |
| total | 191 h | 25 h | |

The gcc12_O2 and gcc12_O2_mono rows are measured: pinned runs of every
proof, one per CPU ([benchmarks.md](benchmarks.md)). The gcc12_O3 and
clang17_O3 rows are estimates from logged wall times under load (±30%).

Symbolic stepping takes only 1-30% of a run (seven logs), e.g. 40 s of
5036 s for gcc12_O3 `keccakf1600_xor_bytes`. Every process first spends
200-280 s loading `arm/proofs/base.ml` (66 s), `common/mlkem_mldsa.ml`
(104-107 s) and, for indcpa/KEM files, `common/fips203.ml` (79 s);
compiling adds 79-228 s. Much of the rest is per-step rewriting of
assumptions, and simulating the code three times (CORRECT, SAFE, FULL)
in 67 files.

### Agent time: cheap edits, expensive failures

Compared with gcc12_O2, 104 files are ports with at most 3% new lines
(28 mono, 53 gcc12_O3, 23 clang17_O3), 67 are adapted and 67 mostly
rewritten. A port changes step numbers, frame sizes, buffer offsets,
registers and names. The whole diff of gcc12_O3 `check_pk_k2.ml` (about
40 lines) follows from one fact: the callees' frames grew from 32 to 64
bytes.

```
<   WORD_FORALL_OFFSET_TAC 1888 THEN
>   WORD_FORALL_OFFSET_TAC 1920 THEN
<       word_add sp (word(if aligned 32 sp then 64 else 80))`,
>       word_add sp (word(if aligned 32 sp then 96 else 112))`,
```

Top-layer files take 1 to 4.7 hours to `make`, so a mistake in them is
found late:

| incident | cost |
|---|---|
| gcc12_O3 `indcpa_enc_k4`: basemul_k4 at -O3 takes `stackpointer`, but the caller passed no `read SP s`. `SPECL` accepted the short list; the error came later, with a misleading hint | make failed after about 4.5 h; same bug in `indcpa_keypair_derand_k4` |
| clang17_O3 `check_pk_k2` (Haiku) debugged through the full `make`, 5 cycles of about 2 h (06:08 to 15:58); a stub harness then reproduced the error in 3 min | about 10 h |
| mono `poly_rej_uniform` merged with `pc + 131048`: the merge script printed "1 problems" but did not fail. The coordinator's `git reset --hard` to undo it was denied; its next command waited for user approval | coordinator stalled 5.8 h; the mono k3 chain waited about 6 h |
| `pc + 131024` copied from gcc12_O2 into gcc12_O3 keypair_derand k2-k4 and mono keypair_derand_k3 | gcc12_O3: k2 rejected at merge (6f830c71), 3 reruns that each re-prove an indcpa callee; mono: 3373 + 3491 s of reruns |
| mono k3 callers developed against a `gen_matrix_k3` stub with the gcc12_O2 frame 3632; the real one is 4400 | 3 dev runs of 851-1767 s |
| gcc12_O3 `indcpa_dec_k2`: buffer constant `word 127` kept, should be 159 | failed after about 85 min |
| 40 of 279 ledger rows merge a file again (SAFE/FULL later) | 24.4 h of make time |

The agents also wrote 411 one-off Python scripts (19,097 lines), many
for the same job: 24 stub makers or checkers, 9 step renumberers, 6
register or liveness analyses.

### Model per kind of task

| kind of work | model | $ per file | evidence |
|---|---|---|---|
| same-code port | Haiku | 0.4-3 | made the argument and `pc + 131024` mistakes above |
| different code, same-build precedent | Sonnet | 3-5 | mono kernels, mono fips202safe |
| no precedent | Sonnet | 8-24 | clang17_O3 fips202: 4 of 16 functions in 10.9 h |
| no precedent | Opus | 5.5-11 | gcc12_O3 codec, arith, fips202 |
| inlined loops, large context through long waits | Opus | 35 | gcc12_O3 sampling: $311 of $453 on cache rewrites |
| debugging a failed make | Opus | $19 total | found the enc_k4 cause in 4 min |

Without a precedent Sonnet costs more per file than Opus: cache reads
cost the same on both, and Sonnet needed more calls (163 per file
against Opus's 44 on fips202).

## 2. What to change, in order

**In progress: statements and proofs in separate files.** Each proof file
`X.ml` becomes `X_spec.ml` (statements, definitions, tactics) and
`X_proof.ml` (proofs). A caller loads only its callees' spec files and
proves its theorems with the callees' statements as hypotheses
(`assume_spec`; a variant of `prove` accepts only hypotheses that are
stated contracts). One generated link file per build loads every proof
file once, discharges the hypotheses with `PROVE_HYP` and requires the
top-level API theorems to have none left, followed by `check_axioms ()`.
This replaces #3, #4 and #12 below. Pilot on gcc12_O3: `keypair_derand_k2`
checks in 594 s instead of 16,175 s, `indcpa_keypair_derand_k2` in
1,187 s instead of 15,598 s; loading the callees' spec files is now 89%
of such a run. Work on branch `mlkem-arm-spec-split`.

| # | change | expected saving (evidence) | effort | risk |
|---|---|---|---|---|
| 1 | Wait on proof runs only as background jobs with a completion notice; 1-hour cache lifetime if available; restart agents at family boundaries (contexts under 250k tokens) | $1,100-1,600 (30-45%; 45% simulated) | a brief rule, a `waitpid.sh` helper | none |
| 2 | One fail-closed gate, run by agents **before** the official make and by the merge script | about 8 h of wall time in this run; most of the 24.4 h of re-merges | hours | none |
| 3 | Shared development harness: callee theorems taken from a cache of checked results; required before any make over 30 min | measured: mono `gen_matrix_k2` 1131 → 435 s; estimate: an `indcpa_enc_k2` iteration 4.7 h → under 1 h | 2-4 days | dev only |
| 4 | Official runs: each file proved once, one process per build or family | estimate: 187 → 26-45 CPU-hours; 3.6x measured once | 1-2 days | OCaml name clashes |
| 5 | Facts generator (frames, buffer offsets, written registers, SAFE regions): first a pre-make check, later layout names in the text | the frame and buffer incidents; 909, 661, 399 numeral-only lines (mono, O3, clang) | 2-3 days | analysis gaps |
| 6 | `CALL_TAC`: callee found by its `bl` target, arguments built from its theorem; `ARM_SUBROUTINE_SIM_TAC` fails on a short argument list | the 4.5 h enc_k4 failure; 215-649 hand-written argument lines per build | 2-3 days | ghost data matched wrongly |
| 7 | Classify functions before assigning; route models by kind; escalate early; start the top layer at once, against stubs | estimate: clang fips202 $45 and 2.5 h instead of $96 and 10.9 h; mono 19 h instead of 25.8 h | policy | Opus at lower effort untested |
| 8 | Script the coordinator: watchdog, dependency tracker, pre-allowed commands, no history rewriting, cost per file in the ledger | about $190 of coordinator wake-ups; the 5.8 h stall; 114 hand-written messages | not estimated | low |
| 9 | Step ranges and state names from layout labels (`steps_between "f_loop1" "f_after_g_1"`) | one failed run per wrong step count; 9 renumbering scripts | 1-2 days | loops stay manual |
| 10 | Faster slow leaves: restrict per-step rewriting; prove FULL once, derive CORRECT and SAFE | 7.5x seen once (2017 → 267 s); about half of a three-simulation file | hours per file | none |
| 11 | Split `common/mlkem_mldsa.ml` so ML-KEM skips ML-DSA material; compile the base once | loading it costs 3.4 h per gcc12_O2 run, compiling about 3 h; the split's share not measured | 1-3 days | none |
| 12 | Re-run callers only when a callee's exported theorems change | e.g. the 3491-s `keypair_k3` rerun | under 1 day after #3 | as #3 |
| 13 | Generate same-code ports, statement templates, polyvec glue | estimate: the 104 port files; 60 makes for 17 same-shape mono kernels | 1-2 weeks | interface changes stay manual |

**#2, the gate.** Partly done: `check_offsets.py` now also catches
`word_add (word pc) (word N)` and decimal GOT addresses, and the merge
script refuses any offset problem. But it runs only at merge time,
after the official make, and only on files in the build directory,
while the numerals of `KEM_GOT_TAC` and `INDCPA_GOT_TAC` were in
`arm/proofs/utils/`. Still to add: the SHA-256 of the committed `.ml`
in its `.correct` log (two logs did not belong to their files); no
`mk_thm` or `new_axiom` outside stubs; SAFE and FULL wherever gcc12_O2
has them; callee statements compared with the callees' current files.

**#3, the harness.** A full run records a digest of every theorem each
file proves, keyed by the digests of the file, its closure and the HOL
Light commit. A development run loads `base.ml` and the
utilities with the real `prove`, then the callee files with

```
prove (t,tac) = if cached t then mk_thm([],t) else real_prove (t,tac)
```

and checks that every extra axiom is a cache entry. Since the real
callee files are loaded, statements are exact, which ends stub drift (5
frame and 4 precondition mismatches in the mono stubs). A cache file can
be edited, so official logs must come from full runs (#4).

**#4, one process.** A generated driver `needs` all proof files of a
build in order, prints each file's specs, ends with `check_axioms ()`,
and its log is split into per-file `.correct` files.
Estimate with one process each for the `_k2`, `_k3`, `_k4` files and
the rest: gcc12_O2 7.9 CPU-hours and 2.5 h wall, gcc12_O3 22.0 and
6.1 h. Risk: 174 OCaml names are bound in more than one gcc12_O2 file,
so a file may pick up another file's tactic.

**#5, the facts generator.** The prototypes agree with the text. A
130-line stack-depth analysis of the `layout.ml` listings reproduces
all 105 frames stated in gcc12_O2. Every non-leaf SAFE read-only list in
gcc12_O3 (66) and clang17_O3 (41) names exactly the regions of its
callees' lists. A wrong fact cannot make a proof unsound, since HOL
rejects it. A frame larger than needed is sound but spreads: mono
`poly_rej_uniform_x4` copied 3312 from gcc12_O2 where 3296 suffices,
adding 16 bytes to 24 callers. Policy question: exact frames everywhere
(needed by mono's callers, valid for O2 too) or gcc12_O2 frames as upper
bounds. With layout names such as `mlkem512_check_pk_frame`, a
statement reads the same in every build, because names become numerals
at parse time.

**#7, routing.** Classify each function as same code, same up to
registers, different, or inlined. Haiku: same code with a done sibling,
behind the gate. Sonnet: different code with a same-build precedent.
Opus: first of a kind, critical path, or after a failed long make or 2 h
without a passing development run.

**Not recommended now: de-interleaving.** Proving inlined code through
relational Hoare logic (`ensures2`) took 5-10x the lines and 3-4x the
time of a direct proof in two experiments, and would need a new call
rule in `arm/proofs/equiv.ml` (61 of 103 fragmented calls cross a `bl`).

## 3. Not measured, open questions

- Per-file own times: estimated from wall times under load, until
  benchmarks.md replaces them.
- Whether one-process builds (#4) pass unchanged.
- Opus at effort `medium` or `high`: every Opus agent ran at `xhigh`.
- How much of `common/mlkem_mldsa.ml` ML-KEM needs.
- Per-tactic profiles of the slow leaves, e.g. gcc12_O3
  `keccakf1600_xor_bytes` (estimate: 4840 s own time).
- Untested: `ocamlopt.opt`; `Dynlink`ing compiled proof files into one
  process; DMTCP checkpoints (restore loses stdin on this host).

*Data:* agent transcripts (token counts at API list prices); the merge
ledger and `.correct` logs; the coordinator's log `STATUS.md`; agent
notes; diffs against gcc12_O2 at 19f9abc7; one closure profiled on one
pinned CPU.
