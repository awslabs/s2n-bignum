# Where the proof-check time goes, and how to cut it

Checking a build means compiling and running every `_proof.ml` file
(each proves its functions relative to its callees' contracts) and then
running the build's `link.ml`, which proves everything again in one
process and discharges the contracts. This note says where the CPU time
of that check goes, what each prototype speed-up measured, and what is
still missing for a 5-10x gain.

All measurements were taken on 2026-11-08 on a 64-CPU Graviton3
(Neoverse V1), at `mlkem-arm` 13f9d7b1. They are CPU seconds
(user+sys) with one process per pinned CPU, unless marked as wall
time. The detailed agent reports and raw data are in
`~/claude-scratch/perf/*.md` and `runtimes_*.tsv`, and the code is on
the `perf-*` branches listed at the end.

## 1. The status quo

A full check of the four builds costs 94 CPU-h:

| build | full check | per-file runs | link run | compile |
|---|--:|--:|--:|--:|
| gcc12_O2 | 22.4 h | 12.9 h (58%) | 4.8 h (22%) | 4.7 h (21%) |
| gcc12_O2_mono | 17.6 h | 9.7 h (55%) | 4.6 h (26%) | 3.3 h (19%) |
| gcc12_O3 | 32.3 h | 18.8 h (58%) | 9.1 h (28%) | 4.3 h (13%) |
| clang17_O3 | 21.8 h | 12.3 h (56%) | 7.7 h (35%) | 1.9 h (9%) |

- **Per-file runs are mostly loading.** Every process first spends
  206-221 s starting HOL Light and proving the shared files again. The
  median file then adds 6-22 s of spec loading and 42-75 s of its own
  proofs. Over all per-file runs, 36-55% of the CPU goes to that
  repeated start and shared work. The largest single item is
  `common/mlkem_mldsa.ml` (10-15% of each build). About 100 s of each
  load is ML-DSA and AVX2 lemmas that no ARM ML-KEM proof uses.
- **The link** is 96-98% the proofs themselves. It is one process, so
  it is also the longest wall-clock step: 4.6-9.1 h.
- **Compiling** each proof file with `ocamlopt.byte` takes 72-384 s.

Inside the proofs, a sampling profile and per-tactic timers found:

- **OCaml's polymorphic `=` is the hottest operation.** It is at the
  leaf of 39-96% of samples. It has no shortcut for physically equal
  arguments, so it walks shared term DAGs as if they were trees.
  `CHANGED_TAC` compares goals this way. In clang17_O3
  `poly_frombytes` that comparison is 86% of the run.
- **Calls cost about 5 s each.** `GEN_BIGSTEP_TAC` rewrites an
  unreduced nest of 58 beta-redexes, and its `GEN_TAC` justifications
  alpha-convert the whole goal once per primed variable. Together this
  is 26% of gcc12_O2 `indcpa_enc_k4`.
- **SAFE proofs cost about twice as much as CORRECT proofs.** 30-40% of
  a SAFE proof is justification time: `CLARIFY_TAC` instantiates all
  remaining assumptions at each split.
- **Quotations are parsed inside predicates.** In gcc12_O3
  `keccakf1600_xor_bytes`, `(m * n + p) DIV m` is parsed 570,843
  times, which makes the file take 4,913 s.

## 2. All prototypes together, measured on gcc12_O2_mono

The configurations, with all 64 `_proof` files at 15 jobs on CPUs
33-47:

- **a** (baseline): `mlkem-arm`.
- **b** (stacked): adds the source changes of sections 3.3 and 3.4, a
  HOL Light built with `--disable-naked-pointers` and the `compare`
  and BDD patches, and compiles with `ocamlopt.opt`.
- **c**: b plus the fork server.

| | full mono check, CPU | wall | re-check `keypair_derand_k2` | re-check `indcpa_enc_k4` |
|---|--:|--:|--:|--:|
| a | 46,721 s | 3,543 s | 809 s | 2,719 s |
| b | 20,419 s | 1,489 s | 307 s | 1,220 s |
| c | 9,934 s | 1,376 s | 289 s | 1,256 s |
| a / c | **4.7x** | 2.6x | 2.8x | 2.2x |

- **All runs pass.** The logs print the same theorems, and the
  statement digests of all mono spec files are equal, apart from four
  unused AVX2 lemmas that moved to another file.
- **Wall time is set by the longest file, not by the CPU spent.** In c,
  `indcpa_enc_k4` spends 1,085 s on its own proofs, after 114 s of
  shared loading.
- **The link is the next limit.** The stacked link takes 8,550 s,
  pinned on one CPU. The only baseline link times are unpinned runs
  under load (16,326 s and 16,139 s, wall). The 1.9x between them is
  indicative only.
- **Including the link changes the picture.** With it, a full mono
  check falls from about 63,000 to about 18,600 CPU s (3.4x), using
  the unpinned baseline link time. Its
  wall time is the link's, so it improves only by that same rough
  1.9x.

## 3. The changes one by one

"Trust" says what a change relies on beyond the HOL Light kernel. None
of them adds an axiom, uses `mk_thm` or imports a theorem.

### 3.1 HOL Light and OCaml (reusable by every HOL Light user)

| change | effect | trust |
|---|---|---|
| OCaml 4.14 with `--disable-naked-pointers` | -15 to -30% per proof; whole mono run -19% CPU | none; no source change |
| `compare x y = 0` instead of `=` in `equals_thm`, `equals_goal` and `INSTANTIATE` | clang17_O3 `poly_frombytes` 4,934 -> 495 s; large proofs -4 to -12%; mono -6.5% CPU, -18% wall | none; on terms the two agree on every input, and the kernel module `Hol` is unchanged |
| one-pass acyclicity check in `BDD_DEFTAUT` | -13 to -102 s per proof | none |
| all three | mono -27.8% CPU, -33.5% wall | |
| `ocamlopt.opt` instead of `ocamlopt.byte` | mono compile 11,568 -> 3,360 s | none |

The patches are in `tools/perf/hol-light/` on `perf-holcore`. Each
commit message argues why the change is equivalent.

### 3.2 Process structure (reusable by every s2n-bignum proof)

- **Fork server** (`tools/forkserver/`, `perf-forkserver`).
  - **How it works:** it splits the inlined source of every proof file
    at its `needs` boundaries, loads each shared prefix once, and forks
    a child for each continuation. It needs no compile.
  - **Effect:** whole mono run 46,000 -> 20,131 CPU s on the old HOL
    Light. Stacked, b -> c is a further 2.1x in CPU.
  - **Trust:** each log is printed by the process whose kernel proved
    it.
  - **Not done:** a port to OCaml 5.5.2.
- **Persistent server** (`perf-server`). It keeps the forked prefixes
  resident between checks.
  - **Effect:** a one-line edit of a proof file re-checks in 7 s
    (`poly_reduce`, against 291 s with `make`) and 71 s
    (`keypair_derand_k2`, against 850 s). After an edit to a callee
    spec, a re-check takes 8-201 s.
  - **Memory:** about 0.5 GB per resident node, or an estimated
    38-52 GB for a whole build.
  - **Not done:** it does not cover `link.ml`.
- **Content-addressed result cache** (`tools/proof-cache/`,
  `perf-cache`).
  - **Key:** one SHA-256 over every file `inline_load.ml` inlines, the
    `.o` files, the HOL Light build and the compiler.
  - **Correctness:** 25 invalidation experiments with no wrong hit or
    wrong miss.
  - **Effect:** replayed over the 20 newest proof commits, per-file
    runs fall from 1,351 to 103 CPU-h (-92%). Counting the links of the
    affected builds, the total falls from 1,883 to 301 CPU-h, and 198 of
    the 301 are the link.
  - **Trust:** a hit means that some writer recorded a passing run of
    the same inputs, so the store must be writable only by main-branch
    CI or be signed. The final theorems never come from the cache,
    because the link re-proves everything.

### 3.3 Shared symbolic-execution tactics (`common/`, `arm/proofs/`)

| change | branch | effect |
|---|---|---|
| beta-reduce before `GEN_BIGSTEP_TAC`'s rewrite; one `GENL` + `ALPHA` | `perf-simtac` | `indcpa_enc_k4` -24.6% |
| linear `CLARIFY_TAC` justification | `perf-simtac` | `gen_matrix_k4` -17.7% |
| the three simtac changes together | `perf-simtac` | `indcpa_enc_k4` 1,787 -> 1,115 s; `gen_matrix_k4` 1,131 -> 761 s; mono `dec_k4` 1,173 -> 917 s |
| forward simulation of basic blocks (`ARM_FWD_STEPS_TAC`) | `perf-forward` | Keccak loop simulation 23.7 -> 6.9 s; no gain on `indcpa_enc_k4` |
| checkpoints inside `ARM_STEPS_TAC` | `perf-forward` | SAFE `keccakf1600_permute` 353 -> 157 s; `gen_matrix_k4` 615 -> 391 s; `indcpa_enc_k4` 991 -> 800 s |
| derive CORRECT and SAFE from FULL (`ENSURES_FROM_FULL_TAC`) | `perf-forward` | `keccakf1600_permute` file 704 -> 280 s |

These are shared with the x86 and RISC-V proofs. The simtac changes
passed a check-mode build in which all 1,888 big steps of mono gave
the old goals. The forward changes have not yet been checked against
the whole repository. Upstream `main` has since changed `CLARIFY_TAC`
as well (#487), so that change has to be reconciled.

### 3.4 Loading of the mlkem files (`perf-specload`)

- **Lazy lemmas:** the ML-DSA lemmas are proved only when used, and
  the AVX2 lemmas move to their own file.
- **Lazy work at load time:** callees are decoded only when a proof
  steps through them. Callee safety tactics are built when first run.
- **Cheaper definitions:** the 16-way case lemmas use
  `EXPAND_CASES_CONV` instead of `ARITH_RULE`, and 56 quotations are
  hoisted out of predicates.
- **Effect:** loading 180-550 -> 90-240 s per file; whole runs -33 to
  -50%; gcc12_O3 `keccakf1600_xor_bytes` 4,913 -> 247 s. The estimated
  saving over all builds is 16 CPU-h.
- **What is left:** a floor of about 91 s per process, of which
  `instruction.ml`, `decode.ml` and `words.ml` take 45 s.

## 4. What a 5-10x gain still needs

The target is reached for CPU per full set of per-file runs (4.7x) and
for the edit-and-recheck loop on small and medium files (6-40x with
the server). Two limits remain:

1. **The link.** It re-proves everything in one process, so after the
   cache it dominates both CPU and wall time: gcc12_O3 alone takes 9.1
   CPU-h serially. The options, none of them measured:
   - Run the link only on main-branch CI, and gate commits on the
     cached per-file runs.
   - Link per top-level family (k2, k3, k4) in parallel. This spends
     more CPU but cuts wall time to the largest closure.
   - Speed up the proofs inside the link with point 2, which acts on
     them directly.
2. **The own proofs of large files**, for example the 1,085 s of
   `indcpa_enc_k4` in configuration c. Calls cannot be checkpointed,
   and a callee's CORRECT and SAFE contracts cannot be combined. One
   simulation per function therefore needs FULL contracts, proved
   bottom-up for every callee and with CORRECT and SAFE derived from
   them (2.5x where measured). That is a proof rewrite, not
   infrastructure. Forward simulation (3.4x on straight-line code)
   helps the leaves.

**Not done:**
- measurements on the other builds;
- the fork server on OCaml 5.5.2;
- a baseline link measured under the same conditions;
- the x86 and RISC-V regression for the shared tactic changes;
- upstreaming the HOL Light patches.

## Branches

All branches start from `mlkem-arm` 13f9d7b1 and are local, not pushed.

| branch | contents |
|---|---|
| `perf-breakdown` | instrumented builds, per-phrase CPU model |
| `perf-profile` | tactic timers, stack sampling; xor_bytes quotation fix |
| `perf-holcore` | HOL Light build recipe, the `compare` and BDD patches |
| `perf-specload` | the loading changes of 3.4 |
| `perf-simtac` | the three tactic changes of 3.3 |
| `perf-forward` | forward simulation, checkpoints, `ENSURES_FROM_FULL_TAC` |
| `perf-forkserver` | fork server |
| `perf-server` | persistent server (on `perf-forkserver`) |
| `perf-cache` | content-addressed result cache |
| `perf-stack` | specload + simtac + forkserver + holcore, `ocamlopt.opt` |
