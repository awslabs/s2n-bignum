# Reflections on the snappy verification

What went well, what went wrong, how it was fixed, and what to carry into the
next library. Written at the end of the project (2026-11-25), from the
coordinator's record and the agents' notes (DESIGN.md, FINDINGS.md, the
HANDOFF and PERF files, now in doc/, and the commit messages).

## 1. The shape of the work

- **Scope.** snappy 1.3.1, gcc 12.4 -O2, AArch64: about 9,300 instructions in
  the image. Every C entry point is proved functionally correct and memory
  safe. Compression is proved byte-for-byte against a HOL model of the
  algorithm, with the round trip and length bound proved on top.
  Decompression and validation are proved against a HOL model of the format,
  for any input.
- **Method.**
  - One spec/proof pair per function, proved relative to its callees'
    contracts (`common/relative.ml`), and a generated link file that closes
    them all.
  - bstep symbolic execution for straight-line code.
  - Cut points with a decreasing measure (`ENSURES_MEASURE_INDUCT`) for loops
    and irregular control flow.
- **Organisation.**
  - Up to 5 agents at a time, each in its own git worktree and branch.
  - The coordinator merged a branch into `snappy` only after its link
    passed, and moved generic material to `snappy-generic`, a prefix of
    `snappy`.
  - 25+ agent instances over about 40 hours.
  - Recurring cycle: specification, infrastructure, leaf functions, then the
    hard loops.

What worked:
- **Contract-based decomposition.** Agents worked in parallel, and a stated
  contract let callers be proved before their callees.
- **Specifying first and testing the specs differentially** against the real
  binary. This caught a wrong hash in the level-2 model before any proof
  depended on it.
- **Investing early in generic infrastructure:** relocations, C library
  contracts, the heap model, bstep fixes.

## 2. Specification errors are found late, by the proofs

About ten statements had to be corrected after proofs of their callers
existed. Every one was about address arithmetic or calling conventions,
never about the algorithm:

- **No-wraparound bounds:**
  - `val out + m + 64 < 2^64`;
  - IncrementalCopy's `op + 64`;
  - the compressor input margin `+ 65536`;
  - decompression input length `< 2^63`;
  - the validator's `< 2^58`.

  Compiled code computes `p + k` and compares it unsigned, so it misbehaves
  when that sum wraps.
- **Alignment:** `aligned 16 sp`, `aligned 8 d`.
- **Buffer sizes:** the fragment output region had to shrink by 5 bytes,
  for the length header written into the same buffer first.
- **Frames:** callee-saved registers saved by callees (X27/X28); objects
  split into separate frame clauses.
- **Load order:** a constant parsed as a free variable when a file was
  loaded first, which made the statement unprovable.

Each fix forced re-proofs of all callers.

Carry over:
- **Start every contract with a standard hypothesis set:** no-wraparound
  for every buffer plus a margin of 64 bytes or so; stack and object
  alignment; all callee-saved registers as ghosts; objects split into
  per-field frame clauses.
- **Prove each function's statement on the fast path first,** before
  callers rely on it. Most of these errors would have shown up there.

## 3. Where the CPU went, and why it took hours

The validator's `DecompressAllTags`, 193 instructions, ran serially for more
than 3.5 hours and never finished. Instrumentation (`common/tactic_timing.ml`)
showed:
- about 90% of the CPU went to arithmetic decision calls;
- about 1% went to symbolic execution;
- the model step took 0.1 s.

Every arithmetic call received all the facts in the proof state, and
`ARITH_TAC` case-splits on every disjunction and disequality among them.
Undecidable branch conditions cost four failing attempts each, and the
"all facts" fallback succeeded 0 times in 316 tries.

Two fixes:
1. **`common/arith_facts.ml`** keeps only arithmetic facts that share atoms
   with the goal, transitively. Classes got 7–16× faster (one went from
   1,781 s to 116 s).
2. **Splitting the proof into 14 per-class pieces** run in parallel.

Wall time went from more than 3.5 hours to about 6 minutes.

The same cause produced the memory blow-ups:
- A seg4 run reached 174 GB, most likely what crashed the machine.
- MESON over the bstep state hung for 40 minutes.
- A history-dependent ARITH went past 48 GB on facts it had handled in
  another run.

Carry over:
- Never give arithmetic or MESON the whole state. Use the relevant-facts
  filter by default.
- Measure before optimising. The intuitive candidates (sharing symbolic
  prefixes, fewer case splits) would have saved 1–2%.
- Design big proofs as independent pieces from the start. Serial
  multi-hour runs are both slow and uninformative: a failure after 2 hours
  said only `Failure("DAT_MODEL_TAC")`.
- Make every proof file print where it is, so a failure is locatable.

## 4. Tooling and engine gaps

Hit and fixed along the way, now generic:
- **bstep:**
  - ADRP pages (alignment facts about the code base);
  - calls and tail calls after a block;
  - frames given by name;
  - footprint frames, and idempotent frames for measure induction
    (footprint union lemmas).
- **Contract application** (`ARM_BSTEP_CONTRACT_TAC`):
  - it needs the goal's frame expanded and callee clauses with a single
    region;
  - it weakens into the first containing clause, losing facts about the
    rest of an object;
  - it needs normalized nested stack addresses.

  Worked around per proof; a generic fix is still owed.
- **Address normal forms:** a store is absorbed only by a clause with the
  same base, and facts at computed addresses are lost at stores.
- **Event terms** grow with every step and needed checkpointing
  (`SNAPPY_EV_CHECKPOINT_TAC`); bstep should keep them abbreviated.
- **Parallel domains:** proof-tool state was global, which caused spurious
  frame and alignment failures on 8 domains. Fixed with
  `par_local`/`par_once`/`par_counter`.
- **Goal stack:** `e` rejects tactics that use assumed contracts (VALID);
  use `refine (by tac)`.
- **Pieces that pass alone but fail in the link.** After the split, the
  final link failed in 4 validator copy-class pieces that passed as
  standalone proofs. Their tactics kept per-proof state in plain global
  refs (`dat_copy_rws`, `dat_subs`, `dat_eq_facts`), and pieces running
  at the same time on several domains overwrote each other's state. Fixed
  by making the state `par_local_ref` (validator branch a0f44b92). The
  pieces were also scheduled last in the link; `link_costs.tsv` now
  starts the long jobs first. Lesson: any new tactic state must follow the
  rules in the `common/par_domains.ml` header, and a piece is only proved
  once it has passed inside the parallel link.

## 5. Process: what went wrong, how it was handled

- **Machine crash.** Under 9 agents and many HOL processes, a 174 GB proof
  process most likely crashed the machine. Recovery:
  - backed up the uncommitted work;
  - resumed the agents;
  - added a watchdog that kills any proof process above 64 GB;
  - capped HOL processes per agent;
  - ran development runs under `systemd-run -p MemoryMax=48G`.
- **Agent context limits.** The hardest functions went through 4–8
  successive agents. Committed `HANDOFF.md` files and coordinator WIP
  snapshots made this survivable. Earlier hand-offs lost scratch notes kept
  in `/tmp`.
- **Stalls.**
  - An agent spent 3 hours in a long-lived toplevel fed through
    `tail -f`.
  - Waiters used `pgrep -f` patterns that matched themselves and never
    exited.
  - Agents waited on runs that had already died.

  Each had to be detected by checking file activity.
- **Duplicated work.**
  - Three agents independently fixed the same `native_link.py` problem.
  - Lemmas were duplicated across branches.
  - Cherry-picks re-applied the same commits with different hashes, so
    merges conflicted.
  - The generated `link.ml`/`proofs.mk` conflicted on every merge.
- **Overclaiming.**
  - Class-restricted runs that ended in "Unsolved goals" were reported as
    "the class closed".
  - A link that "passes" on one branch was not checked against the others.

  Only a full run counts.
- **Over the cap.** Agents spawned nested agents and went over the
  5-agent cap until told not to.
- **Classifier stop.** An API safety classifier stopped two sub-agents on
  `FindMatchLength`/loop5 as "[cyber]". After the user approved, a retry
  went through.
- **Waiting instead of acting.** The coordinator waited on multi-hour
  serial runs before questioning them. The user's push to profile is what
  found the 90%-arithmetic cause.

Carry over:
- **Hard limits from the start:** memory watchdog, per-process memory cap,
  process and waiter budgets, no long-lived piped toplevels.
- **Generic tools are owned by one place** (`snappy-generic`). Agents
  propose changes; the coordinator lands them once.
- **Generate `link.ml`/`proofs.mk` only on the integration branch,** never
  commit them on stream branches.
- **Define "proved" as "full proof file passes",** and have restricted runs
  print the goals they leave.
- **Use the HOL Light MCP server** for interactive work: checkpoint restore
  in about 2 s, and single-goal inspection instead of rebuild-and-read. Set
  it up before starting, not at the end.
- **Time-box any proof run above about 30 minutes:** profile and split
  before waiting.

## 6. Findings about snappy

No functional or memory-safety bug was found. The proofs and differential
tests did surface edge cases (`common/snappy/FINDINGS.md`):
- the validator's fast-path off-by-one, which falls back harmlessly (F1);
- the validator fast path's reliance on a 64-bit counter not wrapping (F2);
- undefined behaviour for compression levels other than 1 and 2 in the
  C++ API (F8);
- search pointers computed past the end of the input (F10);
- pointer comparisons that break near the top of the address space;
- 32 bytes of an uninitialised stack buffer copied into output slack;
- prefetches past the end of buffers.

## 7. Infrastructure to carry over

All of it is on `snappy-generic`; `doc/external_interfaces.md` explains the
interface modelling.

- **Loaded images:** relocated slots (`common/elf_image.ml`,
  `tools/elf_relocs.py`), image tools (`common/loaded_image.ml`), and the
  ELF layout and transcription tools (`tools/elf_*.py`).
- **External functions:** C library contracts in three strengths
  (`common/libc_contracts.ml`, `arm/proofs/libc.ml`) and PLT call tactics.
- **Heap:** the abstract allocator with a slab-allocator witness
  (`common/heap.ml`, `common/footprint.ml`, `arm/proofs/heap*.ml`,
  `arm/heap/`).
- **Proof structure:** `common/relative.ml` with explicit open contracts;
  `tools/native_link.py --open`; `ENSURES_MEASURE_INDUCT`.
- **Performance:** `common/arith_facts.ml` and `common/tactic_timing.ml`.
- **Engine:** bstep improvements (ADRP, calls, named frames), and
  domain-safe proof-tool state (`common/par*.ml`).
- **Instruction models:** RBIT, PRFM/PRFUM, BLR, LDUR/STUR of B/H registers.
- **Environment:** the pinned toolchain (`hol-env.sh`) and the MCP setup
  (`hol-mcp-server.sh`, `holmcp.py`).

Not yet generic but worth promoting:
- the decide-by-arithmetic and run tactics;
- the event checkpointing;
- the contract-call frame normalisation now duplicated across
  snappy proof files.
