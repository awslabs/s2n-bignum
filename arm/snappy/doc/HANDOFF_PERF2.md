# HANDOFF: stream PERF-2 (faster slow proofs, statements unchanged)

Branch snappy-perf2 (from `snappy` at b51bb0ae). Results and tables:
PERF2.md (this directory).

## Method

- Baselines: each proof file standalone, one domain, S2N_TACTIC_TIMING=1,
  TIMED_TAC wrappers and a wrapper of `prove` that prints the time of each
  theorem (dev only, not committed). Peak memory: polled VmRSS.
- Dev drivers (not committed) were in arm/dev/perf2/ and /tmp/perf2.

## Done (committed)

1. RawUncompress(Source*, char*) and InternalUncompress<Validator>: before
   the call of DecompressAllTags, BSTEP_DROP_NUM_DISEQS_TAC and
   ~keep:(bstep_keep_not_bytes8_at `inp`) (array_writer.ml). The facts
   that cross a call are moved by orthogonality proofs whose arithmetic
   (NONOVERLAPPING_RULE) gets all numeric assumptions and splits every
   disequality. 3319 s -> 188 s, 519 s -> 190 s.
2. events.ml: snappy_ev_cur_asl per domain (a race in the link).
3. CompressFragment's segment files as spec/proof pairs (jobs): they were
   loaded serially before the link's jobs (~1100 s). snappy_arith_full is
   a par_local_ref.

4. loop5: cf2_arith_prove (relevant arithmetic facts first) in the model
   spec; SNAPPY_EVENTS_TAC at the leaves. 1721 s -> 510 s.
5. DecompressAllTags<SnappyArrayWriter>: T by tag class, 16 jobs.
6. DecompressBranchless: the near leaves as 3 jobs.
7. Name clashes between the libraries loaded at the link's top level
   (DAW_*/daw_*, daw_exec, db_exec, SNAPPY_CF1_TABLE_*). Link passed:
   1279 s (all jobs 975 s, seg4 the longest; ~304 s before the jobs).

8. seg4 by the match length (5 jobs, compress_fragment_seg4_lib.ml).
9. The slow lemmas of the branchless and DAT<SAW> libraries (LMO tables,
   DB_AND255_X) stated with assuming_proofs, proved in two lemma jobs.

Final link (e6d65204, 8 domains): passes, 156/156 contracts closed,
1018 s (all jobs 781 s; before the jobs 237 s), 1243 s with the build.
Tables in PERF2.md (this directory).

## Possible next steps (not done; gains now small)

- seg4d/seg4e (~410 s in the link) and loop5 (388 s) are the longest
  jobs; the link is throughput-bound on 8 domains (jobs sum to 6245 s).
- The loading before the jobs (~237 s) is mostly the base and the common
  snappy models (relative.ml 59 s, the needs of compress_fragment_lib 58 s).
- The peak memory of the final link (29.9 GB with 8 domains) vs 5.2 GB for
  link2 was not investigated.
- arm/dev/branchless/assemble.py no longer generates the branchless proof
  files (they were split by hand).

## Rules kept

- No statement changes; tactic state per domain (par_local_ref).
- Regenerate proofs.mk / link.ml with tools/native_proofs_mk.py and
  tools/native_link.py; link_costs.tsv with tools/link_costs.py from the
  link log.
