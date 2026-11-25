# COMPSAFE handoff (branch snappy-compsafe): memory safety of compression

Goal: `_SAFE` theorems (correctness + events) of the level-1 compression
path, `_CORRECT` statements unchanged. Design: arm/snappy/DESIGN.md 6.1.

STATUS (all proved, make <name>.correct passes; times are the running
times of the .correct files):
- CompressFragment: SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_IMAGE_SUBROUTINE_SAFE
  and _CORRECT (compress_fragment_proof, 1206 s; seg15 142 s, seg2 150 s,
  seg4 1055 s, seg6 135 s as separate targets).
- InternalCompress _SAFE + _CORRECT (both runs of the tactics in one file),
  208 s (dev run of the proof file).
- Compress(ctx) 75 s, RawCompress(ctx) 133 s, Compress(opts) 137 s,
  RawCompress(opts) 133 s, RawCompress 76 s, snappy_max_compressed_length
  63 s, snappy_compress 129 s, snappy_compress_with_level 133 s: _SAFE added,
  _CORRECT unchanged.
- Link regenerated with
    python3 ../tools/native_link.py snappy gcc12_O2 --open \
      compress_fragment_double_hash,raw_uncompress_sourcep_charp,\
      snappy_decompressor_decompress_all_tags_snappy_array_writer
  (and proofs.mk by native_proofs_mk.py); make snappy/gcc12_O2/link.correct
  passes (1392 s, S2N_PAR_DOMAINS=2): 85 contracts stated, 81 proved, 4
  open (CompressFragmentDoubleHash _CORRECT and _SAFE, RawUncompress(Source*,
  char*), DecompressAllTags<SnappyArrayWriter>). Every compression _SAFE and
  _CORRECT theorem above InternalCompress has exactly 1 open contract (the
  level-2 fragment compressor, stream COMP2); CompressFragment's have 0.

Next steps:
- _SAFE of the TOO_SMALL / INVALID_LEVEL theorems of the C functions (no
  memcpy hypothesis, only the 64-byte frame), if wanted.
- Make CompressFragment's proof cheaper in memory: the whole file peaked at
  about 29 GB (bstep's orthogonality arithmetic, CONTEXT_INT_ARITH, in seg4;
  the segment alone peaked at 0.7 GB): the cost depends on the order of the
  atoms of the decision procedure, i.e. on what ran before in the process.

Dev runs: arm/dev/cfs/ (untracked): run.sh NAME builds arm/dev/cfs/NAME.ml
natively and runs it from the repository root, log /tmp/compsafe/NAME.log;
dbg.ml has TR/SHOW/time_prove and a MATCH_MP_TAC that prints failures;
seg4.ml times SNAPPY_CF1_EV_TAC, SNAPPY_EV_FIRST_TAC and the checkpoints.

Pitfalls found:
- The events in bstep are terms that grow with every step and keep the
  branch conditions in the jumps; in CompressFragment's loop6 segment (seg4)
  the proof went past 48 GB before the first end of a path. Checkpoint the
  events after each block (SNAPPY_EV_CHECKPOINT_TAC).
- The decision procedure for linear arithmetic numbers the atoms by
  genvar, so the order of elimination, and its cost, depends on everything
  the proof did before: an ARITH_TAC with 38 facts that the _CORRECT proof
  of seg4 passed (8.8 GB peak for the whole segment) took more than 48 GB in
  the _SAFE run (found with eu-stack: camlHol_lib.addup under itlist).
  Later, in the whole proof (segments in one process), another such blowup
  (> 64 GB, terminated). Now the lib's SNAPPY_ARITH_TAC tries the relevant
  facts first (events.ml's staged SNAPPY_EV_ARITH_TAC; all facts last, but
  not in seg4: snappy_arith_full) and S4_SNAPPY_CONTR_TAC refutes a case
  with the facts relevant to its condition only; seg4 then peaked at 0.7 GB.
  bstep's orthogonality proofs (CONTEXT_INT_ARITH over all the component
  assumptions) can blow up the same way (seen once, in eu-stack).
- A callee instance rewritten after SPECL (NORMALIZE_RELATIVE_ADDRESS_CONV,
  GSYM WORD_ADD, ...) must get the events of the call afterwards (INST of a
  variable), else ARM_BSTEP_CALL_TAC cannot prove `read events s = e`.
- OCaml strings: a `/\` at the end of a line of a statement string must be
  written `/\\`, else `\` + newline is a line continuation.
- Str is not linked into the native proofs.
- memaccess_inset (sets) does not give memaccess_inbounds (lists): a callee
  in the set form forces the caller's statement into the set form.

Desired generic-tool changes (not made):
- bstep could keep the events abbreviated (as its constant-time runner does)
  for correct_safe proofs, instead of the checkpoint tactic of events.ml.
- A generic events tactic for the list form with symbolic offsets (the one of
  common/consttime.ml calls SIMPLE_ARITH_TAC with all facts and tries every
  region) would replace events.ml.

# T2 handoff (branch snappy-heapclient): compression with the heap

Statements in arm/proofs/snappy/gcc12_O2/ (CORRECT only; no _SAFE yet, since
InternalCompress has no _SAFE theorem to build on):

- compress_options: Compress(Source*, Sink*, CompressionOptions), with the
  WorkingMemory(size_t)/~WorkingMemory contracts and InternalCompress.
- raw_compress_options: RawCompress(..., CompressionOptions).
- raw_compress: RawCompress(const char*, size_t, char*, size_t*) (level 1).
- c_compress: snappy_compress, CORRECT (buffer large enough) and TOO_SMALL.
- c_compress_with_level: CORRECT (level 1/2, any upper bits of x2),
  INVALID_LEVEL, TOO_SMALL.

STATUS: all proved (make <name>_proof.correct passes): compress_options
133 s, raw_compress_options 132 s, raw_compress 76 s, c_compress 128 s,
c_compress_with_level 129 s. Link regenerated with
  python3 ../tools/native_link.py snappy gcc12_O2 --open \
    compress_fragment_double_hash,raw_uncompress_sourcep_charp,\
    snappy_decompressor_decompress_all_tags_snappy_array_writer
make snappy/gcc12_O2/link.correct passes (1397 s, 2 domains): 74 contracts
stated, 71 proved, 3 open (CompressFragmentDoubleHash, RawUncompress(Source*,
char*), DecompressAllTags<SnappyArrayWriter>). The T2 theorems with 0 open:
C_COMPRESS_TOO_SMALL, C_COMPRESS_WITH_LEVEL_TOO_SMALL, ..._INVALID_LEVEL;
with exactly 1 open (CompressFragmentDoubleHash, level 2, stream COMP2):
COMPRESS_OPTIONS, RAW_COMPRESS_OPTIONS, RAW_COMPRESS, C_COMPRESS,
C_COMPRESS_WITH_LEVEL (as InternalCompress itself).

Next steps:
- _SAFE versions: need a _SAFE theorem of InternalCompress (stream COMP);
  then the callee theorems used would be the _SAFE ones of
  WorkingMemory(size_t), ~WorkingMemory and Available, and the events
  combined with MEMACCESS_INSET_TAC (as in the heap clients).
- Compress(Source*, Sink*) (0x4994, a tail call with level 1) if wanted.

Pitfalls found:
- ARM_BSTEP_CONTRACT_TAC weakens the callee's stack regions only if the goal
  frame is a list of MAYCHANGE clauses: REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_
  PERMITTED_BY_ABI] after the ENSURES_MAYCHANGE_PRESERVED steps.
- Callee preconditions with objects at offsets of the caller's SP need
  NORMALIZE_RELATIVE_ADDRESS_CONV on the instance (the *_CONTRACT_TAC helper
  in each proof file), since bstep keeps facts in that form.
- The branches: BSTEP_SPLIT_PC_TAC, then the case closed by rewriting its
  condition with the state-free facts (*_KILL_TAC).

# DECOMP-B3 handoff (branch snappy-decomp3)

## Proved (make *.correct passes)
- snappy_uncompress: SNAPPY_C_UNCOMPRESS_GCC12_O2_IMAGE_SUBROUTINE_{SAFE,CORRECT}
  (c_uncompress_proof.ml, 78 s), relative to GetUncompressedLength (proved,
  DECOMP-A) and RawUncompress(const char*, ...).
- RawUncompress(const char*, size_t, char*):
  SNAPPY_RAW_UNCOMPRESS_CHARP_ULONG_CHARP_..._{SAFE,CORRECT} (84 s), relative
  to RawUncompress(Source*, char*).

## In progress
- RawUncompress(Source*, char*): proof file
  arm/proofs/snappy/gcc12_O2/raw_uncompress_sourcep_charp_proof.ml (copy in
  arm/dev/raw_uncompress_sourcep_charp_proof.ml.wip; NOT committed in the
  proof dir until it passes). Dev version (goal stack, debug prints):
  dev/ru3.ml in the worktree root (untracked). Cases L = 0..4 pass in the
  dev run; case L >= 5 was running (the DecompressAllTags call is slow).
  When it passes: move it in, regenerate proofs.mk and
  `native_link.py snappy gcc12_O2 --open snappy_decompressor_decompress_all_tags_snappy_array_writer`.
  Then the link (relative_close_open) leaves only the DecompressAllTags
  contract open (and, transitively when DAT is proved, DecompressBranchless).

## Not started (stated only)
- DecompressAllTags<SnappyArrayWriter>
  (snappy_decompressor_decompress_all_tags_snappy_array_writer_spec.ml).
  Plan in DESIGN.md 7e (cut points E/L/T, buffer/scratch states, measure,
  frame idempotence problem and the footprint-union plan); exploration in
  dev/dat1.ml (untracked). Lemmas: common/snappy/snappy_slow_path.ml,
  arm/proofs/snappy/array_writer.ml. Its fast path needs
  DecompressBranchless<char*> (statement by DECOMP-B2, being proved by
  BRANCHLESS) -- only as a contract, so DAT does not wait for it.

## Pitfalls (see DESIGN.md 7e)
- goal stack: use `refine(by tac)`, not `e` (VALID fails with assume_spec).
- never ASM_ARITH_TAC / MESON over the bstep state (hangs); never use `o`
  as a HOL variable name; term_match patterns: free vars are matchable.
- bstep frame clauses on the stack must use the same address base as the
  stores; callee-saved registers of callees (X27/X28) must be in frames.
