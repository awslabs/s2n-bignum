# COMP2 handoff (CompressFragmentDoubleHash, level 2)

## State

Proved and committed: init, loop1, loop2, join4, loop4, join5, join2 (+SAFE),
composition. Open: the five FML contracts
(compress_fragment_double_hash_fml_spec.ml) and loop5
(compress_fragment_double_hash_loop5_spec.ml).

## FML work (in progress)

Scratch: arm/scratch_comp2/fml/ (run.sh NAME builds NAME.ml and runs it from
the repository root; output NAME.out; grep "== \|SCRATCH FAILED").
- fml_lib.ml: lemmas (SNAPPY_MATCH_LENGTH_NE8 proved) and tactics
  (FML_READ*_TAC, FML_CANON_TAC "Xn" t, FML_BRANCH_TAC, FML_KNOWN_BRANCH_TAC,
  FML_CALL_TAC th [value,"var"] "sN", FML_IH_TAC, FML_FIN_TAC, FML_CTZ_TAC).
- fml_a.ml: FML A as BYTE (byte loop, WF_INDUCT_TAC + call of the IH),
  TAIL, LOOP (8-byte loop), main.

Plan: each copy X in {A,B,C,D,E} as BYTE/TAIL/LOOP/MAIN lemmas with the
spec's frame; sub-lemma pre/post in the spec's events form. Then
compress_fragment_double_hash_fml_proof.ml with all five.

Code map (offsets from the function at 0x3ae0 = 15072): see the comments
in fml_a.ml and the layout (arm/proofs/snappy/gcc12_O2/layout.ml).

## Status

- DONE: FML A-E (compress_fragment_double_hash_fml_proof.ml, 137 s).
- DONE: loop5 (compress_fragment_double_hash_loop5_proof.ml, 1721 s,
  make ...loop5_proof.correct passes). Assembled from the scratch files by
  arm/scratch_comp2/fml/mk_loop5.py (fml_lib words and tactics, l5_lib,
  l5_emit, l5_tac, l5_piece).
- DONE: link (make snappy/gcc12_O2/link.correct, S2N_PAR_DOMAINS=2,
  2826 s): 81 contracts stated, 79 proved, 2 open (the allowed opens of
  other streams: RawUncompress(Source*, char*) SAFE and the decompressor's
  DecompressAllTags SAFE). SNAPPY_COMPRESS_FRAGMENT_DOUBLE_HASH_GCC12_O2_
  IMAGE_SUBROUTINE_{CORRECT,SAFE}, InternalCompress, Compress(ctx) and
  RawCompress(ctx) are closed with 0 open contracts.
- Link: generated with
  --open compress_fragment_double_hash_model,raw_uncompress_sourcep_charp,
         snappy_decompressor_decompress_all_tags_snappy_array_writer
  (the model spec has no contracts; the other two are other streams').
- Pitfalls found: `ip + x - k` parses as ip + (x - k), write (ip + x) - k;
  facts at computed addresses (x1 - k) are lost at a store, re-derive them
  just before each load; SNAPPY_TB_TAC (ASM_ARITH_TAC over the whole state)
  blew up to 18 GB, replaced by CF2_L5A_TBUPD_TAC; assume_spec contracts
  make `e` report "Invalid tactic" (load the proved FML file to debug).

## FML work (in progress)

Scratch: arm/scratch_comp2/fml/ (run.sh NAME builds NAME.ml and runs it from
the repository root; output NAME.out; grep "== \|SCRATCH FAILED").
- fml_lib.ml: lemmas (SNAPPY_MATCH_LENGTH_NE8 proved) and tactics
  (FML_READ*_TAC, FML_CANON_TAC "Xn" t, FML_BRANCH_TAC, FML_KNOWN_BRANCH_TAC,
  FML_CALL_TAC th [value,"var"] "sN", FML_IH_TAC, FML_FIN_TAC, FML_CTZ_TAC).
- fml_a.ml: FML A as BYTE (byte loop, WF_INDUCT_TAC + call of the IH),
  TAIL, LOOP (8-byte loop), main.

Plan: each copy X in {A,B,C,D,E} as BYTE/TAIL/LOOP/MAIN lemmas with the
spec's frame; sub-lemma pre/post in the spec's events form. Then
compress_fragment_double_hash_fml_proof.ml with all five.

Code map (offsets from the function at 0x3ae0 = 15072): see the comments
in fml_a.ml and the layout (arm/proofs/snappy/gcc12_O2/layout.ml).

## Status

- DONE: FML A-E proved (compress_fragment_double_hash_fml_proof.ml,
  137 s; generated from arm/scratch_comp2/fml/fml_{lib,gen,bde,c}.ml).
- Merged branch snappy (tools, comp1's lemmas in snappy_words.ml).
- loop5: EmitCopy proved in scratch (L5_J15/J7/J6/LOOP10/EMIT, f9.ml
  runs l5_emit.ml in 133 s). The piece (l5_piece.ml, debug l5_pdbg.ml via
  f8.ml) in progress. Assemble the proof file with mk_loop5.py.
- (older notes) loop5: Scratch files arm/scratch_comp2/fml/:
  l5_lib.ml (EmitCopy tags as numbers, EC_REPS, bytes of 32-bit stores),
  l5_emit.ml (L5_J15/J7/J6 tag lemmas, L5_LOOP10, L5_EMIT loop5..join12;
  frame bytes(op,mx), pre bytes(op,P) = v, post bytes(op,P + LENGTH ec)),
  l5_tac.ml (tactics of the loop2 and join5 proofs, renamed CF2_L5A_ and
  CF2_L5B_), l5_piece.ml + l5_pdbg.ml (the piece, being written; f8.ml).
- Piece plan (join12 at +0x368): cmp x10,x1 -> join2 (phase 5); else
  table2 updates at ip'-7, ip'-4 (if ip' > 7, signed b.le), ip'-3, ip'-2,
  table at ip'-2, ip'-1, then table2 entry e2 at ip' (c2) -> FML E if
  Load32 equal, else table entry e1 (c1) -> loop1 (phase 1) or FML D;
  join18 (+0x5fc) w4 += 4, x8 = x1, loop5 (phase 4).
- Debug run style: E "name" tac steps in a g/e script (see l5_pdbg.ml).
