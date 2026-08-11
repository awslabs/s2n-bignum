(* ========================================================================= *)
(* Shared BINARY-INDEPENDENT proof machinery for the AES-GCM decrypt proofs. *)
(*                                                                            *)
(* Used by BOTH decrypt binaries:                                             *)
(*   - aesv8_gcm_8x_dec_256.o    (masked band chain: core -> le1..le8block)   *)
(*   - aesv8_gcm_8x_dec_256_wb.o (whole-blocks variant: wb)                   *)
(* so that each proof chain loads ONLY its own binary.                        *)
(*                                                                            *)
(* Contents (formerly the tail of aesv8_gcm_8x_dec_256_core.ml; provenance    *)
(* notes retained in place):                                                  *)
(*   - the GHASH/Karatsuba bridge lemma layer (KARATSUBA_LIMBS,               *)
(*     GHASH_1BLOCK_CORRECT, GMULT_REDUCE_PROP3, GMULT_FULL_CORRECT_BA, ...); *)
(*   - the SIMD-fold stepping layer (GCM_SIMD_SIMPLIFY_TAC, the per-step-     *)
(*     discard steppers, ARM_VSTEPS_FOLD_TAC, ...);                           *)
(*   - the bridge-close helpers (PMUL_CONG_128, ABBREV_INNER_PMULS_TAC,       *)
(*     QQ0SPLIT, JOINMID, FINISH_WV_REDUCE_TAC, ...);                         *)
(*   - the N-block bridge infra (JOIN_EQ_SPLIT, SUBW_* lane lemmas,           *)
(*     MERGE_2BLK_TAC, mk_discard2, GMULT2_FULL_CORRECT_BA,                   *)
(*     DEC_2BLK_GMULT2_BRIDGE_TAC, LANE_CLOSE_TAC).                           *)
(* No machine code is defined here.  No CHEAT_TAC, no new axioms.             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/aes.ml";;
needs "arm/proofs/utils/aes.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;
needs "common/karatsuba_pmul.ml";;
needs "common/polyval_ghash.ml";;
needs "common/ghash_nblock_karatsuba.ml";;
needs "common/gmult_nblock_lemmas.ml";;
needs "arm/proofs/utils/gcm_ctr_helpers.ml";;
needs "arm/proofs/utils/aes_ctr_spec.ml";;

(* ========================================================================= *)
(* SECTION 1: GENERIC GCM MACHINERY (direction-agnostic).                     *)
(*                                                                            *)
(* Nothing below this banner (until the DECRYPT-SPECIFIC section at the end)  *)
(* is decrypt-specific: it is word/SIMD algebra, the GHASH/Karatsuba bridge   *)
(* layer, exec-parameterized steppers, and N-block byteform merge/close       *)
(* tactics equally valid for the ENCRYPT binaries.  The enc proof files       *)
(* (aesv8_gcm_8x_enc_256_*.ml) currently carry their own private copies of    *)
(* much of this (REV64_*, KARATSUBA_LIMBS, GCM_SIMD_SIMPLIFY_TAC, QQ0SPLIT,   *)
(* MERGE_2BLK_TAC, ...); pointing them here and deleting the copies is a      *)
(* planned cleanup (needs enc re-verification).                               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* SIMD REV64 fold-back lemmas (ported from Mila's gcm_gmult_v8_spec.ml,     *)
(* branch mila-gcm_gmult_proof).  The ARM simulator expands REV64.16B into a *)
(* 4-level nested word_join/word_subword byte tree (128->64->32->16->8).     *)
(* These collapse it back to word_reversefields 8 the instant it appears, so *)
(* the giant (~145k char) term never forms and the final closure is fast.    *)
(* ------------------------------------------------------------------------- *)

let REV64_LOWER_LANE = prove(
  `!(xi:(128)word).
    word_join
      (word_join (word_join (word_subword xi (0,8):(8)word) (word_subword xi (8,8):(8)word):(16)word)
                 (word_join (word_subword xi (16,8):(8)word) (word_subword xi (24,8):(8)word):(16)word):(32)word)
      (word_join (word_join (word_subword xi (32,8):(8)word) (word_subword xi (40,8):(8)word):(16)word)
                 (word_join (word_subword xi (48,8):(8)word) (word_subword xi (56,8):(8)word):(16)word):(32)word):(64)word =
    word_reversefields 8 (word_subword xi (0,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

let REV64_UPPER_LANE = prove(
  `!(xi:(128)word).
    word_join
      (word_join (word_join (word_subword xi (64,8):(8)word) (word_subword xi (72,8):(8)word):(16)word)
                 (word_join (word_subword xi (80,8):(8)word) (word_subword xi (88,8):(8)word):(16)word):(32)word)
      (word_join (word_join (word_subword xi (96,8):(8)word) (word_subword xi (104,8):(8)word):(16)word)
                 (word_join (word_subword xi (112,8):(8)word) (word_subword xi (120,8):(8)word):(16)word):(32)word):(64)word =
    word_reversefields 8 (word_subword xi (64,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

let REV64_128 = prove(
  `!(xi:(128)word).
    word_join
      (word_reversefields 8 (word_subword xi (64,64):(64)word))
      (word_reversefields 8 (word_subword xi (0,64):(64)word)):(128)word =
    word_subword (word_join (word_reversefields 8 xi:(128)word)
                            (word_reversefields 8 xi:(128)word):(256)word) (64,128)`,
  CONV_TAC WORD_BLAST);;

let WORD_SWAP_HALVES_INVOLUTION = prove(
  `!(a:(128)word).
    word_subword
      (word_join
        (word_subword (word_join a a:(256)word) (64,128):(128)word)
        (word_subword (word_join a a:(256)word) (64,128):(128)word):(256)word)
      (64,128):(128)word = a`,
  CONV_TAC WORD_BLAST);;

(* ins->ext runtime opt (2026-08-11): the GHASH-tail Karatsuba mids now use
   `ext vD.16b,vN.16b,vN.16b,#8` in place of `ins vD.d[0],vN.d[1]` (a false-dep
   break; both consumed lane-0-only, values identical).  The stepper models
   `ext vD,vN,vN,#8` on a 128-bit register as
   `word_subword (word_join vN vN:256 word) (64,128):128 word` (a rot-by-64).
   Every one of the 9 sites consumes ONLY lane 0 downstream (via `eor .8b` or
   `pmull .1d`), i.e. the projection `word_subword (<ext form>) (0,64)`, which
   is exactly the plain lane `word_subword vN (64,64)` the old `ins` form gave.
   Collapsing this COMPOSED projection (NOT the standalone register — that would
   false-fire on the byteswap/REV64 machinery, which uses the same
   word_subword(word_join a a)(64,128) shape) restores the pre-opt syntactic
   form, so ABBREV_INNER_PMULS's setify qq-numbering and every downstream tail
   bridge match unchanged.  This is the same identity as SJ_COLLAPSE
   (mainloop.ml), lifted here so the per-step normalizer below can fire it. *)
let EXT8_LANE0_IS_SUBWORD_HI = prove(
  `!(w:(128)word).
    word_subword (word_subword (word_join w w:(256)word) (64,128):(128)word) (0,64):(64)word =
    word_subword w (64,64)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* The xi_p store value is the per-lane byte-reverse of the GHASH result R
   (rev64 on each 64-bit lane); that equals word_bytereverse of the whole 128. *)
let REV64_LANES_EQ = prove(
  `!R:int128. word_join (word_reversefields 8 (word_subword R (0,64):(64)word))
                        (word_reversefields 8 (word_subword R (64,64):(64)word)):(128)word =
              word_bytereverse R`,
  CONV_TAC WORD_BLAST);;

(* Structural normalization lemmas for the GHASH bridge close (from the standalone
   gcm_gmult_v8 proof).  word_insert comes from the INS instr, nested word_subword
   from the EXT instr.  byteswap128 = pure 64-bit half-swap. *)
let WORD_INSERT_SUBWORD = prove(
  `(!x:int128 y:64 word. word_subword (word_insert x (0,64) y : int128) (64,64) : 64 word = word_subword x (64,64)) /\
   (!x:int128 y:64 word. word_subword (word_insert x (64,64) y : int128) (0,64) : 64 word = word_subword x (0,64)) /\
   (!x:int128 y:64 word. word_subword (word_insert x (0,64) y : int128) (0,64) : 64 word = y) /\
   (!x:int128 y:64 word. word_subword (word_insert x (64,64) y : int128) (64,64) : 64 word = y)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN BITBLAST_TAC);;

let WORD_SUBWORD_SUBWORD = prove(
  `(!x:int128. word_subword (word_subword x (0,128) : int128) (0,64) : 64 word = word_subword x (0,64)) /\
   (!x:int128. word_subword (word_subword x (0,128) : int128) (64,64) : 64 word = word_subword x (64,64)) /\
   (!x:int128. word_subword (word_subword x (64,128) : int128) (0,64) : 64 word = word_subword x (64,64)) /\
   (!x:int128. word_subword (word_subword x (0,64) : 64 word) (0,64) : 64 word = word_subword x (0,64))`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* GHASH bridge lemmas (recovered from the standalone gcm_gmult proof).       *)
(* These prove the Karatsuba + Prop3 reduction the assembly computes equals   *)
(* the spec-level polyval_dot / ghash_polyval_acc, so the symbolic Q19 result *)
(* at the xi_p store can be bridged to the postcondition.  All are BITBLAST / *)
(* WORD_RULE proofs (no CHEAT, no axioms).                                    *)
(* ------------------------------------------------------------------------- *)

let KARATSUBA_LIMBS = prove(
  `!(p_lo:int128) (p_hi:int128) (cross:int128).
   let t:(256)word = word_xor (word_xor (word_zx p_lo)
                                        (word_shl (word_zx cross) 64))
                              (word_shl (word_zx p_hi) 128) in
   word_subword t (0,64) : 64 word = word_subword p_lo (0,64) /\
   word_subword t (64,64) : 64 word = word_xor (word_subword p_lo (64,64))
                                               (word_subword cross (0,64)) /\
   word_subword t (128,64) : 64 word = word_xor (word_subword p_hi (0,64))
                                                (word_subword cross (64,64)) /\
   word_subword t (192,64) : 64 word = word_subword p_hi (64,64)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT CONJ_TAC THEN BITBLAST_TAC);;

let JOIN_SUBWORD_RULES = prove(
  `(!a b:64 word. word_subword (word_join a b : int128) (0,64) : 64 word = b) /\
   (!a b:64 word. word_subword (word_join a b : int128) (64,64) : 64 word = a)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN BITBLAST_TAC);;

let WORD_XOR_ACI = WORD_RULE
  `(!x y:N word. word_xor x y = word_xor y x) /\
   (!x y z:N word. word_xor (word_xor x y) z = word_xor x (word_xor y z)) /\
   (!x y z:N word. word_xor x (word_xor y z) = word_xor y (word_xor x z))`;;

let GHASH_1BLOCK_CORRECT = prove(
  `!acc block h:int128.
    polyval_dot (word_xor acc block) h = ghash_polyval_acc h acc [block]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ghash_polyval_acc; polyval_dot]);;

let BYTESWAP128_INVOLUTION = prove(
  `!x:int128. byteswap128(byteswap128 x) = x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128] THEN BITBLAST_TAC);;

let BYTEREVERSE128_XOR = prove(
  `!x y:int128. word_bytereverse(word_xor x y) =
                word_xor (word_bytereverse x) (word_bytereverse y)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* DEC bridge helper lemmas (proven interactively; TODO: move to common file).*)
(* These collapse the dec 1-block GHASH data block at the s350 bridge state.  *)
(*                                                                             *)
(* The dec data block fed to the GHASH multiply reduces to the byteswap128-   *)
(* WRAPPED form (unlike enc, which is unwrapped).  FULLBLK / FULLBLK2 prove    *)
(* the block (tag-half XOR ciphertext-half, both byteswapped per the dec EXT   *)
(* lane order) = byteswap128 (word_xor (brev xi) (brev cph)).  tagv abbrev =   *)
(* word_subword (word_join xi xi) (64,128).                                    *)
(* ------------------------------------------------------------------------- *)
let FULLBLK = prove(
  `!xi cph:int128.
     word_xor
       (word_subword (word_join
          (byteswap128 (word_bytereverse (word_subword (word_join xi xi:(256)word)(64,128):int128)))
          (byteswap128 (word_bytereverse (word_subword (word_join xi xi:(256)word)(64,128):int128))):(256)word)(64,128):int128)
       (byteswap128 (word_bytereverse cph))
     = byteswap128 (word_xor (word_bytereverse xi) (word_bytereverse cph))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* Same, stated over a free tagv with the half-swap hypothesis (matches the    *)
(* live Q19 hyp where tagv is an abbreviation).                                *)
let FULLBLK2 = prove(
  `!xi cph tagv:int128.
     word_subword (word_join (xi:int128) xi:(256)word) (64,128) = tagv
     ==> word_xor
           (word_subword (word_join
              (byteswap128 (word_bytereverse tagv))
              (byteswap128 (word_bytereverse tagv)):(256)word)(64,128):int128)
           (byteswap128 (word_bytereverse cph))
         = byteswap128 (word_xor (word_bytereverse xi) (word_bytereverse cph))`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* word_subword (word_insert x (0,64) y) (0,64) = word_subword y (0,64):        *)
(* discards the leftover tag tree x in the Karatsuba cross-term of the dec      *)
(* GHASH byte-form (the high half is inserted then re-extracted as the low).    *)
let INSERT_SUBWORD_KILL = prove(
  `!(x:(128)word) (y:(128)word).
     word_subword ((word_insert x (0,64) y):(128)word) (0,64):(64)word
     = word_subword y (0,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* byteswap128 in this codebase is a pure 64-bit LANE SWAP (not a byte reverse):     *)
(* subword(byteswap128 X)(0,64) = subword X (64,64) and (64,64) <- (0,64).            *)
(* KEY to the dec bridge: the dec GHASH data operand is byteswap128-wrapped (FULLBLK).*)
(* Rewriting with SUBWORD_BYTESWAP BEFORE GMULT expansion turns the byteswapped       *)
(* product subwords into clean swapped-lane subwords, so ABBREV_INNER_PMULS yields     *)
(* the clean enc-shape qq0/qq1/qq2 (lo/hi/mid) instead of 6 unmergeable products.      *)
let SUBWORD_BYTESWAP = prove(
  `!X:int128.
     word_subword (byteswap128 X) (0,64):(64)word = word_subword X (64,64) /\
     word_subword (byteswap128 X) (64,64):(64)word = word_subword X (0,64)`,
  GEN_TAC THEN REWRITE_TAC[byteswap128] THEN CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* TODO: move to common file. Lane-split + per-shift folds used by the dec GHASH *)
(* bridge close to reduce the W-reduction to pure 64-bit identities.             *)
(* int128 equality via its two 64-bit subwords.                                  *)
let EQ_BY_SUBWORDS_128 = prove(
  `!a b:int128.
     a = b <=>
     (word_subword a (0,64):(64)word = word_subword b (0,64) /\
      word_subword a (64,64):(64)word = word_subword b (64,64))`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN CONV_TAC WORD_BLAST);;

(* The shl63/62/57 W-reduction triple's subwords as clean 64-bit ops.            *)
let TRIPLE_LO = prove(
  `!v:(64)word.
     word_subword (word_xor (word_xor (word_shl (word_zx v:(128)word) 63) (word_shl (word_zx v:(128)word) 62)) (word_shl (word_zx v:(128)word) 57)) (0,64):(64)word
     = word_xor (word_xor (word_shl v 63) (word_shl v 62)) (word_shl v 57)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;
let TRIPLE_HI = prove(
  `!v:(64)word.
     word_subword (word_xor (word_xor (word_shl (word_zx v:(128)word) 63) (word_shl (word_zx v:(128)word) 62)) (word_shl (word_zx v:(128)word) 57)) (64,64):(64)word
     = word_xor (word_xor (word_ushr v 1) (word_ushr v 2)) (word_ushr v 7)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Scalable (a)+(b) decomposition of the GHASH multiply+reduce bridge.         *)
(*                                                                             *)
(* The unroll8 decrypt/encrypt loop accumulates N per-block Karatsuba products *)
(* into Q17/Q18/Q19 and applies ONE shared Prop3 reduction per 8-block         *)
(* iteration.  Factoring the bridge as (a)+(b) below makes both pieces reusable *)
(* at every block count (1/2/4/8), composed with the already-proven, list-     *)
(* generic GHASH_POLYVAL_ACC_BATCHED (common/polyval_ghash.ml):                *)
(*   (a) PMUL_KARATSUBA (common/karatsuba_pmul.ml): the per-block 3-pmull       *)
(*       (lo/hi/mid) byteform = word_pmul a b (the 256-bit product).            *)
(*   (b) GMULT_REDUCE_PROP3 (below): the assembly's W-reduction byteform over   *)
(*       an ABSTRACT 256-bit accumulator t = polyval_reduce_prop3 t.            *)
(* See memory/project_bridge_lemma_scalability.md for the full analysis.       *)
(* ------------------------------------------------------------------------- *)

(* Helper: the low 64-bit lane of v0 = word_join aa bb XOR wa.  Used to make    *)
(* the GMULT and Prop3 `word_pmul _ W` atoms syntactically identical (pmul is   *)
(* opaque to BITBLAST, so the two wv-inputs must match before the lane blast).  *)
let V0LO = prove(
  `!aa bb:64 word. !wa:int128.
     word_subword (word_xor (word_join aa bb:int128) wa) (0,64):64 word =
     word_xor bb (word_subword wa (0,64):64 word)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* (b) The shared Prop3 reduction: the GMULT/assembly W-reduction byteform over  *)
(* an abstract 256-bit accumulator t equals polyval_reduce_prop3 t.  aa/bb/cc/dd *)
(* are t's four 64-bit lanes; w = 0xC200000000000000.  Reusable at any block     *)
(* count (the N-block loop reduces the accumulated 256-bit sum exactly once).    *)
let GMULT_REDUCE_PROP3 = prove(
  `!t:256 word.
     let aa = word_subword t (0,64):64 word in
     let bb = word_subword t (64,64):64 word in
     let cc = word_subword t (128,64):64 word in
     let dd = word_subword t (192,64):64 word in
     let w = word 13979173243358019584:64 word in
     let wa:int128 = word_pmul aa w in
     let v0:int128 = word_xor (word_join aa bb) wa in
     let wv:int128 = word_pmul (word_subword v0 (0,64):64 word) w in
     word_xor wv (word_xor (byteswap128 v0) (word_join dd cc)) = polyval_reduce_prop3 t`,
  GEN_TAC THEN REWRITE_TAC[polyval_reduce_prop3; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[V0LO] THEN
  ABBREV_TAC `wa:int128 = word_pmul (word_subword (t:256 word) (0,64):64 word) (word 13979173243358019584:64 word)` THEN
  ABBREV_TAC `wv:int128 = word_pmul (word_xor (word_subword (t:256 word) (64,64):64 word) (word_subword (wa:int128) (0,64):64 word)) (word 13979173243358019584:64 word)` THEN
  REWRITE_TAC[byteswap128] THEN BITBLAST_TAC);;

(* The full GHASH multiply+reduce bridge: the byte-level Karatsuba/Prop3 the   *)
(* assembly computes (left-hand side, in terms of 64-bit pmul limbs) equals    *)
(* the spec-level polyval_dot.  Now derived from (a) PMUL_KARATSUBA + (b)       *)
(* GMULT_REDUCE_PROP3 + KARATSUBA_LIMBS (lanes of word_pmul a b = the limbs),   *)
(* instead of a single monolithic BITBLAST.                                     *)
let GMULT_FULL_CORRECT_BA = prove(
  `!a b:int128.
   let a_lo = word_subword a (0,64) : 64 word in
   let a_hi = word_subword a (64,64) : 64 word in
   let b_lo = word_subword b (0,64) : 64 word in
   let b_hi = word_subword b (64,64) : 64 word in
   let p_lo:int128 = word_pmul b_lo a_lo in
   let p_hi:int128 = word_pmul b_hi a_hi in
   let p_mid:int128 = word_pmul (word_xor b_lo b_hi) (word_xor a_lo a_hi) in
   let cross = word_xor (word_xor p_mid p_lo) p_hi in
   let bb = word_xor (word_subword p_lo (64,64) : 64 word)
                     (word_subword cross (0,64) : 64 word) in
   let cc = word_xor (word_subword p_hi (0,64) : 64 word)
                     (word_subword cross (64,64) : 64 word) in
   let aa = word_subword p_lo (0,64) : 64 word in
   let dd = word_subword p_hi (64,64) : 64 word in
   let w:64 word = word 13979173243358019584 in
   let wa:int128 = word_pmul aa w in
   let v0:int128 = word_xor (word_join aa bb) wa in
   let wv:int128 = word_pmul (word_subword v0 (0,64) : 64 word) w in
   let result:int128 = word_xor wv (word_xor (byteswap128 v0) (word_join dd cc)) in
   result = polyval_dot a b`,
  (* Compose (a)+(b): polyval_dot a b = polyval_reduce_prop3 (word_pmul a b)  [def];
     word_pmul a b = the Karatsuba 256-word assembly K  [(a) PMUL_KARATSUBA];
     polyval_reduce_prop3 K = the W-reduction byteform over K's lanes  [GSYM (b) GMULT_REDUCE_PROP3];
     K's lanes = the p_lo/cross/p_hi limbs  [KARATSUBA_LIMBS]; then the two byteforms are
     identical up to pmul argument order  [WORD_PMUL_SYM].  Replaces the old monolithic BITBLAST. *)
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[polyval_dot] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  GEN_REWRITE_TAC RAND_CONV
    [GSYM (REWRITE_RULE[LET_DEF; LET_END_DEF] GMULT_REDUCE_PROP3)] THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] KARATSUBA_LIMBS] THEN
  REWRITE_TAC[WORD_PMUL_SYM] THEN REFL_TAC);;

let SIMD_SIMPLIFY_RULES = [REV64_LOWER_LANE; REV64_UPPER_LANE; REV64_128];;

let SIMD_SIMPLIFY_ASSUM_TAC =
  RULE_ASSUM_TAC(fun th ->
    try REWRITE_RULE SIMD_SIMPLIFY_RULES th with _ -> th);;

(* Per-step SIMD simplifier core: fold REV64 trees, cancel double half-swaps,
   normalize nested subwords.  Run after each GHASH step so terms stay small. *)
let GCM_SIMD_SIMPLIFY_CORE_TAC =
  SIMD_SIMPLIFY_ASSUM_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [WORD_SWAP_HALVES_INVOLUTION; EXT8_LANE0_IS_SUBWORD_HI]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    with _ -> th);;

(* The REV64 fold needs TWO passes to reach a fixpoint: pass 1 normalizes the
   nested word_subword tree, pass 2 lets the REV64 lane rules (REV64_LOWER_LANE/
   UPPER_LANE/128) match.  A single pass leaves the raw byte-tree (~2.5k chars)
   in read Q8; two passes fold it to ~320 chars.  Applying the core twice is
   enough empirically (the result is a fixpoint). *)
let GCM_SIMD_SIMPLIFY_TAC =
  GCM_SIMD_SIMPLIFY_CORE_TAC THEN GCM_SIMD_SIMPLIFY_CORE_TAC;;

(* Discard large counter-increment register hypotheses *)
let DISCARD_COUNTER_REGS_TAC =
  DISCARD_ASSUMPTIONS_TAC(fun th ->
    let s = string_of_term (concl th) in
    String.length s > 500 &&
    (let has sub = let slen = String.length s and sublen = String.length sub in
      let rec check j = if j > slen - sublen then false
        else if String.sub s j sublen = sub then true else check (j+1) in check 0 in
     has "read Q1 " || has "read Q2 " || has "read Q3 " || has "read Q4 " ||
     has "read Q5 " || has "read Q6 " || has "read Q7 " || has "read Q30 " ||
     has "read Q16 " || has "read Q17 " || has "read Q18 " || has "read Q19 "));;

(* Resolve conditional branches in PC hypotheses *)
let RESOLVE_BRANCH_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && can (find_term is_cond) (rhs c) &&
       can (find_term (fun t -> name_of t = "PC")) (lhs c) then
      CONV_RULE(RAND_CONV(
        REWRITE_CONV[WORD_RULE `word_sub (word_sub (word_add (x:int64) (word a)) x) (word b) = word_sub (word a) (word b)`;
                     WORD_RULE `word_sub (word_add (x:int64) (word a)) x = word a`] THENC
        DEPTH_CONV WORD_NUM_RED_CONV THENC DEPTH_CONV NUM_RED_CONV THENC
        REWRITE_CONV[BIT_WORD; DIMINDEX_64] THENC NUM_REDUCE_CONV THENC
        REWRITE_CONV[bitval] THENC INT_REDUCE_CONV THENC
        REWRITE_CONV[TAUT `~T <=> F`; TAUT `~F <=> T`;
                     TAUT `F /\ p <=> F`; TAUT `T /\ p <=> p`;
                     TAUT `(F <=> F) <=> T`; TAUT `(T <=> T) <=> T`;
                     TAUT `(T <=> F) <=> F`; TAUT `(F <=> T) <=> F`] THENC
        REWRITE_CONV[COND_CLAUSES])) th
    else th);;

(* Step with branch resolution before each step *)
let ARM_STEPS_RESOLVE_TAC exec range =
  MAP_EVERY (fun n -> RESOLVE_BRANCH_TAC THEN ARM_STEPS_TAC exec [n]) (range);;

(* Step with branch resolution + per-step SIMD REV64 folding (Mila's pattern).
   Folds the byte-tree the instant each REV64/EXT step produces it, so the
   final closure never sees a 145k-char term. *)
let ARM_STEPS_RESOLVE_SIMD_TAC exec range =
  MAP_EVERY (fun n ->
    RESOLVE_BRANCH_TAC THEN ARM_STEPS_TAC exec [n] THEN GCM_SIMD_SIMPLIFY_TAC)
    (range);;

(* VSTEPS variant: keeps register hypotheses alive (needed to capture the
   ciphertext/xi store read-backs) AND folds the REV64 byte-tree per step.
   Used for the store windows where ARM_STEPS_TAC would discard the register
   value the store read-back references. *)
let ARM_VSTEPS_RESOLVE_SIMD_TAC exec range =
  MAP_EVERY (fun n ->
    RESOLVE_BRANCH_TAC THEN ARM_VSTEPS_TAC exec [n] THEN GCM_SIMD_SIMPLIFY_TAC)
    (range);;

(* Straight-line VSTEPS + per-step fold (no branch resolution).  Used for the
   GHASH multiply/reduce tail (steps 333-351), which has no branches.  Keeps the
   GHASH accumulators (Q17/Q18/Q19) and the xi_p store read-back alive while
   folding REV64 byte-trees so the terms stay bounded (~1-2k chars). *)
let ARM_VSTEPS_FOLD_TAC exec range =
  MAP_EVERY (fun n -> ARM_VSTEPS_TAC exec [n] THEN GCM_SIMD_SIMPLIFY_TAC) (range);;

(* GHASH-tail stepper, expressed via the library's standard single-step+discard idiom (the same
   one plain ARM_STEPS_TAC uses) with the SIMD REV64 fold interleaved.  Per step n:
     ARM_VERBOSE_STEP_TAC  -- advance to state s<n>
     GCM_SIMD_SIMPLIFY_TAC -- fold the REV64 byte-tree into Q19 BEFORE the discard
     DISCARD_OLDSTATE_TAC  -- drop all earlier-state reads, keeping s<n>'s (incl. Q19)
     CLARIFY_TAC
   Folding before discarding is essential: the fold collapses the ~49k-char byte-tree into the
   bounded GHASH accumulator term in Q19, which then survives the discard.  Discarding per step
   holds the hypothesis pile flat at ~77 (vs ~1357 if old states were kept), so each step is
   cheap; measured region 333-348 ~8.8s (was ~90s with the original keep-everything ARM_VSTEPS_FOLD).
   This is the XTS-style "step and simplify as we go" — bare ARM_STEPS_TAC already does the
   step+discard; we only add the byte-tree fold that GHASH's REV64s require. *)
let ARM_STEPS_FOLD_DISCARD_TAC exec snums =
  MAP_EVERY
    (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_TAC THEN
              DISCARD_OLDSTATE_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;

(* Branch-resolving variant of ARM_STEPS_FOLD_DISCARD_TAC: resolve the conditional
   branch in the PC hypothesis, step, fold the REV64 byte-tree, THEN discard the old
   state so the hypothesis pile stays flat.  This is the per-step-discard form of
   ARM_VSTEPS_RESOLVE_SIMD_TAC: use it for the multi-block masked-GHASH tail windows,
   which have branches (b.gt cascade) but need NO intermediate-state readback — the
   only readbacks (Q9 mask collapse, Q12 plaintext capture, store, GHASH accumulator)
   land at the window ENDS, whose current state is preserved.  Keeping ARM_VSTEPS's
   keep-everything form over a 16-19 step window makes each GCM_SIMD_SIMPLIFY pass scan
   a linearly-growing pile (goal ballooned to ~677k chars, O(n^2) total); discarding
   per step holds it flat (~10s vs ~140s per window, measured on the dec le4 tail). *)
let ARM_STEPS_RESOLVE_SIMD_DISCARD_TAC exec snums =
  MAP_EVERY
    (fun s -> RESOLVE_BRANCH_TAC THEN ARM_VERBOSE_STEP_TAC exec s THEN
              GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_OLDSTATE_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;

(* Tactic to abbreviate all word_pmul subterms in the goal *)
let ABBREV_ALL_PMUL_TAC =
  let is_pmul t =
    try let (f,_) = dest_comb t in
        let (g,_) = dest_comb f in
        fst(dest_const g) = "word_pmul"
    with _ -> false in
  fun (asl,w) ->
    let pmuls = find_terms is_pmul w in
    let unique_pmuls = setify pmuls in
    let all_frees = frees w @
      List.concat (map (fun (_,th) -> frees(concl th)) asl) in
    let n = ref 0 in
    let tacs = List.map (fun t ->
      incr n;
      let v = variant all_frees (mk_var("pmul_"^string_of_int !n, type_of t)) in
      ABBREV_TAC (mk_eq(v, t))
    ) unique_pmuls in
    (EVERY tacs) (asl,w);;

(* Discard stale flag hypotheses but KEEP read PC (ENSURES_FINAL_STATE_TAC needs the
   final PC value to discharge the PC postcondition). *)
let DISCARD_COUNTER_ONLY_TAC =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    let s = string_of_term(concl th) in
    try String.sub s 0 7 = "read NF" ||
        String.sub s 0 7 = "read ZF" ||
        String.sub s 0 7 = "read CF" ||
        String.sub s 0 7 = "read VF"
    with _ -> false)));;

(* ------------------------------------------------------------------------- *)
(* GHASH s348 bridge close.  The assembly computes, in Q19 at s348, the       *)
(* Karatsuba+Prop3 GHASH over the block word_xor (brev xi)(brev ct) with KEY  *)
(* byteswap128 h (the htable H is stored twisted; the real GHASH key is        *)
(* byteswap128(read htbl_p)).  GMULT_FULL_CORRECT_BA with b := byteswap128 h   *)
(* makes the lane operands match exactly; we then abbreviate the Karatsuba     *)
(* pmul limbs to opaque atoms, canonicalize their argument order with          *)
(* WORD_PMUL_SYM (via a congruence), and bit-blast the residual structural     *)
(* XOR/join/subword skeleton.  All BITBLAST/WORD_BLAST, no cheat.              *)
(* ------------------------------------------------------------------------- *)

let PMUL_CONG_128 = prove(
  `!a b c d:64 word. a = c /\ b = d ==> (word_pmul a b:int128) = word_pmul c d`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let SUBWORD_XOR_JOIN_DIST = prove(
  `(!x y:int128. word_subword (word_xor x y) (0,64) : 64 word =
      word_xor (word_subword x (0,64)) (word_subword y (0,64))) /\
   (!x y:int128. word_subword (word_xor x y) (64,64) : 64 word =
      word_xor (word_subword x (64,64)) (word_subword y (64,64))) /\
   (!a b:64 word. word_subword (word_join a b : int128) (0,64) : 64 word = b) /\
   (!a b:64 word. word_subword (word_join a b : int128) (64,64) : 64 word = a)`,
  REPEAT CONJ_TAC THEN TRY(REPEAT GEN_TAC) THEN BITBLAST_TAC);;

let SUBWORD0_LEMMAS = prove(
  `(word_subword (word 0:int128) (0,64):64 word = word 0) /\
   (word_subword (word 0:int128) (64,64):64 word = word 0)`,
  CONJ_TAC THEN BITBLAST_TAC);;

(* Abbreviate every currently-innermost fully-applied word_pmul to a fresh qqN:int128. *)
let ABBREV_INNER_PMULS_TAC : tactic = fun (asl,w) ->
  let is_pmul_app t = try let (h,args)=strip_comb t in
        fst(dest_const h)="word_pmul" && length args=2 with _ -> false in
  let pmuls = setify(find_terms is_pmul_app w) in
  let contains_pmul_strict t = exists (fun p -> p <> t &&
     (let rec occ u = u=p ||
        (match u with Comb(a,b)->occ a||occ b|Abs(_,b)->occ b|_->false) in occ t)) pmuls in
  let inner = filter (fun t -> not(contains_pmul_strict t)) pmuls in
  let allvars = itlist (fun (_,th) acc ->
        union (map (fun v -> fst(dest_var v)) (frees(concl th))) acc)
        asl (map (fun v -> fst(dest_var v)) (frees w)) in
  let used = ref allvars in
  let fresh () = let rec go i = let n = "qq"^string_of_int i in
                   if mem n !used then go (i+1) else (used := n :: !used; n) in go 0 in
  EVERY (map (fun t -> ABBREV_TAC (mk_eq(mk_var(fresh(), `:int128`), t))) inner) (asl,w);;

(* For each pair of pmul-atom definitions, try to prove the atoms equal (same product up to
   argument order via WORD_PMUL_SYM, operands equal by WORD_BLAST) and rewrite to merge them. *)
let MERGE_PMUL_ATOMS_TAC : tactic = fun (asl,w) ->
  let is_pmul_app t = try let (h,a)=strip_comb t in
        fst(dest_const h)="word_pmul" && length a=2 with _ -> false in
  let defs = filter (fun (_,th) ->
        let c = concl th in is_eq c && is_var(rhs c) && is_pmul_app(lhs c)) asl in
  let rec allpairs2 = function [] -> []
    | x::xs -> (map (fun y -> (x,y)) xs) @ allpairs2 xs in
  let cand = filter (fun ((_,t1),(_,t2)) -> rhs(concl t1) <> rhs(concl t2)) (allpairs2 defs) in
  let rec chain = function
    | [] -> ALL_TAC
    | ((_,t1),(_,t2))::rest ->
        let v1 = rhs(concl t1) and v2 = rhs(concl t2) in
        let prover =
          EXPAND_TAC (fst(dest_var v1)) THEN EXPAND_TAC (fst(dest_var v2)) THEN
          ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST)
           ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
                   MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST)) in
        (SUBGOAL_THEN (mk_eq(v1,v2)) (fun th -> REWRITE_TAC[th]) THENL [prover; chain rest])
        ORELSE chain rest in
  chain cand (asl,w);;

(* Abbreviate the innermost Prop3 reduction pmul (word_pmul (word_subword _ (0,64)) W). *)
let ABBREV_WA_TAC : tactic = fun (asl,w) ->
  let is_wa t = try let (h,a)=strip_comb t in fst(dest_const h)="word_pmul" &&
                    string_of_term(List.nth a 1)="word 13979173243358019584" &&
                    (let (h2,_)=strip_comb(List.nth a 0) in fst(dest_const h2)="word_subword")
                with _ -> false in
  let was = setify(find_terms is_wa w) in
  let inner = filter (fun t -> not(can (find_term (fun s -> s<>t && is_wa s)) t)) was in
  (match inner with
   | t::_ -> ABBREV_TAC (mk_eq(`wa_atom:int128`, t))
   | [] -> ALL_TAC) (asl,w);;

(* Final: if exactly two pmuls remain (the two wv reductions), prove them equal and blast. *)
let FINISH_WV_TAC : tactic = fun (asl,w) ->
  let is_pmul_app t = try let (h,a)=strip_comb t in
        fst(dest_const h)="word_pmul" && length a=2 with _ -> false in
  let pmuls = setify(find_terms is_pmul_app w) in
  match pmuls with
  | [p0;p1] ->
     (SUBGOAL_THEN (mk_eq(p0,p1)) (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
      CONV_TAC WORD_BLAST) (asl,w)
  | _ -> CONV_TAC WORD_BLAST (asl,w);;

(* Abbreviate the two 64-bit halves of every Karatsuba pmul output as fresh xNl/xNh vars
   (label l=low subword(0,64), h=hi subword(64,64); N from the operand kind: l for
   subword-at-0 product, h for subword-at-64, m for the (a xor b) mid product).  Ported
   verbatim from Mila's one_block_aes256_gcm_preloop_tail_direct.ml. *)
let ABBREV_PMUL_HALVES_TAC : tactic = fun (asl,w) ->
  let classify_pmul eqn =
    try
      let lhs, rhs = dest_eq eqn in
      let pmul, _ = dest_comb lhs in
      let pmul_fn, x_arg = dest_comb pmul in
      if name_of pmul_fn <> "word_pmul" then None
      else begin
        match x_arg with
        | Comb(Comb(Const("word_xor",_), _), _) -> Some ("m", rhs)
        | Comb(Comb(Const("word_subword",_), _), pair) ->
          (try
             let k_term, _ = dest_pair pair in
             let k = dest_small_numeral k_term in
             if k = 0 then Some ("l", rhs)
             else if k = 64 then Some ("h", rhs)
             else None
           with _ -> None)
        | _ -> None
      end
    with _ -> None in
  let pmul_vs = List.filter_map (fun (_, th) -> classify_pmul (concl th)) asl in
  let all_frees =
    frees w @ List.concat (map (fun (_,th) -> frees(concl th)) asl) in
  let subword_const =
    inst [`:128`, `:M`; `:64`, `:N`] `word_subword:(M)word->num#num->(N)word` in
  let rec process all tasks (asl,w) =
    match tasks with
    | [] -> ALL_TAC (asl,w)
    | (label, v_term) :: rest ->
      let vname = "x" ^ label in
      let vl_var = variant all (mk_var(vname ^ "l", `:(64)word`)) in
      let vh_var = variant all (mk_var(vname ^ "h", `:(64)word`)) in
      let el = mk_eq(vl_var, mk_comb(mk_comb(subword_const, v_term), `0,64`)) in
      let eh = mk_eq(vh_var, mk_comb(mk_comb(subword_const, v_term), `64,64`)) in
      (ABBREV_TAC el THEN ABBREV_TAC eh THEN process (vl_var::vh_var::all) rest) (asl,w) in
  process all_frees pmul_vs (asl,w);;

(* Half projection helpers for the Mila close. *)
let JOINMID = prove(
  `!q:int128. word_subword (word_join q q :(256)word) (64,128):int128 =
     word_join (word_subword q (0,64):64 word) (word_subword q (64,64):64 word)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;
let QQ0SPLIT = prove(
  `!q:int128. q = word_join (word_subword q (64,64):64 word) (word_subword q (0,64):64 word)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* W-reduction lane-fold close (the "Mila route"): reduce the post-MERGE GHASH bridge goal to a
   pure 64-bit XOR identity instead of one monolithic WORD_BLAST over `word_pmul _ W`.  Method:
   PMUL_W_64_128 (pmul-by-W -> shl 63/62/57), JOINMID, split qq0/qq1/qq2 into named 64-bit halves
   (QQ0SPLIT), fold the r1/u shift-triples to abbreviations, finish with a flat 64-bit blast.
   NOTE: NOT used by the committed dec close — on the dec goal shape this tactic stack-overflows,
   so the bridge below inlines the r1/u/r2 staging by hand (see methodology doc §5).  Kept as
   reference for the technique. *)
let FINISH_WV_REDUCE_TAC : tactic =
  REWRITE_TAC[PMUL_W_64_128] THEN
  ABBREV_PMUL_HALVES_TAC THEN
  REWRITE_TAC[JOINMID] THEN
  SUBGOAL_THEN
    `qq0:int128 = word_join (xlh:64 word) (xll:64 word) /\
     qq1:int128 = word_join (xhh:64 word) (xhl:64 word) /\
     qq2:int128 = word_join (xmh''':64 word) (xml''':64 word)`
    (fun th -> REWRITE_TAC[CONJUNCT1 th] THEN
               REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)] THEN
               REWRITE_TAC[CONJUNCT2(CONJUNCT2 th)]) THENL
   [(* Each conjunct qqN = word_join (sub qqN 64,64) (sub qqN 0,64) by QQ0SPLIT, then the two
       half hypotheses substitute the subwords.  Direct LAND rewrite + ASM_REWRITE is ~0.4s here;
       the previous ASM_MESON_TAC[QQ0SPLIT] was ~48s (it searched instead of rewriting). *)
    REPEAT CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [QQ0SPLIT] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[JOIN_SUBWORD_RULES] THEN
  ABBREV_TAC
   `r1:(128)word = word_xor (word_xor (word_shl (word_zx (xhl:(64)word):(128)word) 63)
                                      (word_shl (word_zx xhl:(128)word) 62))
                            (word_shl (word_zx xhl:(128)word) 57)` THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_subword (word_shl (word_zx (xhl:(64)word):(128)word) 63) (0,64):(64)word)
                       (word_subword (word_shl (word_zx xhl:(128)word) 62) (0,64):(64)word))
             (word_subword (word_shl (word_zx xhl:(128)word) 57) (0,64):(64)word) =
    word_subword (r1:(128)word) (0,64):(64)word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_subword (word_shl (word_zx (xhl:(64)word):(128)word) 63) (64,64):(64)word)
                       (word_subword (word_shl (word_zx xhl:(128)word) 62) (64,64):(64)word))
             (word_subword (word_shl (word_zx xhl:(128)word) 57) (64,64):(64)word) =
    word_subword (r1:(128)word) (64,64):(64)word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ABBREV_TAC `u:(64)word = word_xor (word_xor (xhh:64 word) (word_xor (word_xor (xml''':64 word) (xhl:64 word)) (xll:64 word))) (word_subword (r1:(128)word) (0,64))` THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_xor (word_xor (xml''':64 word) (xhl:64 word)) (xll:64 word)) (word_subword (r1:128 word) (0,64))) (xhh:64 word) = u`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "u" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOIN_SUBWORD_RULES] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_xor (word_xor (xml''':64 word) (xhl:64 word)) (xll:64 word)) (word_subword (r1:128 word) (0,64))) (xhh:64 word) = u`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "u" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  CONV_TAC WORD_BLAST;;

(* ========================================================================= *)
(* N-block GHASH bridge infrastructure (formerly aesv8_gcm_8x_dec_256_        *)
(* 2block.ml), used by the le2..le8 bands.                                    *)
(*                                                                            *)
(* All library needs are at the top of this file: gmult_nblock_lemmas.ml is   *)
(* SELF-CONTAINED (it proves its own GMULT_REDUCE_PROP3/V0LO), so load order  *)
(* no longer matters.  The V0LO/GMULT_REDUCE_PROP3 definitions earlier in     *)
(* this file harmlessly shadow the identical library ones.                    *)
(* ========================================================================= *)
(* ========================================================================= *)
(* Helper lemmas for the 2-product GHASH bridge (copied verbatim from the      *)
(* encrypt 2-block proof; they are byte-form-agnostic so transfer unchanged).  *)
(* ========================================================================= *)

(* word_join lane split: reduces a 128-bit word_join equality to two 64-bit   *)
(* lane equalities (so the final close is two small flat XOR identities).      *)
let JOIN_EQ_SPLIT = prove(
  `!(a:(64)word) (b:(64)word) (c:(64)word) (d:(64)word).
     ((word_join a b:(128)word) = word_join c d) <=> (a = c /\ b = d)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(fun th ->
      MP_TAC(REWRITE_RULE[JOIN_SUBWORD_RULES]
        (BETA_RULE(AP_TERM `\x:(128)word. word_subword x (64,64):(64)word` th))) THEN
      MP_TAC(REWRITE_RULE[JOIN_SUBWORD_RULES]
        (BETA_RULE(AP_TERM `\x:(128)word. word_subword x (0,64):(64)word` th))) THEN
      MESON_TAC[]);
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* per-lane reversefields: word_reversefields 8 on a full int128 commutes with *)
(* the 64-bit lane projection (with a lane swap).                              *)
let RF8_SUBWORD = prove(
  `(!x:int128. word_subword (word_reversefields 8 x) (0,64):64 word =
               word_reversefields 8 (word_subword x (64,64):64 word)) /\
   (!x:int128. word_subword (word_reversefields 8 x) (64,64):64 word =
               word_reversefields 8 (word_subword x (0,64):64 word))`,
  CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* subword lane extraction through word_zx / word_shl of the 256-bit Karatsuba *)
(* assembly (for a 64-bit source).                                             *)
let SUBW_ZX_256 = prove(
  `(!x:64 word. word_subword (word_zx x:256 word) (0,64):64 word = x) /\
   (!x:64 word. word_subword (word_zx x:256 word) (64,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_zx x:256 word) (128,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_zx x:256 word) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_SHL64_256 = prove(
  `(!x:64 word. word_subword (word_shl (word_zx x:256 word) 64) (0,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 64) (64,64):64 word = x) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 64) (128,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 64) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_SHL128_256 = prove(
  `(!x:64 word. word_subword (word_shl (word_zx x:256 word) 128) (0,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 128) (64,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 128) (128,64):64 word = x) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 128) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
(* and for a 128-bit source (the qq atoms). *)
let SUBW_ZX128_256 = prove(
  `(!x:128 word. word_subword (word_zx x:256 word) (0,64):64 word = word_subword x (0,64)) /\
   (!x:128 word. word_subword (word_zx x:256 word) (64,64):64 word = word_subword x (64,64)) /\
   (!x:128 word. word_subword (word_zx x:256 word) (128,64):64 word = word 0) /\
   (!x:128 word. word_subword (word_zx x:256 word) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_SHL64_128_256 = prove(
  `(!x:128 word. word_subword (word_shl (word_zx x:256 word) 64) (0,64):64 word = word 0) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 64) (64,64):64 word = word_subword x (0,64)) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 64) (128,64):64 word = word_subword x (64,64)) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 64) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_SHL128_128_256 = prove(
  `(!x:128 word. word_subword (word_shl (word_zx x:256 word) 128) (0,64):64 word = word 0) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 128) (64,64):64 word = word 0) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 128) (128,64):64 word = word_subword x (0,64)) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 128) (192,64):64 word = word_subword x (64,64))`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_XOR_256 = prove(
  `!x y:256 word. !lo. word_subword (word_xor x y) (lo,64):64 word =
     word_xor (word_subword x (lo,64)) (word_subword y (lo,64))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_SUBWORD_XOR]);;

(* Collapse a 64-bit lane of subword(subword(join a a)(64,128)) to a plain lane *)
(* of a (the duplicated mid-half the wv W-reduction operand produces).          *)
let SUBSUB_JOIN_DUP = prove(
  `(!a:128 word. word_subword (word_subword (word_join a a :256 word) (64,128) :128 word) (0,64) :64 word
                 = word_subword a (64,64)) /\
   (!a:128 word. word_subword (word_subword (word_join a a :256 word) (64,128) :128 word) (64,64) :64 word
                 = word_subword a (0,64))`,
  CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Abbreviate EVERY `word_subword (a:int128) (lo,64)` subterm in the goal to a   *)
(* fresh 64-bit var, so the residual is a flat word_xor identity over 64-bit     *)
(* vars that WORD_BITWISE_TAC closes.                                            *)
let ABBREV_ALL_SUBWORDS_TAC : tactic = fun (asl,w) ->
  let is_sw64 t = try fst(dest_const(rator(rator t)))="word_subword" &&
                      type_of t = `:(64)word` &&
                      type_of (rand(rator t)) = `:int128` with _->false in
  let sws = setify(find_terms is_sw64 w) in
  let used = ref 0 in
  let tac = itlist (fun t acc ->
      let n = !used in used := n+1;
      ABBREV_TAC (mk_eq(mk_var("zw"^string_of_int n,`:64 word`), t)) THEN acc)
    sws ALL_TAC in
  tac (asl,w);;

(* Fast closer for a merge's operand-equality subgoal (flatten 256-bit Karatsuba *)
(* lanes to 64-bit, abbreviate, WORD_BITWISE — <1s vs ~90s WORD_BLAST).           *)
let FAST_OPERAND_TAC : tactic =
  REWRITE_TAC[SUBW_XOR_256; SUBW_ZX_256; SUBW_SHL64_256; SUBW_SHL128_256;
              SUBW_ZX128_256; SUBW_SHL64_128_256; SUBW_SHL128_128_256] THEN
  REWRITE_TAC[WORD_XOR_0; SUBSUB_JOIN_DUP; WORD_SUBWORD_SUBWORD;
              JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  ABBREV_ALL_SUBWORDS_TAC THEN
  WORD_BITWISE_TAC;;

(* Targeted pmul-atom merge for the 2-block bridge (one structurally-determined  *)
(* pair per call; FAST_OPERAND_TAC closes the operand equalities).               *)
let MERGE_ONE_2BLK_TAC : tactic = fun (asl,w) ->
  let is_pmul t = try let (hd,a)=strip_comb t in fst(dest_const hd)="word_pmul" && length a=2 with _->false in
  let is_wordconst t = try is_comb t && fst(dest_const(rator t))="word" && is_numeral(rand t) with _->false in
  let is_keyvar n = String.length n>=2 && n.[0]='k' &&
                    (try let _ = int_of_string (String.sub n 1 (String.length n-1)) in true with _->false) in
  let goalvars = setify(map (fun t->fst(dest_var t))
    (find_terms (fun t->is_var t && type_of t=`:int128` &&
      (let n=fst(dest_var t) in String.length n>=2 && String.sub n 0 2="qq")) w)) in
  let defs = filter (fun (_,th)->let c=concl th in is_eq c && is_var(rhs c) &&
    is_pmul(lhs c) && mem (fst(dest_var(rhs c))) goalvars) asl in
  let fvnames t = sort (<) (filter (fun n -> not(is_keyvar n))
                              (map (fun v->fst(dest_var v)) (frees t))) in
  let lane_tag op2 =
    if is_comb op2 && is_comb(rator op2) &&
       (try fst(dest_const(rator(rator op2)))="word_subword" with _->false)
    then string_of_term(rand op2) else "X" in
  let info th =
    let p = lhs(concl th) in
    let (_,args) = strip_comb p in
    let op1 = el 0 args and op2 = el 1 args in
    (rhs(concl th), op2, (fvnames op1, fvnames op2, lane_tag op2)) in
  let items = map (fun (_,th)-> info th) defs in
  let rec find_pair = function
    | [] -> None
    | (v,op2,sg)::rest ->
        let cand =
          if is_wordconst op2
          then filter (fun (v2,op2b,_)-> v2<>v && is_wordconst op2b && op2b=op2) rest
          else filter (fun (v2,op2b,sg2)-> v2<>v && not(is_wordconst op2b) && sg2=sg) rest in
        (match cand with (v2,_,_)::_ -> Some(v,v2) | [] -> find_pair rest) in
  (match find_pair items with
  | None -> (fun _ -> failwith "MERGE_ONE_2BLK_TAC: nothing to merge")
  | Some(v1,v2) ->
      let close_op = FAST_OPERAND_TAC ORELSE CONV_TAC WORD_BLAST in
      SUBGOAL_THEN (mk_eq(v1,v2))
        (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]))
       THENL [EXPAND_TAC(fst(dest_var v1)) THEN EXPAND_TAC(fst(dest_var v2)) THEN
              ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN close_op)
               ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
                       MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN close_op));
              ALL_TAC]) (asl,w);;

(* Repeat the single-merge to a fixpoint. *)
let MERGE_2BLK_TAC : tactic = REPEAT MERGE_ONE_2BLK_TAC;;

(* Discard helpers for the front (keep block-0/1 keystreams + GHASH tag). *)
let mk_discard2 keepset =
  DISCARD_ASSUMPTIONS_TAC(fun th ->
    let s = string_of_term (concl th) in
    String.length s > 500 &&
    (let has sub = let sl=String.length s and bl=String.length sub in
      let rec ck j = if j>sl-bl then false else if String.sub s j bl=sub then true else ck(j+1) in ck 0 in
     List.exists (fun n -> has ("read Q"^string_of_int n^" ")) keepset));;



(* The flatten-and-blast close for the 2-product reduction structural identity. *)
let FINISH_2BLK_TAC : tactic =
  REWRITE_TAC[SUBW_XOR_256; SUBW_ZX_256; SUBW_SHL64_256; SUBW_SHL128_256;
              SUBW_ZX128_256; SUBW_SHL64_128_256; SUBW_SHL128_128_256] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_SUBWORD_SUBWORD] THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOINMID] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  ABBREV_ALL_SUBWORDS_TAC THEN
  REWRITE_TAC[JOIN_EQ_SPLIT] THEN
  REPEAT CONJ_TAC THEN WORD_BITWISE_TAC;;

(* ========================================================================= *)
(* GMULT2 fast-reduce bridge (the ~35s route, replacing the ~73s MERGE/FINISH *)
(* reduce-blast).  GMULT2_FULL_CORRECT_BA is the scalable 2-block fused        *)
(* multiply+reduce: the assembly's byteform that XOR-accumulates TWO Karatsuba *)
(* triples then runs the shared W-reduction equals                            *)
(*   polyval_reduce_prop3 (word_pmul a0 b0 XOR word_pmul a1 b1).               *)
(* Built from PMUL_KARATSUBA + GMULT_REDUCE_PROP3 (W-reduction proven ONCE in  *)
(* the dec 1-block file), so the reduction is NEVER re-blasted.  This is OUR-  *)
(* binary analog of Mila's GHASH_NBLOCK_KARATSUBA_EQ_PROP3; the per-block      *)
(* operand transpose (rev64/h <-> brev/byteswap128) is reconciled by MERGE_2BLK *)
(* and the W-reduction *surface* arrangement is closed by the r1/u/r2 hand     *)
(* staging in DEC_2BLK_GMULT2_BRIDGE_TAC (generalized from the dec 1-block      *)
(* s351 W-staging, 3 atoms -> 6).  See _docs/gmult2-fused-reduce-lemma.md and   *)
(* _docs/dec-2block-gmult2-finish-handoff.md.                                  *)
(* ------------------------------------------------------------------------- *)

(* GMULT2_FULL_CORRECT_BA: the 2-block fused multiply+reduce byteform =          *)
(* polyval_reduce_prop3 (word_pmul a0 b0 XOR word_pmul a1 b1).  Built INSTANTLY  *)
(* by the shared fast GMULTn builder (common/gmult_nblock_lemmas.ml); the build *)
(* reproduces the old hand-written dec2_tL + PACK2_ID derivation's concl exactly. *)
let PACK2_ID, GMULT2_FULL_CORRECT_BA = build_GMULTn_fast 2;;



(* Targeted lane closer: fold ONLY the 64-bit lane-subword equations (rhs a    *)
(* qqNl/qqNh var), NOT the pmul atom defs (which would re-expand qq atoms),     *)
(* then a flat 64-bit WORD_RULE (XOR-ACI over the named lanes).                 *)
let LANE_CLOSE_TAC : tactic = fun (asl,w) ->
  let is_lane_def (_,th) =
    let c = concl th in is_eq c &&
    (try let r = rhs c in is_var r &&
       (let n = fst(dest_var r) in String.length n>=3 && String.sub n 0 2="qq" &&
        (let last = n.[String.length n-1] in last='l' || last='h'))
     with _ -> false) &&
    (try let l = lhs c in is_comb l && fst(dest_const(rator(rator l)))="word_subword" with _ -> false) in
  let lane_ths = map snd (filter is_lane_def asl) in
  (REWRITE_TAC lane_ths THEN CONV_TAC WORD_RULE) (asl,w);;

(* ========================================================================= *)
(* SECTION 2: DECRYPT-SPECIFIC LEMMAS AND TACTICS.                            *)
(*                                                                            *)
(* Everything below is keyed to the DECRYPT dataflow (GHASH input = the RAW   *)
(* loaded ciphertext blocks cph_i; the masked less_than_1 path ANDs the       *)
(* loaded block).  The encrypt analogues differ in which term feeds the       *)
(* GHASH multiply (computed ciphertext), so these do NOT transfer.            *)
(* ========================================================================= *)

(* Collapse the all-ones partial-block mask on the block-1 ciphertext: the dec
   less_than_1 path applies `and v9,v9,v0` with an all-ones mask v0, so the GHASH
   multiply (rev64 v8,v9) carries `word_and <mask> cph1` inside Q8/Q17/Q18/Q19.
   For a full block the mask is all-ones (its 64-bit lanes are 0xff..ff, the
   aes-junk base fully overwritten), so `word_and <mask> cph1 = cph1` by WORD_BLAST.
   This tactic finds that masked term inside Q8 and rewrites it to cph1 everywhere,
   so the bridge merge sees the clean `word_reversefields 8 cph1` block.  (Without
   this the block-1 pmul atoms carry the masked form and the merge cannot pair them
   with the spec's brev cph1 atoms.) *)
let MASK_COLLAPSE_CPH1_TAC : tactic = fun (asl,w) ->
  let q8 = tryfind (fun (_,th)-> if (try string_of_term(rand(rator(lhs(concl th))))="Q8" with _->false) then th else fail()) asl in
  let mterm = hd (find_terms (fun t-> try fst(dest_const(rator(rator t)))="word_and" && rand t = `cph1:int128` with _->false) (rhs(concl q8))) in
  let eqn = mk_eq(mterm, `cph1:int128`) in
  (SUBGOAL_THEN eqn (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th)
    THENL [CONV_TAC WORD_BLAST; ALL_TAC]) (asl,w);;

(* XOR-commutativity helper for the wal lane (the two byteforms present the     *)
(* wa-round lane sum in opposite operand order).                               *)
let DEC2_WXSYM = WORD_RULE `word_xor qq6l qq1l = word_xor qq1l qq6l`;;

(* The full GMULT2 bridge close.  Assumes the goal is
     <gq19 s370 byteform> = ghash_polyval_acc (byteswap128 h)(brev xi)
                              [brev cph0; brev cph1]
   with the hk preconditions + the H^2 relation (asm25) in the assumptions.
   Steps: (1) fold the spec RHS to the GMULT2-instantiated byteform (operands
   a0=brev xi^brev cph0, b0=byteswap128 h2, a1=brev cph1, b1=byteswap128 h) via
   GHASH_POLYVAL_ACC_2 + asm25 GSYM + GMULT2_FULL_CORRECT_BA; (2) MERGE_2BLK the
   block products to the 6 atoms {qq0,qq1,qq4,qq5,qq6,qq10}; (3) the r1/u/r2
   W-reduction hand staging (generalized from the dec 1-block, 3 atoms -> 6) then
   a flat per-lane WORD_RULE.  ~30s total (was ~73s MERGE/FINISH). *)
let DEC_2BLK_GMULT2_BRIDGE_TAC : tactic =
  let a0t = `word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`
  and a1t = `word_bytereverse cph1:int128` in
  let gmult2_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [a0t; `byteswap128 h2:int128`; a1t; `byteswap128 h:int128`] GMULT2_FULL_CORRECT_BA) in
  let r1def = `word_xor (word_xor (word_shl (word_zx (wal:64 word):128 word) 63) (word_shl (word_zx wal:128 word) 62)) (word_shl (word_zx wal:128 word) 57)` in
  let udef = `word_xor (word_subword (r1:128 word) (0,64):64 word) (word_xor (word_xor qq1h qq6h) (word_xor (word_xor qq0l (word_xor qq1l qq4l)) (word_xor qq5l (word_xor qq10l qq6l))))` in
  (* spec -> prop3(...) -> GMULT2 byteform LHS *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th)=`byteswap128 h2` with _->false)
    then GEN_REWRITE_TAC RAND_CONV
           [REWRITE_RULE[GSYM gmult2_dec]
             (GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [GSYM th]
               (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
                       `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`]
                 GHASH_POLYVAL_ACC_2))]
    else NO_TAC) THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[byteswap128] THEN
  REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
  REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
  ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
  REWRITE_TAC[PMUL_W_64_128] THEN REWRITE_TAC[JOINMID] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  EVERY (map (fun a ->
    let av = mk_var(a,`:int128`) in
    ABBREV_TAC (mk_eq(mk_var(a^"l",`:64 word`), mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, av), `(0,64)`))) THEN
    ABBREV_TAC (mk_eq(mk_var(a^"h",`:64 word`), mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, av), `(64,64)`))))
    ["qq0";"qq1";"qq4";"qq5";"qq6";"qq10"]) THEN
  ABBREV_TAC `wal:64 word = word_xor qq1l qq6l` THEN
  REWRITE_TAC[DEC2_WXSYM] THEN
  FIRST_ASSUM(fun th -> if (try rhs(concl th)=`wal:64 word` && lhs(concl th)=`word_xor qq1l qq6l:64 word` with _->false) then REWRITE_TAC[th] else NO_TAC) THEN
  ABBREV_TAC (mk_eq(`r1:128 word`, r1def)) THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 63) (0,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 62) (0,64):64 word)) (word_subword (word_shl (word_zx wal:128 word) 57) (0,64):64 word) = word_subword (r1:128 word) (0,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 63) (64,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 62) (64,64):64 word)) (word_subword (word_shl (word_zx wal:128 word) 57) (64,64):64 word) = word_subword (r1:128 word) (64,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 57) (0,64):64 word) (word_xor (word_subword (word_shl (word_zx wal:128 word) 62) (0,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 63) (0,64):64 word)) = word_subword (r1:128 word) (0,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 57) (64,64):64 word) (word_xor (word_subword (word_shl (word_zx wal:128 word) 62) (64,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 63) (64,64):64 word)) = word_subword (r1:128 word) (64,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ABBREV_TAC (mk_eq(`u:64 word`, udef)) THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_xor qq10l qq4l) (word_xor wal (word_xor qq0l qq5l))) (word_xor (word_xor qq1h qq6h) (word_subword (r1:128 word) (0,64):64 word)) = u`
   (fun th -> REWRITE_TAC[th]) THENL [MAP_EVERY EXPAND_TAC ["u";"wal"] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (r1:128 word) (0,64):64 word) (word_xor (word_xor qq1h qq6h) (word_xor (word_xor qq0l (word_xor qq1l qq4l)) (word_xor qq5l (word_xor qq10l qq6l)))) = u`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "u" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC `us57:128 word = word_shl (word_zx (u:64 word):128 word) 57` THEN
  ABBREV_TAC `us62:128 word = word_shl (word_zx (u:64 word):128 word) 62` THEN
  ABBREV_TAC `us63:128 word = word_shl (word_zx (u:64 word):128 word) 63` THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_CLOSE_TAC;;
(* -------------------------------------------------------------------------
   PROGRESS (dec 2-block, mirror of enc 2-block + dec tail dataflow)
   -------------------------------------------------------------------------
   HYBRID: dec binary (dec mc/EXEC, dec step->PC map, dec tail dataflow where
   Q9 = input ciphertext is GHASHed and Q12 = plaintext is stored) + the enc
   2-block STRATEGY (keep Q1/ctr1, cascade to more_than_1 then less_than_1,
   GHASH_POLYVAL_ACC_2 bridge).

   STEP->PC MAP DISCOVERED (dec binary, this proof):
     1--5   prologue 0x18..0x28; s5 pc+0x2c, X9=32, X1=256.
     6--30  CTR setup (per-step fold, keep Q0,Q1,Q30); s30 pc+0x90.
     31--84 AES bulk; s84 pc+360.  85--173; s173 pc+716, X5=word 0.
     174--177 GHASH tag load+rev64 + GCM_SIMD_SIMPLIFY -> Q19 stable
              reversefields(xi) form.  178--184; 185--254; s254 pc+1040.
     [255] cmp x0,x5/b.ge -> tail (INT_SUB_REFL).  256--265; s265 pc+3788.
       set X5=word 32 (WORD_RULE).  Q9 s265 = cph0; Q16 = partial tag.
     266--272 tail+eor3 v12,v9,v0,v29 -> s272 pc+3816 Q12 = block-0 plaintext.
       Abbrev Q12 -> pt0 = word_xor cph0 (aes256_encrypt ctr0 keys) (spec form).
     273--312 cascade movs (DISCARD_OLDSTATE at s312 to flatten pile!).
       *** Use ARM_VSTEPS_FOLD then DISCARD_OLDSTATE; do NOT keep all states
       (the mov v_k cascade copies Q1's 2666-char keystream into Q2..Q7 across
       40 states = pile blow-up).
     [313] RESOLVE_BRANCH (x5=32>16, b.gt) -> s313 pc+4340 = 0x10f4 = more_than_1.
       Q7 = block-1 keystream; Q9 = cph0; Q12 = pt0; Q17/18/19 = 0.

   NEXT (more_than_1 0x10f4..0x1134, dec block-0 GHASH vs H^2):
     - st1 v12,[x2],#16 stores pt0 to out_p, advances X2 to out_p+16.
       *** capture out_p block-0 readback = pt0 BEFORE discard.
     - rev64 v8,v9 (v9=cph0 ATOM, so no tower blow-up unlike enc's ct0);
       eor v8,v8,v16 (feed tag); pmull2/pmull/mid vs Q22=h2 + Q21=hk hi lane;
       accumulate Q17/Q19/Q18.  ldr q9,[x0]=cph1; eor3 v12,v9,v7 = block-1 PT.
       *** abbrev block-1 Q12 -> pt1 = word_xor cph1 (aes256_encrypt ctr1 keys);
       ctr1 keystream input = gcm_ctr_inc ctr0 (GCM_CTR_INC_LANES on Q7/Q1).
     - less_than_1 0x1450..: X1=128 -> mask all-ones, Q9=cph1; block-1 GHASH vs
       Q20=h; accumulate; single Prop3 reduction folds BOTH blocks.  store pt1.
     - BRIDGE at dec s351-analog (NOT s350): the dec MODULO splits enc's 3 eor3
       into 6 eors, so the final eor lands one step later.  Find the analog of
       enc s367 (clean polyval) empirically; assert read Q19 =
         ghash_polyval_acc (byteswap128 h)(brev xi)[brev cph0; brev cph1]
       via DEC_2BLK_GMULT2_BRIDGE_TAC (GMULT2 fast route, ~30s; the old
         GHASH_POLYVAL_ACC_2 + MERGE_2BLK + FINISH_2BLK reduce-blast was ~73s).
     - ext+rev64 -> word_bytereverse gval; store xi_p; exit pc+0x11e4.

   UPDATE: bridge state is s370 (pc+4568), the analog of dec 1-block s351 (after
   the final `eor v19,v19,v18`, before `ext v19`).  out_p block-0 store readback
   = pt0 (captured at s320), block-1 = pt1 (captured at s363).  pt0/pt1 abbreviated
   to the spec forms word_xor cph_i (aes256_encrypt ctr_i keys).
   ------------------------------------------------------------------------- *)
