(* ========================================================================= *)
(* gcm_aesgcm_nblock_helpers.ml                                              *)
(*                                                                           *)
(* Generic N-block AES-GCM proof framework. Provides:                        *)
(*   - ghash_Nblock_karatsuba: the assembly-shape Karatsuba spec             *)
(*       parameterized over a list of (input, h_tw, hk) triples.             *)
(*   - GHASH_NBLOCK_KARATSUBA_EQ_PROP3: inductive bridge from the            *)
(*       assembly-shape spec to polyval_reduce_prop3 of the batched form     *)
(*       (which equals ghash_polyval_acc by GHASH_POLYVAL_ACC_BATCHED). Each *)
(*       per-N proof file derives its own GHASH_kBLOCK_..._EQ_POLYVAL_ACC    *)
(*       bridge from this.                                                   *)
(*   - The symmetric h-power normalizers POLYVAL_DOT_H4_EQ_LOCAL..H8_EQ.     *)
(*       (The GHASH_POLYVAL_ACC_1..8 family lives in gcm_aesgcm_helpers.ml.) *)
(*   - Per-block named tactics: ABBREV_FINAL_XI_TAC, GCM_NBLOCK_CT_STEP_TAC, *)
(*     GCM_NBLOCK_POST_AES/TAIL_DISPATCH/POST_SIM_NORMALIZE_TAC.             *)
(*   - bubble_sort_conv (XOR-AC canonicaliser for the GHASH closure).        *)
(*   - Shared LANE/CTR/BYTEREVERSE/gcm_ctr_inc lemmas.                       *)
(*                                                                           *)
(* Each per-N proof file hand-writes its own GHASH closure                   *)
(* (GCM_kBLOCK_GHASH_STEP_TAC) using the atoms/pmuls/qS/qB/bubble_sort       *)
(* pattern; there is intentionally no single generic GHASH-closure tactic.   *)
(*                                                                           *)
(* The key inductive step:                                                   *)
(*   ghash_Nblock_karatsuba (CONS triple rest) acc =                         *)
(*     ghash_Nblock_karatsuba rest (xor_triple acc triple)                   *)
(* where each triple contributes pl⊕ph⊕pm to the running accumulator.        *)
(* The base case rest = [] applies the SHARED Barrett reduction.             *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_aesgcm_helpers.ml";;

(* ========================================================================= *)
(* COUNTER-INCREMENT HELPER (N≥2)                                            *)
(* gcm_ctr_inc, LANE0..3 byte-join, CTR_WORD_INSERT, BYTEREVERSE_JOIN_FOLD   *)
(* These describe the AES counter increment via REV32+ADD+REV32 byte chain.  *)
(* ========================================================================= *)

let gcm_ctr_inc = new_definition
 `gcm_ctr_inc (ivec:(128)word) : (128)word =
   word_insert ivec (96,32)
     (word_bytereverse
        (word_add (word_bytereverse
                     (word_subword ivec (96,32):(32)word))
                  (word 1:(32)word)))`;;

let LANE0_BYTES_JOIN = prove
 (`!a:(128)word.
    (word_join
     (word_join (word_subword a (24,8):(8)word)
                (word_subword a (16,8):(8)word):(16)word)
     (word_join (word_subword a (8,8):(8)word)
                (word_subword a (0,8):(8)word):(16)word)) :(32)word =
    word_subword a (0,32):(32)word`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let LANE1_BYTES_JOIN = prove
 (`!a:(128)word.
    (word_join
     (word_join (word_subword a (56,8):(8)word)
                (word_subword a (48,8):(8)word):(16)word)
     (word_join (word_subword a (40,8):(8)word)
                (word_subword a (32,8):(8)word):(16)word)) :(32)word =
    word_subword a (32,32):(32)word`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let LANE2_BYTES_JOIN = prove
 (`!a:(128)word.
    (word_join
     (word_join (word_subword a (88,8):(8)word)
                (word_subword a (80,8):(8)word):(16)word)
     (word_join (word_subword a (72,8):(8)word)
                (word_subword a (64,8):(8)word):(16)word)) :(32)word =
    word_subword a (64,32):(32)word`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let LANE3_BYTES_JOIN_BE = prove
 (`!a:(128)word.
    (word_join
     (word_join (word_subword a (96,8):(8)word)
                (word_subword a (104,8):(8)word):(16)word)
     (word_join (word_subword a (112,8):(8)word)
                (word_subword a (120,8):(8)word):(16)word)) :(32)word =
    word_bytereverse (word_subword a (96,32):(32)word)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let CTR_WORD_INSERT = prove
 (`!a:(128)word. !x:(32)word.
    word_join
     (word_join x (word_subword a (64,32):(32)word):(64)word)
     (word_join (word_subword a (32,32):(32)word)
                (word_subword a (0,32):(32)word):(64)word) :(128)word =
    word_insert a (96,32) x`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let BYTEREVERSE_JOIN_FOLD = prove
 (`!a:(32)word.
     word_join (word_join (word_subword a (0,8):(8)word)
                          (word_subword a (8,8):(8)word):(16)word)
               (word_join (word_subword a (16,8):(8)word)
                          (word_subword a (24,8):(8)word):(16)word):(32)word =
     word_bytereverse a`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Post-b9a430b the ARM simulator emits `word_reversefields 8` (not          *)
(* `word_bytereverse`) for the 32-bit REV counter shuffle.  On 32-bit words  *)
(* the two are identical; this bridge normalizes the counter folds back to   *)
(* the `word_bytereverse` form the CTR tactics were written against.         *)
let WORD_REVERSEFIELDS_8_BYTEREVERSE_32 = prove
 (`!x:(32)word. word_reversefields 8 x = word_bytereverse x`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ========================================================================= *)
(* GENERIC N-BLOCK KARATSUBA SPEC                                            *)
(*                                                                           *)
(* ghash_Nblock_karatsuba : (int128 list) -> int128 -> int128 -> int128      *)
(*                                                                           *)
(*   The assembly-shape recursive spec.                                      *)
(*   Each block contributes (pl, ph, pm) computed from its (input, h_tw, hk) *)
(*   triple; all triples are XOR-summed; then SHARED Barrett reduction.      *)
(*                                                                           *)
(* Note: in the actual assembly, the per-block hk_lo is fetched from         *)
(* `karatsuba_mid (h_power h k)` (precomputed in Htable). The spec captures  *)
(* this via the precondition `subword hk_k (0,64) = karatsuba_mid h_k`.      *)
(*                                                                           *)
(* INPUT LAYOUT:                                                             *)
(*   triples = [(input_1, h_tw_1, hk_1); (input_2, h_tw_2, hk_2); ...]       *)
(*   where:                                                                  *)
(*     input_k = the kth GHASH input block (already XOR'd with running acc   *)
(*               for the first block by the caller)                          *)
(*     h_tw_k  = byteswap128 (h^{N-k+1})  -- the H power for this block      *)
(*     hk_k    = the Karatsuba-mid key for h_tw_k                            *)
(* ========================================================================= *)

(* Karatsuba (pl_k, ph_k, pm_k) for a single block. *)
let karatsuba_block_pl = new_definition
 `karatsuba_block_pl (input:int128) (h_tw:int128) : int128 =
  word_pmul (word_subword input (0,64) :64 word)
            (word_subword h_tw (64,64) :64 word)`;;

let karatsuba_block_ph = new_definition
 `karatsuba_block_ph (input:int128) (h_tw:int128) : int128 =
  word_pmul (word_subword input (64,64) :64 word)
            (word_subword h_tw (0,64) :64 word)`;;

let karatsuba_block_pm = new_definition
 `karatsuba_block_pm (input:int128) (hk:int128) : int128 =
  word_pmul
    (word_xor (word_subword input (0,64) :64 word)
              (word_subword input (64,64) :64 word))
    (word_subword hk (0,64) :64 word)`;;

(* The recursive XOR-sum of (pl, ph, pm) across all blocks. *)
let kara_acc = define
 `(kara_acc ([]:(int128#int128#int128)list) (pl_acc:int128) (ph_acc:int128)
            (pm_acc:int128) = (pl_acc, ph_acc, pm_acc)) /\
  (kara_acc (CONS (input,h_tw,hk) rest) pl_acc ph_acc pm_acc =
    kara_acc rest
      (word_xor pl_acc (karatsuba_block_pl input h_tw))
      (word_xor ph_acc (karatsuba_block_ph input h_tw))
      (word_xor pm_acc (karatsuba_block_pm input hk)))`;;

(* The shared Barrett reduction taking the accumulated (pl, ph, pm) triple
   and producing the final 128-bit GHASH digest. This mirrors the let-chain
   in ghash_1block_karatsuba (in gcm_one_block_closers.ml) and the
   matching let-chain in ghash_2block_karatsuba. *)
let karatsuba_reduce_shared = new_definition
 `karatsuba_reduce_shared (pl:int128) (ph:int128) (pm:int128) : int128 =
  let mid:int128 = word_xor (word_xor pm ph) pl in
  let a:64 word = word_subword pl (0,64) in
  let b:64 word = word_xor (word_subword pl (64,64)) (word_subword mid (0,64)) in
  let c:64 word = word_xor (word_subword ph (0,64)) (word_subword mid (64,64)) in
  let d:64 word = word_subword ph (64,64) in
  let w:64 word = word 13979173243358019584 in
  let wa:128 word = word_pmul a w in
  let wa_lo:64 word = word_subword wa (0,64) in
  let wa_hi:64 word = word_subword wa (64,64) in
  let v:64 word = word_xor b wa_lo in
  let u:64 word = word_xor (word_xor c a) wa_hi in
  let wv:128 word = word_pmul v w in
  let wv_lo:64 word = word_subword wv (0,64) in
  let wv_hi:64 word = word_subword wv (64,64) in
  let f:64 word = word_xor u wv_lo in
  let g:64 word = word_xor (word_xor d v) wv_hi in
  word_reversefields 8 (word_join g f : 128 word)`;;

(* The full N-block assembly-shape spec: accumulate Karatsuba triples,
   then apply the shared Barrett reduction. *)
let ghash_Nblock_karatsuba = new_definition
 `ghash_Nblock_karatsuba (triples:(int128#int128#int128)list) : int128 =
  let pl,ph,pm = kara_acc triples (word 0) (word 0) (word 0) in
  karatsuba_reduce_shared pl ph pm`;;

(* ========================================================================= *)
(* INDUCTIVE BRIDGE                                                          *)
(*                                                                           *)
(* GHASH_NBLOCK_KARATSUBA_EQ_PROP3 is proved BY INDUCTION on the block list  *)
(* via three structural lemmas:                                              *)
(*                                                                           *)
(*   1. KARATSUBA_REDUCE_AS_PROP3_CLEAN:                                     *)
(*      karatsuba_reduce_shared pl ph pm =                                   *)
(*        word_reversefields 8 (polyval_reduce_prop3 (pack_corrected ...))   *)
(*      (i.e., the assembly-shape Barrett reduction equals prop3 on the      *)
(*       Karatsuba-corrected packed value, modulo a final byte-reversal.)    *)
(*                                                                           *)
(*   2. KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN:                                 *)
(*      pack_corrected (pl_k, ph_k, pm_k) = pmul input_k h_k (256-bit)       *)
(*      under the precondition that hk's low half = karatsuba_mid h_k.       *)
(*                                                                           *)
(*   3. PACK_CORRECTED_XOR (additivity / linearity):                         *)
(*      pack_corrected commutes with XOR in all three arguments.             *)
(*                                                                           *)
(* From these three the inductive bridge follows: kara_acc XOR-folds         *)
(* per-block (pl, ph, pm); pack distributes over XOR; each block contributes *)
(* pmul input_k h_k; the total equals XOR of pmul input_k h_k; then          *)
(* karatsuba_reduce_shared = prop3 on this total.                            *)
(*                                                                           *)
(* The N=1, 2, 3, ..., 8 bridges are derived from this inductive bridge      *)
(* + GHASH_POLYVAL_ACC_<N> (from gcm_aesgcm_helpers.ml).                     *)
(* ========================================================================= *)

(* Pack-corrected: combines (pl, ph, pm) into the 256-bit Karatsuba layout
   (with mid corrected by ⊕ pl ⊕ ph). *)
let pack_corrected = new_definition
 `pack_corrected (pl:int128) (ph:int128) (pm:int128) :256 word =
   word_xor (word_xor
     (word_zx pl :256 word)
     (word_shl (word_zx (word_xor (word_xor pl ph) pm) :256 word) 64))
    (word_shl (word_zx ph :256 word) 128)`;;

(* Lemma 1: structural identity karatsuba_reduce_shared = prop3 ∘ pack_corrected *)
let KARATSUBA_REDUCE_AS_PROP3 = prove
 (`!pl ph pm:int128.
    karatsuba_reduce_shared pl ph pm =
    word_reversefields 8 (polyval_reduce_prop3
      (word_xor (word_xor
        (word_zx pl :256 word)
        (word_shl (word_zx (word_xor (word_xor pl ph) pm) :256 word) 64))
       (word_shl (word_zx ph :256 word) 128)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[karatsuba_reduce_shared; polyval_reduce_prop3;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[KARATSUBA_LIMBS] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  ABBREV_TAC `(plL:(64)word) = word_subword (pl:(128)word) (0,64)` THEN
  ABBREV_TAC `(plH:(64)word) = word_subword (pl:(128)word) (64,64)` THEN
  ABBREV_TAC `(phL:(64)word) = word_subword (ph:(128)word) (0,64)` THEN
  ABBREV_TAC `(phH:(64)word) = word_subword (ph:(128)word) (64,64)` THEN
  ABBREV_TAC `(pmL:(64)word) = word_subword (pm:(128)word) (0,64)` THEN
  ABBREV_TAC `(pmH:(64)word) = word_subword (pm:(128)word) (64,64)` THEN
  SUBGOAL_THEN
    `word_xor (word_xor (plH:(64)word)
                (word_xor (word_xor pmL phL) plL))
              (word_subword (word_pmul plL
                              (word 13979173243358019584:(64)word):(128)word)
                            (0,64):(64)word) =
     word_xor (word_xor plH
                (word_xor (word_xor plL phL) pmL))
              (word_subword (word_pmul plL
                              (word 13979173243358019584:(64)word):(128)word)
                            (0,64):(64)word):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
    `qBig = word_pmul (word_xor (plH:(64)word)
                         (word_xor (word_xor plL phL) pmL))
                      (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC
    `qSmall = word_pmul (plL:(64)word)
                        (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC `qBigL = word_subword (qBig:(128)word) (0,64):(64)word` THEN
  ABBREV_TAC `qBigH = word_subword (qBig:(128)word) (64,64):(64)word` THEN
  ABBREV_TAC `qSmallL = word_subword (qSmall:(128)word) (0,64):(64)word` THEN
  ABBREV_TAC `qSmallH = word_subword (qSmall:(128)word) (64,64):(64)word` THEN
  BINOP_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE]);;

let KARATSUBA_REDUCE_AS_PROP3_CLEAN = prove
 (`!pl ph pm:int128.
    karatsuba_reduce_shared pl ph pm =
    word_reversefields 8 (polyval_reduce_prop3 (pack_corrected pl ph pm))`,
  REWRITE_TAC[pack_corrected; KARATSUBA_REDUCE_AS_PROP3]);;

(* Lemma 2: per-block pack identity *)
let KARATSUBA_BLOCK_PACKS_TO_PMUL = prove
 (`!(input:int128) (h:int128) (hk:int128).
    word_subword hk (0,64):(64)word = karatsuba_mid h
    ==>
    (word_xor (word_xor
        (word_zx (karatsuba_block_pl input (byteswap128 h)) :256 word)
        (word_shl (word_zx (word_xor (word_xor
            (karatsuba_block_pl input (byteswap128 h))
            (karatsuba_block_ph input (byteswap128 h)))
          (karatsuba_block_pm input hk)) :256 word) 64))
       (word_shl (word_zx (karatsuba_block_ph input (byteswap128 h)) :256 word) 128)) =
    word_pmul input h : 256 word`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[karatsuba_block_pl; karatsuba_block_ph; karatsuba_block_pm;
              BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  ASM_REWRITE_TAC[karatsuba_mid] THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `(p1:(128)word) = word_pmul (word_subword (input:(128)word) (0,64):(64)word)
                                          (word_subword (h:(128)word) (0,64):(64)word)` THEN
  ABBREV_TAC `(p2:(128)word) = word_pmul (word_subword (input:(128)word) (64,64):(64)word)
                                          (word_subword (h:(128)word) (64,64):(64)word)` THEN
  ABBREV_TAC `(p3:(128)word) = word_pmul
                                  (word_xor (word_subword (input:(128)word) (0,64):(64)word)
                                            (word_subword (input:(128)word) (64,64):(64)word))
                                  (word_xor (word_subword (h:(128)word) (0,64):(64)word)
                                            (word_subword (h:(128)word) (64,64):(64)word))` THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC WORD_RULE);;

let KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN = prove
 (`!(input:int128) (h:int128) (hk:int128).
    word_subword hk (0,64):(64)word = karatsuba_mid h
    ==>
    pack_corrected
      (karatsuba_block_pl input (byteswap128 h))
      (karatsuba_block_ph input (byteswap128 h))
      (karatsuba_block_pm input hk) =
    word_pmul input h : 256 word`,
  REWRITE_TAC[pack_corrected; KARATSUBA_BLOCK_PACKS_TO_PMUL]);;

(* Lemma 3: pack_corrected is XOR-additive in each argument *)
let PACK_CORRECTED_XOR = prove
 (`!pl1 ph1 pm1 pl2 ph2 pm2:int128.
   pack_corrected (word_xor pl1 pl2) (word_xor ph1 ph2) (word_xor pm1 pm2) =
   word_xor (pack_corrected pl1 ph1 pm1) (pack_corrected pl2 ph2 pm2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pack_corrected; WORD_ZX_XOR; WORD_SHL_XOR] THEN
  CONV_TAC WORD_RULE);;

(* Linearity of kara_acc: starting at non-zero (pl0, ph0, pm0) is the same as
   starting at (0,0,0) and XOR-ing the result with the start. *)
let KARA_ACC_CONS_DESTR = prove
 (`!input h_tw hk rest pl0 ph0 pm0.
    kara_acc (CONS (input,h_tw,hk) rest) pl0 ph0 pm0 =
    kara_acc rest
      (word_xor pl0 (karatsuba_block_pl input h_tw))
      (word_xor ph0 (karatsuba_block_ph input h_tw))
      (word_xor pm0 (karatsuba_block_pm input hk))`,
  REWRITE_TAC[kara_acc]);;

let KARA_ACC_FIRST = prove
 (`!triples (pl0:int128) (ph0:int128) (pm0:int128).
    kara_acc triples pl0 ph0 pm0 =
    (let (pl', ph', pm') = kara_acc triples (word 0) (word 0) (word 0) in
     (word_xor pl0 pl', word_xor ph0 ph', word_xor pm0 pm'))`,
  MATCH_MP_TAC list_INDUCT THEN
  CONJ_TAC THENL
   [REWRITE_TAC[kara_acc; LET_DEF; LET_END_DEF; WORD_XOR_0];
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`input:int128`; `h_tw:int128`; `hk:int128`;
                        `rest:(int128#int128#int128)list`] THEN
    DISCH_TAC THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[KARA_ACC_CONS_DESTR] THEN
    FIRST_X_ASSUM(fun ih ->
      ONCE_REWRITE_TAC[ih] THEN
      MP_TAC(SPECL [`word_xor (word 0:int128)
                              (karatsuba_block_pl input h_tw)`;
                    `word_xor (word 0:int128)
                              (karatsuba_block_ph input h_tw)`;
                    `word_xor (word 0:int128)
                              (karatsuba_block_pm input hk)`] ih)) THEN
    REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN(fun th ->
      ABBREV_TAC `acc_zero = kara_acc rest (word 0:int128) (word 0:int128) (word 0:int128)` THEN
      MP_TAC th) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    SPEC_TAC(`acc_zero:int128#int128#int128`,`q:int128#int128#int128`) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[PAIR_EQ] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE]);;

(* Quad-list = (input, h_tw, hk, h_true) per block. Used to express the bridge
   precondition (every triple must come from a real `h` with byteswap128 + mid). *)
let kara_quad_pmul = define
  `(kara_quad_pmul ([]:(int128#int128#int128#int128)list) (acc:256 word) = acc) /\
   (kara_quad_pmul (CONS (input,h_tw,hk,h) qrest) acc =
     kara_quad_pmul qrest (word_xor acc (word_pmul input h:256 word)))`;;

let kara_quad_ok = define
  `(kara_quad_ok ([]:(int128#int128#int128#int128)list) <=> T) /\
   (kara_quad_ok (CONS (input,h_tw,hk,h) qrest) <=>
     h_tw = byteswap128 h /\
     word_subword hk (0,64):(64)word = karatsuba_mid h /\
     kara_quad_ok qrest)`;;

let project_triples = define
  `(project_triples ([]:(int128#int128#int128#int128)list) = []:(int128#int128#int128)list) /\
   (project_triples (CONS (input,h_tw,hk,h) qrest) =
     CONS (input,h_tw,hk) (project_triples qrest))`;;

(* The key inductive helper: kara_acc on the projected triples, packed,
   equals kara_quad_pmul (XOR of pmul input_k h_k). *)
let KARA_ACC_PACK_HELPER = prove
 (`!quads (acc:256 word).
    kara_quad_ok quads
    ==>
    (let pl,ph,pm = kara_acc (project_triples quads)
                              (word 0:int128) (word 0:int128) (word 0:int128) in
     kara_quad_pmul quads acc = word_xor acc (pack_corrected pl ph pm))`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[kara_quad_ok; project_triples; kara_quad_pmul; kara_acc;
                LET_DEF; LET_END_DEF; pack_corrected;
                WORD_ZX_0; WORD_SHL_ZERO; WORD_XOR_0] THEN
    GEN_TAC THEN CONV_TAC WORD_BLAST;
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`input:int128`; `h_tw:int128`; `hk:int128`;
                        `h:int128`; `qrest:(int128#int128#int128#int128)list`] THEN
    DISCH_TAC THEN GEN_TAC THEN
    REWRITE_TAC[kara_quad_ok; kara_quad_pmul; project_triples;
                KARA_ACC_CONS_DESTR; WORD_XOR_0_LEFT; WORD_XOR_0] THEN
    STRIP_TAC THEN
    ONCE_REWRITE_TAC[KARA_ACC_FIRST] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `word_xor (acc:256 word)
                                          (word_pmul (input:int128) (h:int128):256 word)`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    SPEC_TAC(`kara_acc (project_triples (qrest:(int128#int128#int128#int128)list))
                       (word 0:int128) (word 0:int128) (word 0:int128)`,
             `q:int128#int128#int128`) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`pl':int128`; `ph':int128`; `pm':int128`] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`input:int128`; `h:int128`; `hk:int128`]
                 KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM PACK_CORRECTED_XOR] THEN
    REWRITE_TAC[PACK_CORRECTED_XOR] THEN
    CONV_TAC WORD_RULE]);;

(* THE INDUCTIVE BRIDGE *)
let GHASH_NBLOCK_KARATSUBA_EQ_PROP3 = prove
 (`!quads.
    kara_quad_ok quads
    ==>
    ghash_Nblock_karatsuba (project_triples quads) =
    word_reversefields 8
      (polyval_reduce_prop3 (kara_quad_pmul quads (word 0:256 word)))`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ghash_Nblock_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[KARATSUBA_REDUCE_AS_PROP3_CLEAN] THEN
  MP_TAC(SPECL [`quads:(int128#int128#int128#int128)list`; `word 0:256 word`]
               KARA_ACC_PACK_HELPER) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  SPEC_TAC(`kara_acc (project_triples (quads:(int128#int128#int128#int128)list))
                     (word 0:int128) (word 0:int128) (word 0:int128)`,
           `q:int128#int128#int128`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`pl:int128`; `ph:int128`; `pm:int128`] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[WORD_XOR_0_LEFT]);;

(* Per-block prefix tactic for the AES round simulation + s13 abbreviation.  *)
(* In the actual proof body, this expands to:                                *)
(*   ARM_STEPS_TAC EXEC (start--end) THEN                                    *)
(*   GCM_ENC_SIMPLIFY_TAC THEN                                               *)
(*   ABBREV_TAC `s13_k = aese (aesmc (aese ... (aese ivec_k rk0)) ... rk13)` *)
(*                                                                           *)
(* But because the AES chain term is huge (~14 lines of nested aese/aesmc),  *)
(* we provide a generator that builds it on demand from the round-key list.  *)
(* ------------------------------------------------------------------------- *)

(* ABBREV_FINAL_XI_TAC : tactic                                              *)
(*   Abbreviate Q19 (the assembled Karatsuba+Barrett result) as `final_xi`.  *)
(*   Insert in the main proof BEFORE the EXT/REV64/STR steps to avoid        *)
(*   byte-level term explosion.                                              *)
let ABBREV_FINAL_XI_TAC : tactic =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read Q19 (s:armstate) = (x:int128)`) (concl th)
    then let rhs = rand(concl th) in
         ABBREV_TAC(mk_eq(mk_var("final_xi",type_of rhs), rhs))
    else NO_TAC);;

(* Post-simulation assumption cleanup before the final state: normalize      *)
(* stack/pointer arithmetic, masks, XOR association, and the SIMD shuffles.  *)
let GCM_NBLOCK_POST_SIM_NORMALIZE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_AND_MASK; WORD_AND_MASK_SYM;
    WORD_AND_MASK_64; WORD_AND_MASK_SYM_64;
    WORD_XOR_ASSOC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0; KAR_MID_BRIDGE]) THEN
  SIMD_SIMPLIFY_ASSUM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SWAP_HALVES_INVOLUTION]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    with _ -> th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_XOR_ASSOC]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV PMUL_NORM_CONV)) th
    with _ -> th);;

(* ========================================================================= *)
(* PER-BLOCK CIPHERTEXT CLOSURE                                              *)
(*                                                                           *)
(* GCM_NBLOCK_CT_STEP_TAC k : closes `ct_k = pt_k ⊕ aes256(ivec_k, ...)`     *)
(*   via EXPAND_TAC ct_k + EXPAND_TAC s13_k + WORD_XOR_ASSOC + ASM_REWRITE.  *)
(*   For k=1: ivec_k = ivec.                                                 *)
(*   For k≥2: ivec_k = gcm_ctr_inc^{k-1} ivec — needs LANE/CTR chain.        *)
(* ========================================================================= *)

(* Build "ct" or "ct_k", "s13" or "s13_k" name strings. By convention:       *)
(*   1-block: `ct`, `s13`        (no suffix)                                 *)
(*   N-block (N≥2): `ct_k`, `s13_k` for k = 1..N                             *)
let mk_ct_name (n:int) (k:int) : string =
  if n = 1 then "ct" else "ct" ^ string_of_int k;;
let mk_s13_name (n:int) (k:int) : string =
  if n = 1 then "s13" else "s13_" ^ string_of_int k;;

(* For the 1st block (k=1, ivec_k = ivec): no LANE/CTR chain needed. *)
let GCM_NBLOCK_CT1_STEP_TAC (n:int) : tactic =
  let ct = mk_ct_name n 1 and s13 = mk_s13_name n 1 in
  EXPAND_TAC ct THEN EXPAND_TAC s13 THEN
  REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN
  ASM_REWRITE_TAC[];;

(* --- Counter-insert lemmas (used by the ct>=3 folds in the GHASH step) ----- *)

let INSERT_IDEM = prove
 (`!(x:(128)word) (y:(32)word) (z:(32)word).
     (word_insert:(128)word->num#num->(32)word->(128)word)
     (word_insert x (96,32) y) (96,32) z = word_insert x (96,32) z`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let INSERT_SUBWORD = prove
 (`!(x:(128)word) (y:(32)word).
     word_subword
     ((word_insert:(128)word->num#num->(32)word->(128)word) x (96,32) y)
     (96,32):(32)word = y`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* For block k≥2: ivec_k = gcm_ctr_inc^{k-1} ivec, needs the LANE/CTR chain. *)
(* The shared front-half (substitute ct_k / s13_k, unfold aes256_encrypt,    *)
(* peel to the ivec argument, apply LANE0..3 + CTR_WORD_INSERT) is identical *)
(* for all k. The TAIL then differs by counter depth:                        *)
(*   k=2 (ivec_2 = gcm_ctr_inc ivec): one unfold, fold via BYTEREVERSE_JOIN. *)
(*   k≥3 (ivec_k = gcm_ctr_inc^{k-1} ivec): abbreviate ctr_k/br_k/step1_k,   *)
(*     then INSERT_SUBWORD/INSERT_IDEM collapse the nested word_inserts and  *)
(*     double-byte-reverse cancels.                                          *)
(* This generalizes the per-file GCM_CT3..CTk_STEP_TAC so each proof just    *)
(* calls GCM_NBLOCK_CT_STEP_TAC n k (one line per block, like CT1/CT2).      *)
let GCM_NBLOCK_CT_LATER_STEP_TAC (n:int) (k:int) : tactic =
  if k <= 1 then failwith "GCM_NBLOCK_CT_LATER_STEP_TAC: k must be ≥ 2"
  else
  let ct = mk_ct_name n k and s13 = mk_s13_name n k in
  let ct_tm = mk_var(ct, `:(128)word`)
  and s13_tm = mk_var(s13, `:(128)word`) in
  (* k≥3 fresh abbreviation variables, named by block index *)
  let ctr = mk_var("ctr"^string_of_int k, `:(32)word`)
  and br = mk_var("br"^string_of_int k, `:(32)word`)
  and step1 = mk_var("step1_"^string_of_int k, `:(32)word`) in
  let ctr_def   = mk_eq(ctr, `word_subword (ivec:(128)word) (96,32):(32)word`) in
  let br_def    = mk_eq(br, mk_comb(`word_bytereverse:(32)word->(32)word`, ctr)) in
  let step1_def = mk_eq(step1,
    `word_bytereverse (word_add (word_bytereverse (word_subword (ivec:(128)word) (96,32):(32)word)) (word 1:(32)word)):(32)word`) in
  (* the shared front-half: substitute ct_k, unfold AES, peel to ivec arg.
     June-2026 base: the goal is `ct_k = word_xor pt_k (aes256_encrypt ...)`
     (ct on LHS), the ct_k defining assumption is LEFT-associated
     `word_xor (word_xor pt_k s13_k) rk14 = ct_k`, WORD_XOR_ASSOC normalizes to
     left, and the 32-bit REV counter shuffle emits word_reversefields 8 (not
     word_bytereverse).  Orient with SYM_CONV, accept either ct-association,
     peel THM/TERM/TERM (left-assoc), and bridge the counter identity. *)
  CONV_TAC SYM_CONV THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = ct_tm &&
       (try
         match lhs(concl th) with
         | Comb(Comb(Const("word_xor",_), _),
                Comb(Comb(Const("word_xor",_), s13_arg), _)) -> s13_arg = s13_tm
         | Comb(Comb(Const("word_xor",_),
                Comb(Comb(Const("word_xor",_), _), s13_arg)), _) -> s13_arg = s13_tm
         | _ -> false
        with _ -> false)
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[AES256_ENCRYPT_UNFOLD] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = s13_tm &&
       not(try fst(dest_const(rator(rator(lhs(concl th))))) = "read"
           with _ -> false)
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN;
              LANE2_BYTES_JOIN; LANE3_BYTES_JOIN_BE;
              CTR_WORD_INSERT] THEN
  REWRITE_TAC[gcm_ctr_inc] THEN
  (if k = 2 then
     REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
     REWRITE_TAC[WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
     REWRITE_TAC[GSYM CTR_WORD_INSERT] THEN
     REWRITE_TAC[BYTEREVERSE_JOIN_FOLD]
   else
     (* k≥3: collapse the gcm_ctr_inc^{k-1} nest.  June base: after the rev
        bridge the goal is a word_join=word_insert counter identity; fold the
        LHS word_join back to word_insert (GSYM CTR_WORD_INSERT), peel both
        word_join layers to the 32-bit top field, then close arithmetically. *)
     REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
     REWRITE_TAC[WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
     ABBREV_TAC ctr_def THEN ABBREV_TAC br_def THEN ABBREV_TAC step1_def THEN
     REWRITE_TAC[BYTEREVERSE_JOIN_FOLD; INSERT_SUBWORD; INSERT_IDEM] THEN
     REWRITE_TAC[GSYM CTR_WORD_INSERT] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     EXPAND_TAC ("step1_"^string_of_int k) THEN
     REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
     AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* Top-level entry: closes the kth ciphertext subgoal. *)
let GCM_NBLOCK_CT_STEP_TAC (n:int) (k:int) : tactic =
  if k = 1 then GCM_NBLOCK_CT1_STEP_TAC n
  else GCM_NBLOCK_CT_LATER_STEP_TAC n k;;

(* ========================================================================= *)
(*  SHARED PER-N PROOF HELPERS (hoisted here so the N-block proof files do   *)
(*  not each re-prove them).  Used by two_/three_/.../eight_blocks proofs.   *)
(* ========================================================================= *)

(* ---- Symmetric h-power normalizers -------------------------------------- *)
(* GHASH_POLYVAL_ACC_N emits left-associated h-powers (((h.h).h)..); the     *)
(* karatsuba bridge wants the symmetric forms the Htable holds.  H4 is the   *)
(* one nontrivial ring-algebra proof; H5..H8 follow by congruence.           *)

let POLYVAL_DOT_H4_EQ_LOCAL = prove
 (`!(h:int128).
     polyval_dot (polyval_dot (polyval_dot h h) h) h =
     polyval_dot (polyval_dot h h) (polyval_dot h h)`,
  GEN_TAC THEN
  MATCH_MP_TAC(ISPEC `256` MOD_POLYVAL_CANCEL_VARPOW) THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
   `ring_mul bool_poly
      (ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
                          (poly_of_word (h:int128)))
      (poly_of_word (h:int128))` THEN
  CONJ_TAC THENL [
    MP_TAC(ISPECL [`polyval_dot (polyval_dot (h:int128) h) h`; `h:int128`]
      POLYVAL_DOT_CORRECT) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`polyval_dot (h:int128) h`; `h:int128`]
      POLYVAL_DOT_CORRECT) THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `ring_pow bool_poly (poly_var bool_ring (one:1)) 256 =
       ring_mul bool_poly (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)
                          (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)`
      SUBST1_TAC THENL
     [MP_TAC(ISPECL [`bool_poly`; `poly_var bool_ring (one:1)`; `128`; `128`]
        RING_POW_ADD) THEN
      REWRITE_TAC[POLY_VAR_BOOL_POLY; ARITH_RULE `128+128=256`] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `ring_mul bool_poly
         (poly_of_word (polyval_dot (polyval_dot (polyval_dot (h:int128) h) h) h))
         (ring_mul bool_poly (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)
                             (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)) =
       ring_mul bool_poly
         (ring_mul bool_poly
            (poly_of_word (polyval_dot (polyval_dot (polyval_dot (h:int128) h) h) h))
            (ring_pow bool_poly (poly_var bool_ring (one:1)) 128))
         (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)`
      SUBST1_TAC THENL
     [MATCH_MP_TAC RING_MUL_ASSOC THEN
      REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY]; ALL_TAC] THEN
    MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
    EXISTS_TAC
     `ring_mul bool_poly
        (ring_mul bool_poly (poly_of_word (polyval_dot (polyval_dot (h:int128) h) h))
                            (poly_of_word (h:int128)))
        (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)` THEN
    CONJ_TAC THENL [
      MATCH_MP_TAC(ISPECL
        [`ring_mul bool_poly
            (poly_of_word (polyval_dot (polyval_dot (polyval_dot (h:int128) h) h) h))
            (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)`;
         `ring_mul bool_poly (poly_of_word (polyval_dot (polyval_dot (h:int128) h) h))
            (poly_of_word (h:int128))`;
         `ring_pow bool_poly (poly_var bool_ring (one:1)) 128`;
         `ring_pow bool_poly (poly_var bool_ring (one:1)) 128`] MOD_POLYVAL_MUL) THEN
      CONJ_TAC THENL [
        FIRST_ASSUM MATCH_ACCEPT_TAC;
        REWRITE_TAC[MOD_POLYVAL_REFL; POLY_VARPOW_BOOL_POLY]]; ALL_TAC] THEN
    SUBGOAL_THEN
      `ring_mul bool_poly
         (ring_mul bool_poly (poly_of_word (polyval_dot (polyval_dot (h:int128) h) h))
                             (poly_of_word (h:int128)))
         (ring_pow bool_poly (poly_var bool_ring (one:1)) 128) =
       ring_mul bool_poly
         (ring_mul bool_poly (poly_of_word (polyval_dot (polyval_dot (h:int128) h) h))
                             (ring_pow bool_poly (poly_var bool_ring (one:1)) 128))
         (poly_of_word (h:int128))`
      SUBST1_TAC THENL
     [MP_TAC(ISPEC `bool_poly` RING_MUL_AC) THEN STRIP_TAC THEN
      ASM_MESON_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY]; ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL
      [`ring_mul bool_poly (poly_of_word (polyval_dot (polyval_dot (h:int128) h) h))
          (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)`;
       `ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h)) (poly_of_word (h:int128))`;
       `poly_of_word (h:int128)`; `poly_of_word (h:int128)`] MOD_POLYVAL_MUL) THEN
    CONJ_TAC THENL [
      FIRST_ASSUM MATCH_ACCEPT_TAC;
      REWRITE_TAC[MOD_POLYVAL_REFL; BOOL_POLY_OF_WORD]]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
  MP_TAC(ISPECL [`polyval_dot (h:int128) h`; `polyval_dot (h:int128) h`]
                POLYVAL_DOT_CORRECT) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:int128`; `h:int128`] POLYVAL_DOT_CORRECT) THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `ring_pow bool_poly (poly_var bool_ring (one:1)) 256 =
     ring_mul bool_poly (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)
                        (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)`
    SUBST1_TAC THENL
   [MP_TAC(ISPECL [`bool_poly`; `poly_var bool_ring (one:1)`; `128`; `128`]
      RING_POW_ADD) THEN
    REWRITE_TAC[POLY_VAR_BOOL_POLY; ARITH_RULE `128+128=256`] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `ring_mul bool_poly
       (poly_of_word (polyval_dot (polyval_dot (h:int128) h) (polyval_dot h h)))
       (ring_mul bool_poly (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)
                           (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)) =
     ring_mul bool_poly
       (ring_mul bool_poly
          (poly_of_word (polyval_dot (polyval_dot (h:int128) h) (polyval_dot h h)))
          (ring_pow bool_poly (poly_var bool_ring (one:1)) 128))
       (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC RING_MUL_ASSOC THEN
    REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY]; ALL_TAC] THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
   `ring_mul bool_poly
      (ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
                          (poly_of_word (polyval_dot (h:int128) h)))
      (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)` THEN
  CONJ_TAC THENL [
    MATCH_MP_TAC(ISPECL
      [`ring_mul bool_poly
          (poly_of_word (polyval_dot (polyval_dot (h:int128) h) (polyval_dot h h)))
          (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)`;
       `ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
          (poly_of_word (polyval_dot (h:int128) h))`;
       `ring_pow bool_poly (poly_var bool_ring (one:1)) 128`;
       `ring_pow bool_poly (poly_var bool_ring (one:1)) 128`] MOD_POLYVAL_MUL) THEN
    CONJ_TAC THENL [
      FIRST_ASSUM MATCH_ACCEPT_TAC;
      REWRITE_TAC[MOD_POLYVAL_REFL; POLY_VARPOW_BOOL_POLY]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul bool_poly
      (ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
                          (poly_of_word (polyval_dot (h:int128) h)))
      (ring_pow bool_poly (poly_var bool_ring (one:1)) 128) =
    ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
      (ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
                          (ring_pow bool_poly (poly_var bool_ring (one:1)) 128))`
    SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_MUL_ASSOC THEN
    REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul bool_poly
      (ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
                          (poly_of_word (h:int128)))
      (poly_of_word (h:int128)) =
    ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
      (ring_mul bool_poly (poly_of_word (h:int128)) (poly_of_word (h:int128)))`
    SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_MUL_ASSOC THEN
    REWRITE_TAC[BOOL_POLY_OF_WORD]; ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
    [`poly_of_word (polyval_dot (h:int128) h)`;
     `poly_of_word (polyval_dot (h:int128) h)`;
     `ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h))
        (ring_pow bool_poly (poly_var bool_ring (one:1)) 128)`;
     `ring_mul bool_poly (poly_of_word (h:int128)) (poly_of_word (h:int128))`]
    MOD_POLYVAL_MUL) THEN
  CONJ_TAC THENL [
    REWRITE_TAC[MOD_POLYVAL_REFL; BOOL_POLY_OF_WORD];
    FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let POLYVAL_DOT_H5_EQ = prove
 (`!(h:int128).
     polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h =
     polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h`,
  GEN_TAC THEN REWRITE_TAC[POLYVAL_DOT_H4_EQ_LOCAL]);;

let POLYVAL_DOT_H6_EQ = prove
 (`!(h:int128).
     polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h =
     polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h`,
  GEN_TAC THEN REWRITE_TAC[POLYVAL_DOT_H5_EQ]);;

let POLYVAL_DOT_H7_EQ = prove
 (`!(h:int128).
     polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h =
     polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h`,
  GEN_TAC THEN REWRITE_TAC[POLYVAL_DOT_H6_EQ]);;

let POLYVAL_DOT_H8_EQ = prove
 (`!(h:int128).
     polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) h =
     polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h`,
  GEN_TAC THEN REWRITE_TAC[POLYVAL_DOT_H7_EQ]);;

(* ---- Bubble-sort conversion for XOR canonical form ---------------------- *)
(* WORD_BITWISE_RULE blows up past ~17-21 atoms; this sorts word_xor chains  *)
(* string-lexicographically via pairwise commutativity.                      *)

let word_xor_left_comm = WORD_RULE
  `word_xor (a:64 word) (word_xor b c) = word_xor b (word_xor a c)`;;

let xor_pair_comm = WORD_RULE `word_xor (a:64 word) b = word_xor b a`;;

let term_leq t1 t2 = String.compare (string_of_term t1) (string_of_term t2) <= 0;;

let rec bubble_conv tm =
  match tm with
  | Comb(Comb(Const("word_xor",_), a), b) ->
    (match b with
     | Comb(Comb(Const("word_xor",_), b1), _) ->
       if term_leq a b1 then
         AP_TERM (mk_comb(rator(rator tm), a)) (bubble_conv b)
       else
         let th1 = PART_MATCH lhs word_xor_left_comm tm in
         let new_rhs = rhs(concl th1) in
         let inner = rand new_rhs in
         TRANS th1 (AP_TERM (rator new_rhs) (bubble_conv inner))
     | _ ->
       if term_leq a b then REFL tm
       else PART_MATCH lhs xor_pair_comm tm)
  | _ -> REFL tm;;

let rec bubble_sort_conv tm =
  let rec count_xors t =
    match t with
    | Comb(Comb(Const("word_xor",_), _), r) -> 1 + count_xors r
    | _ -> 0 in
  let n = count_xors tm in
  let rec apply_n_times k acc =
    if k <= 0 then acc
    else
      let th = bubble_conv (rhs(concl acc)) in
      apply_n_times (k-1) (TRANS acc th) in
  apply_n_times n (REFL tm);;

(* Iterate bubble_sort_conv to a fixpoint: keep re-sorting until the XOR     *)
(* chain is stable.  Shared by every N-block GHASH closer (folds word_pmul   *)
(* args up to AC so the final per-half sort sees abbreviated atoms on both   *)
(* sides).                                                                   *)
let rec bubble_fix tm =
  let th = bubble_sort_conv tm in
  let r = rhs(concl th) in
  if r = tm then th else TRANS th (bubble_fix r);;

(* ========================================================================= *)
(* PARTIAL-BLOCK MASK CONSTRUCTION (shared across all N-block proofs)        *)
(*                                                                           *)
(* In an N-block encrypt the final block may be partial: byte_len in 1..16   *)
(* bytes.  The routine builds a 128-bit mask in Q0 from the (mod-128) bit    *)
(* length via  and #127 ; sub #128 ; neg ; and #127 ; lsrv (all-ones >> n) ; *)
(* cmp #64 ; csel ; csel ; ins d0/d1, masks the last ciphertext block to its *)
(* low 8*byte_len bits, and (via bif) keeps the untouched output bytes above *)
(* the message end.  NBLOCK_MASK_REG shows the constructed register, in the  *)
(* exact ival/flag form the symbolic simulator produces, equals              *)
(* word (2^(8*byte_len) - 1).  The proof peels byte_len into its 16 values   *)
(* (a single 16-way ARITH_RULE disjunction is intractable).                  *)
(* ========================================================================= *)

let nblock_mask_red_tac =
  CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV ORELSEC INT_RED_CONV) THENC
           WORD_REDUCE_CONV THENC NUM_REDUCE_CONV);;

let nblock_cases16 lo =
  if lo = 16 then
    ARITH_RULE(Printf.sprintf "%d <= b /\\ b <= 16 ==> b = 16" lo |> parse_term)
  else
    ARITH_RULE(Printf.sprintf
      "%d <= b /\\ b <= 16 <=> b = %d \\/ (%d <= b /\\ b <= 16)" lo lo (lo+1)
      |> parse_term);;

let rec NBLOCK_MASK_PEEL_TAC lo =
  if lo = 16 then
    DISCH_THEN(fun th -> SUBST1_TAC(MATCH_MP (nblock_cases16 16) th)) THEN
    nblock_mask_red_tac
  else
    REWRITE_TAC[nblock_cases16 lo] THEN
    DISCH_THEN(DISJ_CASES_THEN (fun th ->
      (SUBST1_TAC th THEN nblock_mask_red_tac)
      ORELSE (MP_TAC th THEN NBLOCK_MASK_PEEL_TAC (lo+1))));;

(* Inserting both 64-bit lanes of a 128-bit register discards the original base. *)
let NBLOCK_WORD_INSERT_BOTH_LANES = prove
 (`!(b0:int128) (a:int64) (c:int64).
     word_insert ((word_insert b0 (0,64) a):int128) (64,64) c : int128 =
     word_join c a`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* The mask register built in Q0 (base b0 = whatever previously occupied Q0;
   both lanes are overwritten by the two csel results) equals
   word (2^(8*byte_len) - 1). *)
let NBLOCK_MASK_REG = prove
 (`!byte_len (b0:int128). 1 <= byte_len /\ byte_len <= 16 ==>
    (word_insert
     ((word_insert (b0:int128)
        (0,64)
        (if ~(ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64)) < &0 <=>
              ~(ival (word_and (word_sub (word 0) (word_sub (word_and (word (8*byte_len):int64) (word 127)) (word 128))) (word 127)) - &64 =
                ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64))))
         then word 18446744073709551615:int64
         else word_jushr (word 18446744073709551615:int64) (word_and (word_sub (word 0) (word_sub (word_and (word (8*byte_len):int64) (word 127)) (word 128))) (word 127)))):int128)
     (64,64)
     (if ~(ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64)) < &0 <=>
           ~(ival (word_and (word_sub (word 0) (word_sub (word_and (word (8*byte_len):int64) (word 127)) (word 128))) (word 127)) - &64 =
             ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64))))
        then word_jushr (word 18446744073709551615:int64) (word_and (word_sub (word 0) (word_sub (word_and (word (8*byte_len):int64) (word 127)) (word 128))) (word 127))
        else word 0:int64)
    : int128)
    = word (2 EXP (8 * byte_len) - 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NBLOCK_WORD_INSERT_BOTH_LANES] THEN
  NBLOCK_MASK_PEEL_TAC 1);;

(* Masking an already-masked block again with the same mask is idempotent. *)
let NBLOCK_MASK_IDEM = prove
 (`!(ct:int128) (mask:int128).
     word_and (word_and mask ct) mask = word_and ct mask`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* The returned byte length: x9 = total_bits >> 3 = total_bytes when
   total_bytes < 2^61 (always true here: total_bytes <= 112). *)
let NBLOCK_USHR_BYTELEN = prove
 (`!total_bytes. total_bytes <= 127
     ==> word_ushr (word (8 * total_bytes):int64) 3 = word total_bytes`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `val (word (8 * total_bytes):int64) = 8 * total_bytes` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ARITH_TAC);;

(* ival of a small nonnegative word literal (used to resolve the cascade
   block-count comparison with a symbolic partial byte_len). *)
let NBLOCK_IVAL_WORD_SMALL = prove
 (`!n. n < 2 EXP 63 ==> ival(word n:int64) = &n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word n:int64) = n` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ival(word n:int64) = &(val(word n:int64))` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_EQ_VAL THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;
