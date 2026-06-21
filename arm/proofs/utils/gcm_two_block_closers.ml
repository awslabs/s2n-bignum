(* ========================================================================= *)
(* Two-block GHASH / mask / cascade closers for the AES-256-GCM band proofs.  *)
(*                                                                           *)
(* Split out of the former gcm_branch_closers.ml.                            *)
(* Pure-algebra closers (no machine code, no symbolic simulation); shared    *)
(* by the standalone per-N proof and the single-binary band proof.           *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml";;

(* ===== TWO-BLOCK: Karatsuba bridge ======================================= *)
let ghash_2block_karatsuba = new_definition
 `ghash_2block_karatsuba (b1:int128) (b2:int128)
                         (h_tw:int128) (hk:int128)
                         (h2_tw:int128) (h2k:int128) : int128 =
  let b1_lo:64 word = word_subword b1 (0,64) in
  let b1_hi:64 word = word_subword b1 (64,64) in
  let h2_lo:64 word = word_subword h2_tw (0,64) in
  let h2_hi:64 word = word_subword h2_tw (64,64) in
  let h2k_lo:64 word = word_subword h2k (0,64) in
  let pl1:int128 = word_pmul b1_lo h2_hi in
  let ph1:int128 = word_pmul b1_hi h2_lo in
  let pm1:int128 = word_pmul (word_xor b1_lo b1_hi) h2k_lo in
  let b2_lo:64 word = word_subword b2 (0,64) in
  let b2_hi:64 word = word_subword b2 (64,64) in
  let h_lo:64 word = word_subword h_tw (0,64) in
  let h_hi:64 word = word_subword h_tw (64,64) in
  let hk_lo:64 word = word_subword hk (0,64) in
  let pl2:int128 = word_pmul b2_lo h_hi in
  let ph2:int128 = word_pmul b2_hi h_lo in
  let pm2:int128 = word_pmul (word_xor b2_lo b2_hi) hk_lo in
  let pl:int128 = word_xor pl1 pl2 in
  let ph:int128 = word_xor ph1 ph2 in
  let pm:int128 = word_xor pm1 pm2 in
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

(* ========================================================================= *)
(* RELATIONSHIP TO ghash_Nblock_karatsuba                                    *)
(*                                                                           *)
(* The N=2 instance of ghash_Nblock_karatsuba — applied to                   *)
(*   triples = [(b1, h_tw, hk); (b2, h2_tw, h2k)]                            *)
(* — is structurally equivalent to ghash_2block_karatsuba. We prove this    *)
(* compatibility theorem so the 2-block bridge can be derived from the      *)
(* generic inductive bridge.                                                  *)
(* ========================================================================= *)

(* Note the N-block aggregator XOR-folds (pl, ph, pm) using fresh names;
   ghash_2block_karatsuba uses inline pl1+pl2 etc. They are equal under
   simple unfolding. *)
let GHASH_2BLOCK_AS_NBLOCK = prove
 (`!(b1:int128) (b2:int128) (h_tw:int128) (hk:int128)
    (h2_tw:int128) (h2k:int128).
    ghash_Nblock_karatsuba [(b1, h2_tw, h2k); (b2, h_tw, hk)] =
    ghash_2block_karatsuba b1 b2 h_tw hk h2_tw h2k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ghash_Nblock_karatsuba; ghash_2block_karatsuba;
              kara_acc; karatsuba_block_pl; karatsuba_block_ph;
              karatsuba_block_pm; karatsuba_reduce_shared;
              LET_DEF; LET_END_DEF; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[]);;

(* ========================================================================= *)
(* PER-N BRIDGE: ghash_2block_karatsuba ↔ polyval_reduce_prop3                *)
(*                                                                           *)
(* The bridge GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC (proven below) is what    *)
(* the GHASH closure applies. It corresponds to the generic inductive bridge  *)
(* GHASH_NBLOCK_KARATSUBA_EQ_PROP3 specialised via GHASH_2BLOCK_AS_NBLOCK +    *)
(* GHASH_POLYVAL_ACC_2.                                                        *)
(* ========================================================================= *)

let GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC = prove
 (`!(b1:int128) (b2:int128) (h:int128) (hk:int128) (h2k:int128).
    word_subword hk (0,64):(64)word = karatsuba_mid h /\
    word_subword h2k (0,64):(64)word = karatsuba_mid (polyval_dot h h)
    ==> ghash_2block_karatsuba b1 b2 (byteswap128 h) hk
                                (byteswap128 (polyval_dot h h)) h2k =
        word_reversefields 8
          (polyval_reduce_prop3
            (word_xor (word_pmul b1 (polyval_dot h h) : 256 word)
                      (word_pmul b2 h : 256 word)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM GHASH_2BLOCK_AS_NBLOCK] THEN
  (* Equivalent quad-list form: [(b1, byteswap128(h^2), h2k, h^2);
                                  (b2, byteswap128(h),   hk,  h)]
     Note: project_triples extracts the first 3 fields of each quad. *)
  SUBGOAL_THEN
    `[(b1:int128, byteswap128 (polyval_dot h h):int128, h2k:int128);
      (b2:int128, byteswap128 h:int128, hk:int128)] =
     project_triples [(b1, byteswap128 (polyval_dot h h), h2k, polyval_dot h h);
                      (b2, byteswap128 h, hk, h)]`
    SUBST1_TAC THENL [REWRITE_TAC[project_triples]; ALL_TAC] THEN
  MP_TAC(SPEC `[(b1:int128, byteswap128 (polyval_dot h h):int128, h2k:int128, polyval_dot h h:int128);
                (b2:int128, byteswap128 h:int128, hk:int128, h:int128)]
              :(int128#int128#int128#int128)list`
              GHASH_NBLOCK_KARATSUBA_EQ_PROP3) THEN
  ASM_REWRITE_TAC[kara_quad_ok; kara_quad_pmul; WORD_XOR_0_LEFT] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ========================================================================= *)
(*  PER-N: MACHINE CODE                                                      *)
(* ========================================================================= *)

(* ===== TWO-BLOCK: GHASH / mask / branch closers ========================== *)
(* ========================================================================= *)
(* PER-BLOCK CIPHERTEXT CLOSURES (instances of GCM_NBLOCK_CT_STEP_TAC for     *)
(* N=2). Block 1 has ivec_1 = ivec (no LANE/CTR chain); block 2 has         *)
(* ivec_2 = gcm_ctr_inc ivec (LANE/CTR/BYTEREVERSE chain).                    *)
(* ========================================================================= *)


(* ========================================================================= *)
(*  GHASH STEP TACTIC (N=2 instance) -- same template as 4/5/6/7 blocks.      *)
(*  Atoms (c?lo/c?hi, xilo/xihi, hd/he) -> inner pmuls (w?lo/w?hi/w?md) ->     *)
(*  z-vars -> qS/qB Barrett pmuls -> bubble_sort_conv XOR-AC closure.         *)
(* ========================================================================= *)

(* GCM_2BLOCK_GHASH_STEP_TAC moved to gcm_aesgcm_standalone_blocks_helper.ml (unused by AES256_GCM_ENCRYPT_CORRECT). *)

(* The shared masked-GHASH normalisation for two ciphertext blocks (block 1   *)
(* full, block 2 partial), up to the point where the two word_join halves are  *)
(* left as a single XOR-of-Karatsuba-atoms equality.  The standalone two-block *)
(* routine and the single-binary more_than_1 branch differ only in how that    *)
(* final equality is discharged, so they share this prefix.                    *)
let GCM_2BLOCK_GHASH_PREFIX_TAC =
  REWRITE_TAC[GHASH_POLYVAL_ACC_2; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  SUBGOAL_THEN
    `word_xor xi (word_xor pt1
       (aes256_block_enc ivec rk0 rk1 rk2 rk3 rk4 rk5 rk6 rk7
                         rk8 rk9 rk10 rk11 rk12 rk13 rk14)) =
     word_xor xi ct1:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ct1" THEN EXPAND_TAC "s13_1" THEN
    REWRITE_TAC[aes256_block_enc; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN
    ASM_REWRITE_TAC[] THEN
    (* June-2026 base leaves a residual XOR-association goal `(xi(+)pt1)(+)s13_1)(+)rk14
       = xi (+) ct1`; fold ct1 back via GSYM of its defining assumption, then WORD_RULE. *)
    FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `ct1:(128)word` &&
         aconv (lhs(concl th)) `word_xor (word_xor pt1 s13_1) rk14:(128)word`
      then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    CONV_TAC WORD_RULE; ALL_TAC ] THEN
  SUBGOAL_THEN
    `word_xor pt2
       (aes256_block_enc (gcm_ctr_inc ivec) rk0 rk1 rk2 rk3 rk4 rk5 rk6
                         rk7 rk8 rk9 rk10 rk11 rk12 rk13 rk14) =
     ct2:(128)word`
    (fun th -> REWRITE_TAC[th]) THENL [
    (* The ct2 def hypothesis is stored LEFT-associated in the June base; accept
       either association for the SYM-fold. *)
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `ct2:(128)word` &&
         (aconv (lhs(concl th)) `word_xor pt2 (word_xor s13_2 rk14):(128)word` ||
          aconv (lhs(concl th)) `word_xor (word_xor pt2 s13_2) rk14:(128)word`)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[aes256_block_enc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `s13_2:(128)word` &&
         not(try fst(dest_const(rator(rator(lhs(concl th))))) = "read" with _ -> false)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
    REWRITE_TAC[gcm_ctr_inc] THEN
    REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
    REWRITE_TAC[WORD_BLAST `!x:(32)word. word_reversefields 8 x = word_bytereverse x`] THEN
    REWRITE_TAC[GSYM CTR_WORD_INSERT] THEN
    REWRITE_TAC[BYTEREVERSE_JOIN_FOLD]; ALL_TAC ] THEN
  (* Partial last block: abbreviate the mask and the masked block ctm2, and
     bridge the simulator's word_and mask ct2 to ctm2 = word_and ct2 mask. *)
  ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm2 = word_and (ct2:(128)word) mask` THEN
  SUBGOAL_THEN `word_and (mask:(128)word) (ct2:(128)word) = ctm2`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm2" THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC ] THEN
  MP_TAC(SPECL
    [`word_reversefields 8 (word_xor xi ct1):int128`;
     `word_reversefields 8 ctm2:int128`;
     `h:int128`;
     `h1k:int128`;
     `word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word`]
    GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h1k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[ghash_2block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot h h):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[GSYM karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC SYM_CONV THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word` &&
       (try (let l = lhs(concl th) in is_comb l &&
             (let r = rator l in not(is_comb r && (try fst(dest_const(rator r)) = "read" with _ -> false))))
        with _ -> false)
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  REWRITE_TAC[WORD_SWAP_HALVES_INVOLUTION] THEN
  (* June-2026 base: collapse the straddling word_subword (word_join _ _) (64,128). *)
  REWRITE_TAC[WORD_JOIN_SELF_MID] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_1; WORD_INSERT_AS_JOIN_2;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION; WORD_JOIN_SELF_MID;
              WORD_OR_REFL; WORD_XOR_ASSOC; WORD_SUBWORD_XOR;
              BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_0; WORD_XOR_ASSOC;
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  SUBGOAL_THEN
    `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
     word_subword (word 0:(128)word) (64,64):(64)word = word 0`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  (* 10 atomic ABBREVs *)
  ABBREV_TAC `(c1lo:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c1hi:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c2lo:(64)word) = word_subword (word_reversefields 8 (ctm2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c2hi:(64)word) = word_subword (word_reversefields 8 (ctm2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(xilo:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (0,64)` THEN
  ABBREV_TAC `(xihi:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (64,64)` THEN
  ABBREV_TAC `(hd0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(hd1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(he0:(64)word) = word_subword ((polyval_dot h h):(128)word) (0,64)` THEN
  ABBREV_TAC `(he1:(64)word) = word_subword ((polyval_dot h h):(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* 6 inner pmul ABBREVs *)
  ABBREV_TAC `(w1lo:(128)word) = word_pmul (word_xor (xilo:(64)word) (c1lo:(64)word)) (he0:(64)word)` THEN
  ABBREV_TAC `(w1hi:(128)word) = word_pmul (word_xor (xihi:(64)word) (c1hi:(64)word)) (he1:(64)word)` THEN
  ABBREV_TAC `(w1md:(128)word) = word_pmul (word_xor (word_xor (xihi:(64)word) (c1hi:(64)word)) (word_xor (xilo:(64)word) (c1lo:(64)word))) (word_xor (he0:(64)word) (he1:(64)word))` THEN
  ABBREV_TAC `(w2lo:(128)word) = word_pmul (c2lo:(64)word) (hd0:(64)word)` THEN
  ABBREV_TAC `(w2hi:(128)word) = word_pmul (c2hi:(64)word) (hd1:(64)word)` THEN
  ABBREV_TAC `(w2md:(128)word) = word_pmul (word_xor (c2hi:(64)word) (c2lo:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (xihi:(64)word) (word_xor (c1hi:(64)word) (word_xor (xilo:(64)word) (c1lo:(64)word)))) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* 12 z-vars *)
  ABBREV_TAC `(w1lo_l:(64)word) = word_subword (w1lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1lo_h:(64)word) = word_subword (w1lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1hi_l:(64)word) = word_subword (w1hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1hi_h:(64)word) = word_subword (w1hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1md_l:(64)word) = word_subword (w1md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1md_h:(64)word) = word_subword (w1md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2lo_l:(64)word) = word_subword (w2lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2lo_h:(64)word) = word_subword (w2lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2hi_l:(64)word) = word_subword (w2hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2hi_h:(64)word) = word_subword (w2hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2md_l:(64)word) = word_subword (w2md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2md_h:(64)word) = word_subword (w2md:(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* Normalize LHS mid-pmuls to abbreviated w?md. *)
  SUBGOAL_THEN `word_pmul (word_xor (c2lo:(64)word) (c2hi:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word)):(128)word = w2md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w2md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (xilo:(64)word) (word_xor (c1lo:(64)word) (word_xor (xihi:(64)word) (c1hi:(64)word)))) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* qS. *)
  ABBREV_TAC `(qS:(128)word) = word_pmul (word_xor (w2lo_l:(64)word) (w1lo_l)) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN `word_pmul (word_xor (w1lo_l:(64)word) (w2lo_l)) (word 13979173243358019584:(64)word):(128)word = qS`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "qS" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* qB. *)
  ABBREV_TAC `(qB:(128)word) = word_pmul
    (word_xor (w2md_l:(64)word) (word_xor w1md_l (word_xor w2lo_l (word_xor w1lo_l (word_xor w2hi_l (word_xor w1hi_l (word_xor (word_subword (qS:(128)word) (0,64)) (word_xor w2lo_h (w1lo_h))))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (w1lo_h:(64)word) (word_xor w2lo_h (word_xor w1md_l (word_xor w2md_l (word_xor w1hi_l (word_xor w2hi_l (word_xor w1lo_l (word_xor w2lo_l ((word_subword (qS:(128)word) (0,64))))))))))) (word 13979173243358019584:(64)word):(128)word = qB`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC];;

(* Fold the byte-join/word_add form the simulator produces for an AES counter  *)
(* block back to `aes256_block_enc (gcm_ctr_inc^k ivec) ...`.  Used to discharge*)
(* a `word_xor pt (aes256_block_enc (gcm_ctr_inc^k ivec) ...) = ct` goal after  *)
(* EXPAND_TAC has unfolded `ct`; `sname` is the abbreviated keystream variable. *)
(* CTR1: one increment (the second of two blocks). *)
let GCM_CTR1_FOLD_TAC sname =
  REWRITE_TAC[aes256_block_enc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  (* June-2026 HOL base: WORD_XOR_ASSOC normalizes to LEFT-association and the ARM
     simulator emits word_reversefields 8 (not word_bytereverse) for the 32-bit REV
     counter shuffle.  Normalize to left-assoc, peel THM/TERM/TERM, then bridge the
     counter identity with WORD_REVERSEFIELDS_REVERSEFIELDS + reversefields->
     bytereverse + GSYM CTR_WORD_INSERT + BYTEREVERSE_JOIN_FOLD. *)
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = mk_var(sname,`:(128)word`) &&
       not(try fst(dest_const(rator(rator(lhs(concl th))))) = "read" with _ -> false)
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  REWRITE_TAC[gcm_ctr_inc] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_BLAST `!x:(32)word. word_reversefields 8 x = word_bytereverse x`] THEN
  REWRITE_TAC[GSYM CTR_WORD_INSERT] THEN
  REWRITE_TAC[BYTEREVERSE_JOIN_FOLD] THEN TRY REFL_TAC;;

(* CTR2: two increments (the third of three blocks).  The nested gcm_ctr_inc    *)
(* needs the intermediate counter abbreviated before the bytereverse folds.     *)
let GCM_CTR2_FOLD_TAC sname =
  REWRITE_TAC[aes256_block_enc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  (* June-2026 base: left-associated WORD_XOR_ASSOC, reversefields-8 counter
     shuffle.  Normalize to left-assoc, peel THM/TERM/TERM, substitute the
     keystream, bridge reversefields->bytereverse, then the double-increment
     counter identity (word_join=word_insert) closes per 32-bit field. *)
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = mk_var(sname,`:(128)word`) &&
       not(try fst(dest_const(rator(rator(lhs(concl th))))) = "read" with _ -> false)
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  REWRITE_TAC[LANE0_BYTES_JOIN; LANE1_BYTES_JOIN; LANE2_BYTES_JOIN; LANE3_BYTES_JOIN_BE;
              CTR_WORD_INSERT] THEN
  REWRITE_TAC[gcm_ctr_inc] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
  ABBREV_TAC `ctr3g:(32)word = word_subword (ivec:(128)word) (96,32)` THEN
  ABBREV_TAC `br3g:(32)word = word_bytereverse (ctr3g:(32)word)` THEN
  ABBREV_TAC `step1_3g:(32)word = word_bytereverse (word_add (br3g:(32)word) (word 1:(32)word))` THEN
  REWRITE_TAC[BYTEREVERSE_JOIN_FOLD; INSERT_SUBWORD; INSERT_IDEM] THEN
  REWRITE_TAC[GSYM CTR_WORD_INSERT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  EXPAND_TAC "step1_3g" THEN
  REWRITE_TAC[WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_RULE;;

(* xi reassembled from its own halves.  The single-binary more_than_1 path     *)
(* emits an EXT/INS decompose-recompose of xi that the standalone routine does *)
(* not; folding it back lets the xilo/xihi abbreviations fire on both halves.  *)
let JOIN_XI_SELF = prove
 (`word_join (word_subword (xi:(128)word) (64,64):(64)word)
             (word_subword xi (0,64):(64)word):(128)word = xi`,
  CONV_TAC WORD_BLAST);;

(* Standalone-routine ending: the two halves already share an atom multiset,   *)
(* so a per-half AC sort closes them. *)
let GCM_2BLOCK_GHASH_STEP_MASKED_TAC =
  GCM_2BLOCK_GHASH_PREFIX_TAC THEN
  BINOP_TAC THENL
   [CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC;
    CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC];;

(* `bubble_sort_conv` performs only `n` bubble passes (n = #xors), which is not *)
(* always enough to fully sort a chain whose atoms start far from their final   *)
(* position (e.g. `word_subword qS (0,64)` needing to travel the whole chain).  *)
(* Iterating to a fixpoint yields a canonical normal form, so two XOR sums with *)
(* the same atom multiset always converge to identical terms.                   *)
let rec bubble_fix tm =
  let th = bubble_sort_conv tm in
  let r = rhs(concl th) in
  if r = tm then th else TRANS th (bubble_fix r);;

(* The single-binary more_than_1 path reassembles xi from its halves (via the   *)
(* EXT/INS that the standalone routine lacks), which reintroduces the qB        *)
(* Barrett mid-pmul in several distinct XOR-associations.  Fold every           *)
(* `word_pmul <args> (word 13979173243358019584)` occurrence back to the        *)
(* abbreviated `qB` by matching args up to AC (fixpoint bubble sort), so the    *)
(* final per-half sort sees `qB` as a single atom on both sides.                *)
let GCM_2BLOCK_FOLD_QB_TAC : tactic =
  let w64 = `word 13979173243358019584:(64)word` in
  fun (asl,gg) ->
    let rec finds t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = w64 ->
          a :: (finds a (finds x acc))
      | Comb(l,r) -> finds l (finds r acc)
      | Abs(_,b) -> finds b acc
      | _ -> acc in
    let args = setify (finds gg []) in
    let mk arg =
      SUBGOAL_THEN
        (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[arg;w64]),
               `qB:(128)word`))
        (fun th -> REWRITE_TAC[th]) THENL
       [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC; ALL_TAC] in
    (EVERY (map mk args)) (asl,gg);;

(* Single-binary more_than_1 branch ending: fold the reassembled xi (so the    *)
(* block-1 atoms collapse onto the abbreviations), re-fold the reordered w1md  *)
(* mid-pmul in all three orderings the reassembly produces, fold the qB        *)
(* Barrett pmuls, then AC-sort the two halves to a fixpoint. *)
let GCM_2BLOCK_GHASH_VIA_BRANCH_TAC =
  GCM_2BLOCK_GHASH_PREFIX_TAC THEN
  REWRITE_TAC[JOIN_XI_SELF] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (xihi:(64)word) (word_xor c1hi (word_xor xilo c1lo)))
               (word_xor (he0:(64)word) he1):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (word_xor (word_xor (xilo:(64)word) c1lo) xihi) c1hi)
               (word_xor (he0:(64)word) he1):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (word_xor (word_xor (xihi:(64)word) c1hi) xilo) c1lo)
               (word_xor (he0:(64)word) he1):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  GCM_2BLOCK_FOLD_QB_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_ASSOC] THEN
  BINOP_TAC THENL
   [CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;
    CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Partial-final-block helpers.                                              *)
(*   total bytes = 16 + byte_len (block 1 full, block 2 = byte_len bytes).    *)
(* ------------------------------------------------------------------------- *)

let TWOBLOCK_USHR = prove
 (`!byte_len. byte_len <= 16 ==>
     word_ushr (word (128 + 8 * byte_len):int64) 3 = word (16 + byte_len)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `128 + 8 * byte_len = 8 * (16 + byte_len)` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NBLOCK_USHR_BYTELEN THEN ASM_ARITH_TAC);;

(* The "more than 1 block" cascade branch (b.gt) is taken for any partial
   final block, so the PC resolves to the in-cascade target (pc+408). *)
(* TWOBLOCK_BRANCH moved to gcm_aesgcm_standalone_blocks_helper.ml (unused by AES256_GCM_ENCRYPT_CORRECT). *)

(* The partial-block mask register, built from the 2-block bit length
   (128 + 8*byte_len), collapses to word (2^(8*byte_len) - 1): the leading
   full block contributes 128 = 0 (mod 128), so only byte_len matters. *)
let TWOBLOCK_MASK_REG = prove
 (`!byte_len (b0:int128). 1 <= byte_len /\ byte_len <= 16 ==>
    (word_insert
     ((word_insert (b0:int128)
        (0,64)
        (if ~(ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (128 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64)) < &0 <=>
              ~(ival (word_and (word_sub (word 0) (word_sub (word_and (word (128 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) - &64 =
                ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (128 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64))))
         then word 18446744073709551615:int64
         else word_jushr (word 18446744073709551615:int64) (word_and (word_sub (word 0) (word_sub (word_and (word (128 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)))):int128)
     (64,64)
     (if ~(ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (128 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64)) < &0 <=>
           ~(ival (word_and (word_sub (word 0) (word_sub (word_and (word (128 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) - &64 =
             ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (128 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64))))
        then word_jushr (word 18446744073709551615:int64) (word_and (word_sub (word 0) (word_sub (word_and (word (128 + 8*byte_len):int64) (word 127)) (word 128))) (word 127))
        else word 0:int64)
    : int128)
    = word (2 EXP (8 * byte_len) - 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NBLOCK_WORD_INSERT_BOTH_LANES] THEN
  NBLOCK_MASK_PEEL_TAC 1);;
