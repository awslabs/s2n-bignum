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

(* The two standalone-routine GHASH closers (GCM_2BLOCK_GHASH_STEP_MASKED_TAC /
   _VIA_BRANCH_TAC) and their helpers (GCM_2BLOCK_GHASH_PREFIX_TAC,
   GCM_2BLOCK_FOLD_QB_TAC, GCM_CTR1/2_FOLD_TAC, JOIN_XI_SELF) were removed:
   unused by AES256_GCM_ENCRYPT_CORRECT (the live more_than_1 GHASH is closed
   inline in aes256_gcm.ml). *)
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
