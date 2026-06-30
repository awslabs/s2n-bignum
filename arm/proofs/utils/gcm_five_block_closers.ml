(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)
(* ========================================================================= *)
(* 5-block GHASH and partial-block closers for the AES-256-GCM band proof.   *)
(* Pure algebra (no machine code, no symbolic simulation).                   *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml";;

let ghash_5block_karatsuba = new_definition
 `ghash_5block_karatsuba (b1:int128) (b2:int128) (b3:int128) (b4:int128) (b5:int128)
                         (h_tw:int128)  (hk:int128)
                         (h2_tw:int128) (h2k:int128)
                         (h3_tw:int128) (h3k:int128)
                         (h4_tw:int128) (h4k:int128)
                         (h5_tw:int128) (h5k:int128) : int128 =
  let b1_lo:64 word = word_subword b1 (0,64) in
  let b1_hi:64 word = word_subword b1 (64,64) in
  let h5_lo:64 word = word_subword h5_tw (0,64) in
  let h5_hi:64 word = word_subword h5_tw (64,64) in
  let h5k_lo:64 word = word_subword h5k (0,64) in
  let pl1:int128 = word_pmul b1_lo h5_hi in
  let ph1:int128 = word_pmul b1_hi h5_lo in
  let pm1:int128 = word_pmul (word_xor b1_lo b1_hi) h5k_lo in
  let b2_lo:64 word = word_subword b2 (0,64) in
  let b2_hi:64 word = word_subword b2 (64,64) in
  let h4_lo:64 word = word_subword h4_tw (0,64) in
  let h4_hi:64 word = word_subword h4_tw (64,64) in
  let h4k_lo:64 word = word_subword h4k (0,64) in
  let pl2:int128 = word_pmul b2_lo h4_hi in
  let ph2:int128 = word_pmul b2_hi h4_lo in
  let pm2:int128 = word_pmul (word_xor b2_lo b2_hi) h4k_lo in
  let b3_lo:64 word = word_subword b3 (0,64) in
  let b3_hi:64 word = word_subword b3 (64,64) in
  let h3_lo:64 word = word_subword h3_tw (0,64) in
  let h3_hi:64 word = word_subword h3_tw (64,64) in
  let h3k_lo:64 word = word_subword h3k (0,64) in
  let pl3:int128 = word_pmul b3_lo h3_hi in
  let ph3:int128 = word_pmul b3_hi h3_lo in
  let pm3:int128 = word_pmul (word_xor b3_lo b3_hi) h3k_lo in
  let b4_lo:64 word = word_subword b4 (0,64) in
  let b4_hi:64 word = word_subword b4 (64,64) in
  let h2_lo:64 word = word_subword h2_tw (0,64) in
  let h2_hi:64 word = word_subword h2_tw (64,64) in
  let h2k_lo:64 word = word_subword h2k (0,64) in
  let pl4:int128 = word_pmul b4_lo h2_hi in
  let ph4:int128 = word_pmul b4_hi h2_lo in
  let pm4:int128 = word_pmul (word_xor b4_lo b4_hi) h2k_lo in
  let b5_lo:64 word = word_subword b5 (0,64) in
  let b5_hi:64 word = word_subword b5 (64,64) in
  let h_lo:64 word = word_subword h_tw (0,64) in
  let h_hi:64 word = word_subword h_tw (64,64) in
  let hk_lo:64 word = word_subword hk (0,64) in
  let pl5:int128 = word_pmul b5_lo h_hi in
  let ph5:int128 = word_pmul b5_hi h_lo in
  let pm5:int128 = word_pmul (word_xor b5_lo b5_hi) hk_lo in
  let pl:int128 = word_xor pl1 (word_xor pl2 (word_xor pl3 (word_xor pl4 pl5))) in
  let ph:int128 = word_xor ph1 (word_xor ph2 (word_xor ph3 (word_xor ph4 ph5))) in
  let pm:int128 = word_xor pm1 (word_xor pm2 (word_xor pm3 (word_xor pm4 pm5))) in
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
(* ========================================================================= *)

let GHASH_5BLOCK_AS_NBLOCK = prove
 (`!(b1:int128) (b2:int128) (b3:int128) (b4:int128) (b5:int128)
    (h_tw:int128)  (hk:int128)
    (h2_tw:int128) (h2k:int128)
    (h3_tw:int128) (h3k:int128)
    (h4_tw:int128) (h4k:int128)
    (h5_tw:int128) (h5k:int128).
    ghash_Nblock_karatsuba [(b1, h5_tw, h5k); (b2, h4_tw, h4k);
                            (b3, h3_tw, h3k); (b4, h2_tw, h2k);
                            (b5, h_tw, hk)] =
    ghash_5block_karatsuba b1 b2 b3 b4 b5 h_tw hk h2_tw h2k h3_tw h3k h4_tw h4k h5_tw h5k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ghash_Nblock_karatsuba; ghash_5block_karatsuba;
              kara_acc; karatsuba_block_pl; karatsuba_block_ph;
              karatsuba_block_pm; karatsuba_reduce_shared;
              LET_DEF; LET_END_DEF; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC]);;

(* ========================================================================= *)
(* PER-N BRIDGE: ghash_5block_karatsuba ↔ polyval_reduce_prop3               *)
(* DERIVED from GHASH_NBLOCK_KARATSUBA_EQ_PROP3 (the inductive bridge)       *)
(* ========================================================================= *)

let GHASH_5BLOCK_KARATSUBA_EQ_POLYVAL_ACC = prove
 (`!(b1:int128) (b2:int128) (b3:int128) (b4:int128) (b5:int128) (h:int128)
     (hk:int128) (h2k:int128) (h3k:int128) (h4k:int128) (h5k:int128).
    word_subword hk  (0,64):(64)word = karatsuba_mid h /\
    word_subword h2k (0,64):(64)word = karatsuba_mid (polyval_dot h h) /\
    word_subword h3k (0,64):(64)word =
      karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
    word_subword h4k (0,64):(64)word =
      karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
    word_subword h5k (0,64):(64)word =
      karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h)
    ==> ghash_5block_karatsuba b1 b2 b3 b4 b5
          (word_swaphalves128 h) hk
          (word_swaphalves128 (polyval_dot h h)) h2k
          (word_swaphalves128 (polyval_dot h (polyval_dot h h))) h3k
          (word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h))) h4k
          (word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h)) h5k =
        word_reversefields 8
          (polyval_reduce_prop3
            (word_xor
              (word_pmul b1 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h)
                : 256 word)
             (word_xor
              (word_pmul b2 (polyval_dot (polyval_dot h h) (polyval_dot h h)) : 256 word)
              (word_xor
                (word_pmul b3 (polyval_dot h (polyval_dot h h)) : 256 word)
                (word_xor
                  (word_pmul b4 (polyval_dot h h) : 256 word)
                  (word_pmul b5 h : 256 word))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM GHASH_5BLOCK_AS_NBLOCK] THEN
  SUBGOAL_THEN
    `[(b1:int128, word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):int128, h5k:int128);
      (b2:int128, word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)):int128, h4k:int128);
      (b3:int128, word_swaphalves128 (polyval_dot h (polyval_dot h h)):int128, h3k:int128);
      (b4:int128, word_swaphalves128 (polyval_dot h h):int128, h2k:int128);
      (b5:int128, word_swaphalves128 h:int128, hk:int128)] =
     project_triples
       [(b1, word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h),
           h5k, polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h);
        (b2, word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)),
           h4k, polyval_dot (polyval_dot h h) (polyval_dot h h));
        (b3, word_swaphalves128 (polyval_dot h (polyval_dot h h)), h3k, polyval_dot h (polyval_dot h h));
        (b4, word_swaphalves128 (polyval_dot h h), h2k, polyval_dot h h);
        (b5, word_swaphalves128 h, hk, h)]`
    SUBST1_TAC THENL [REWRITE_TAC[project_triples]; ALL_TAC] THEN
  MP_TAC(SPEC
    `[(b1:int128, word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):int128,
         h5k:int128, polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h:int128);
      (b2:int128, word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)):int128,
         h4k:int128, polyval_dot (polyval_dot h h) (polyval_dot h h):int128);
      (b3:int128, word_swaphalves128 (polyval_dot h (polyval_dot h h)):int128, h3k:int128, polyval_dot h (polyval_dot h h):int128);
      (b4:int128, word_swaphalves128 (polyval_dot h h):int128, h2k:int128, polyval_dot h h:int128);
      (b5:int128, word_swaphalves128 h:int128, hk:int128, h:int128)]
    :(int128#int128#int128#int128)list`
    GHASH_NBLOCK_KARATSUBA_EQ_PROP3) THEN
  ASM_REWRITE_TAC[kara_quad_ok; kara_quad_pmul; WORD_XOR_0_LEFT] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* GHASH_POLYVAL_ACC_5 and the symmetric h-power normalizer POLYVAL_DOT_H5_EQ
   live in gcm_aesgcm_helpers.ml / gcm_aesgcm_nblock_helpers.ml respectively. *)

(* ===== Per-block ciphertext closers (ct1 closes inline in aes256_gcm.ml) = *)
let GCM_5BLOCK_CT2_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 5 2;;
let GCM_5BLOCK_CT3_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 5 3;;
let GCM_5BLOCK_CT4_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 5 4;;

(* ===== Partial-final-block helpers (total bytes = 64 + byte_len) ========= *)
let FIVEBLOCK_USHR = prove
 (`!byte_len. byte_len <= 16 ==>
     word_ushr (word (512 + 8 * byte_len):int64) 3 = word (64 + byte_len)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `512 + 8 * byte_len = 8 * (64 + byte_len)` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NBLOCK_USHR_BYTELEN THEN ASM_ARITH_TAC);;

let FIVEBLOCK_MASK_REG = prove
 (`!byte_len (b0:int128). 1 <= byte_len /\ byte_len <= 16 ==>
    (word_insert
     ((word_insert (b0:int128)
        (0,64)
        (if ~(ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (512 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64)) < &0 <=>
              ~(ival (word_and (word_sub (word 0) (word_sub (word_and (word (512 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) - &64 =
                ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (512 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64))))
         then word 18446744073709551615:int64
         else word_jushr (word 18446744073709551615:int64) (word_and (word_sub (word 0) (word_sub (word_and (word (512 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)))):int128)
     (64,64)
     (if ~(ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (512 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64)) < &0 <=>
           ~(ival (word_and (word_sub (word 0) (word_sub (word_and (word (512 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) - &64 =
             ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (512 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64))))
        then word_jushr (word 18446744073709551615:int64) (word_and (word_sub (word 0) (word_sub (word_and (word (512 + 8*byte_len):int64) (word 127)) (word 128))) (word 127))
        else word 0:int64)
    : int128)
    = word (2 EXP (8 * byte_len) - 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NBLOCK_WORD_INSERT_BOTH_LANES] THEN
  NBLOCK_MASK_PEEL_TAC 1);;

