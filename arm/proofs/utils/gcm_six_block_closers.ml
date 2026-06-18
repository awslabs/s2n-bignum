(* ===== 6-block GHASH closers (mc-free, extracted from aes256_gcm_six_block.ml) ===== *)
needs "arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml";;

let ghash_6block_karatsuba = new_definition
 `ghash_6block_karatsuba (b1:int128) (b2:int128) (b3:int128) (b4:int128) (b5:int128) (b6:int128)
                         (h_tw:int128)  (hk:int128)
                         (h2_tw:int128) (h2k:int128)
                         (h3_tw:int128) (h3k:int128)
                         (h4_tw:int128) (h4k:int128)
                         (h5_tw:int128) (h5k:int128)
                         (h6_tw:int128) (h6k:int128) : int128 =
  let b1_lo:64 word = word_subword b1 (0,64) in
  let b1_hi:64 word = word_subword b1 (64,64) in
  let hp6_lo:64 word = word_subword h6_tw (0,64) in
  let hp6_hi:64 word = word_subword h6_tw (64,64) in
  let hp6k_lo:64 word = word_subword h6k (0,64) in
  let pl1:int128 = word_pmul b1_lo hp6_hi in
  let ph1:int128 = word_pmul b1_hi hp6_lo in
  let pm1:int128 = word_pmul (word_xor b1_lo b1_hi) hp6k_lo in
  let b2_lo:64 word = word_subword b2 (0,64) in
  let b2_hi:64 word = word_subword b2 (64,64) in
  let hp5_lo:64 word = word_subword h5_tw (0,64) in
  let hp5_hi:64 word = word_subword h5_tw (64,64) in
  let hp5k_lo:64 word = word_subword h5k (0,64) in
  let pl2:int128 = word_pmul b2_lo hp5_hi in
  let ph2:int128 = word_pmul b2_hi hp5_lo in
  let pm2:int128 = word_pmul (word_xor b2_lo b2_hi) hp5k_lo in
  let b3_lo:64 word = word_subword b3 (0,64) in
  let b3_hi:64 word = word_subword b3 (64,64) in
  let hp4_lo:64 word = word_subword h4_tw (0,64) in
  let hp4_hi:64 word = word_subword h4_tw (64,64) in
  let hp4k_lo:64 word = word_subword h4k (0,64) in
  let pl3:int128 = word_pmul b3_lo hp4_hi in
  let ph3:int128 = word_pmul b3_hi hp4_lo in
  let pm3:int128 = word_pmul (word_xor b3_lo b3_hi) hp4k_lo in
  let b4_lo:64 word = word_subword b4 (0,64) in
  let b4_hi:64 word = word_subword b4 (64,64) in
  let hp3_lo:64 word = word_subword h3_tw (0,64) in
  let hp3_hi:64 word = word_subword h3_tw (64,64) in
  let hp3k_lo:64 word = word_subword h3k (0,64) in
  let pl4:int128 = word_pmul b4_lo hp3_hi in
  let ph4:int128 = word_pmul b4_hi hp3_lo in
  let pm4:int128 = word_pmul (word_xor b4_lo b4_hi) hp3k_lo in
  let b5_lo:64 word = word_subword b5 (0,64) in
  let b5_hi:64 word = word_subword b5 (64,64) in
  let hp2_lo:64 word = word_subword h2_tw (0,64) in
  let hp2_hi:64 word = word_subword h2_tw (64,64) in
  let hp2k_lo:64 word = word_subword h2k (0,64) in
  let pl5:int128 = word_pmul b5_lo hp2_hi in
  let ph5:int128 = word_pmul b5_hi hp2_lo in
  let pm5:int128 = word_pmul (word_xor b5_lo b5_hi) hp2k_lo in
  let b6_lo:64 word = word_subword b6 (0,64) in
  let b6_hi:64 word = word_subword b6 (64,64) in
  let hp1_lo:64 word = word_subword h_tw (0,64) in
  let hp1_hi:64 word = word_subword h_tw (64,64) in
  let hp1k_lo:64 word = word_subword hk (0,64) in
  let pl6:int128 = word_pmul b6_lo hp1_hi in
  let ph6:int128 = word_pmul b6_hi hp1_lo in
  let pm6:int128 = word_pmul (word_xor b6_lo b6_hi) hp1k_lo in
  let pl:int128 = word_xor pl1 (word_xor pl2 (word_xor pl3 (word_xor pl4 (word_xor pl5 (pl6))))) in
  let ph:int128 = word_xor ph1 (word_xor ph2 (word_xor ph3 (word_xor ph4 (word_xor ph5 (ph6))))) in
  let pm:int128 = word_xor pm1 (word_xor pm2 (word_xor pm3 (word_xor pm4 (word_xor pm5 (pm6))))) in
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

let GHASH_6BLOCK_AS_NBLOCK = prove
 (`!(b1:int128) (b2:int128) (b3:int128) (b4:int128) (b5:int128) (b6:int128)
    (h_tw:int128)  (hk:int128)
    (h2_tw:int128) (h2k:int128)
    (h3_tw:int128) (h3k:int128)
    (h4_tw:int128) (h4k:int128)
    (h5_tw:int128) (h5k:int128)
    (h6_tw:int128) (h6k:int128).
    ghash_Nblock_karatsuba [(b1, h6_tw, h6k); (b2, h5_tw, h5k);
                            (b3, h4_tw, h4k); (b4, h3_tw, h3k);
                            (b5, h2_tw, h2k); (b6, h_tw, hk)] =
    ghash_6block_karatsuba b1 b2 b3 b4 b5 b6 h_tw hk h2_tw h2k h3_tw h3k h4_tw h4k h5_tw h5k h6_tw h6k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ghash_Nblock_karatsuba; ghash_6block_karatsuba;
              kara_acc; karatsuba_block_pl; karatsuba_block_ph;
              karatsuba_block_pm; karatsuba_reduce_shared;
              LET_DEF; LET_END_DEF; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC]);;

(* ========================================================================= *)
(* PER-N BRIDGE: ghash_6block_karatsuba <-> polyval_reduce_prop3              *)
(* ========================================================================= *)

let GHASH_6BLOCK_KARATSUBA_EQ_POLYVAL_ACC = prove
 (`!(b1:int128) (b2:int128) (b3:int128) (b4:int128) (b5:int128) (b6:int128) (h:int128)
     (hk:int128) (h2k:int128) (h3k:int128) (h4k:int128) (h5k:int128) (h6k:int128).
    word_subword hk  (0,64):(64)word = karatsuba_mid h /\
    word_subword h2k (0,64):(64)word = karatsuba_mid (polyval_dot h h) /\
    word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
    word_subword h4k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
    word_subword h5k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
    word_subword h6k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h)
    ==> ghash_6block_karatsuba b1 b2 b3 b4 b5 b6
          (byteswap128 h) hk
          (byteswap128 (polyval_dot h h)) h2k
          (byteswap128 (polyval_dot h (polyval_dot h h))) h3k
          (byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h))) h4k
          (byteswap128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h)) h5k
          (byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h)) h6k =
        word_reversefields 8
          (polyval_reduce_prop3
            (word_xor
              (word_pmul b1 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) : 256 word)
             (word_xor
              (word_pmul b2 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) : 256 word)
              (word_xor
                (word_pmul b3 (polyval_dot (polyval_dot h h) (polyval_dot h h)) : 256 word)
                (word_xor
                  (word_pmul b4 (polyval_dot h (polyval_dot h h)) : 256 word)
                  (word_xor
                    (word_pmul b5 (polyval_dot h h) : 256 word)
                    (word_pmul b6 h : 256 word)))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM GHASH_6BLOCK_AS_NBLOCK] THEN
  SUBGOAL_THEN
    `[(b1:int128, byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h):int128, h6k:int128);
      (b2:int128, byteswap128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):int128, h5k:int128);
      (b3:int128, byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h)):int128, h4k:int128);
      (b4:int128, byteswap128 (polyval_dot h (polyval_dot h h)):int128, h3k:int128);
      (b5:int128, byteswap128 (polyval_dot h h):int128, h2k:int128);
      (b6:int128, byteswap128 h:int128, hk:int128)] =
     project_triples
       [(b1, byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h), h6k, (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h));
        (b2, byteswap128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h), h5k, (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h));
        (b3, byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h)), h4k, (polyval_dot (polyval_dot h h) (polyval_dot h h)));
        (b4, byteswap128 (polyval_dot h (polyval_dot h h)), h3k, (polyval_dot h (polyval_dot h h)));
        (b5, byteswap128 (polyval_dot h h), h2k, (polyval_dot h h));
        (b6, byteswap128 h, hk, h)]`
    SUBST1_TAC THENL [REWRITE_TAC[project_triples]; ALL_TAC] THEN
  MP_TAC(SPEC
    `[(b1:int128, byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h):int128, h6k:int128, (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h):int128);
      (b2:int128, byteswap128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):int128, h5k:int128, (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):int128);
      (b3:int128, byteswap128 (polyval_dot (polyval_dot h h) (polyval_dot h h)):int128, h4k:int128, (polyval_dot (polyval_dot h h) (polyval_dot h h)):int128);
      (b4:int128, byteswap128 (polyval_dot h (polyval_dot h h)):int128, h3k:int128, (polyval_dot h (polyval_dot h h)):int128);
      (b5:int128, byteswap128 (polyval_dot h h):int128, h2k:int128, (polyval_dot h h):int128);
      (b6:int128, byteswap128 h:int128, hk:int128, h:int128)]
    :(int128#int128#int128#int128)list`
    GHASH_NBLOCK_KARATSUBA_EQ_PROP3) THEN
  ASM_REWRITE_TAC[kara_quad_ok; kara_quad_pmul; WORD_XOR_0_LEFT] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* GHASH_POLYVAL_ACC_6 (6-block specialization of GHASH_POLYVAL_ACC_BATCHED)
   is defined in arm/proofs/utils/gcm_aesgcm_helpers.ml (ACC_2..4 are in
   common/ghash_spec.ml; ACC_5/6/7 are derived in the helpers file).
   POLYVAL_DOT_H4_EQ_LOCAL / H5_EQ / H6_EQ live in
   arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml. *)


(* GCM_6BLOCK_CT1_STEP_TAC moved to gcm_aesgcm_standalone_blocks_helper.ml (unused by AES256_GCM_ENCRYPT_CORRECT). *)
let GCM_6BLOCK_CT2_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 6 2;;

(* CT3 for ivec_3 = gcm_ctr_inc² ivec — needs the second counter unfolding.
   Uses INSERT_IDEM/INSERT_SUBWORD to sidestep the polymorphic-type issue. *)
let GCM_6BLOCK_CT3_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 6 3;;

let GCM_6BLOCK_CT4_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 6 4;;

let GCM_6BLOCK_CT5_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC 6 5;;

(* GCM_6BLOCK_CT6_STEP_TAC moved to gcm_aesgcm_standalone_blocks_helper.ml (unused by AES256_GCM_ENCRYPT_CORRECT). *)

(* GCM_6BLOCK_GHASH_STEP_MASKED_TAC moved to gcm_aesgcm_standalone_blocks_helper.ml (unused by AES256_GCM_ENCRYPT_CORRECT). *)

let SIXBLOCK_USHR = prove
 (`!byte_len. byte_len <= 16 ==>
     word_ushr (word (640 + 8 * byte_len):int64) 3 = word (80 + byte_len)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `640 + 8 * byte_len = 8 * (80 + byte_len)` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NBLOCK_USHR_BYTELEN THEN ASM_ARITH_TAC);;

let SIXBLOCK_MASK_REG = prove
 (`!byte_len (b0:int128). 1 <= byte_len /\ byte_len <= 16 ==>
    (word_insert
     ((word_insert (b0:int128)
        (0,64)
        (if ~(ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (640 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64)) < &0 <=>
              ~(ival (word_and (word_sub (word 0) (word_sub (word_and (word (640 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) - &64 =
                ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (640 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64))))
         then word 18446744073709551615:int64
         else word_jushr (word 18446744073709551615:int64) (word_and (word_sub (word 0) (word_sub (word_and (word (640 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)))):int128)
     (64,64)
     (if ~(ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (640 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64)) < &0 <=>
           ~(ival (word_and (word_sub (word 0) (word_sub (word_and (word (640 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) - &64 =
             ival (word_sub (word_and (word_sub (word 0) (word_sub (word_and (word (640 + 8*byte_len):int64) (word 127)) (word 128))) (word 127)) (word 64))))
        then word_jushr (word 18446744073709551615:int64) (word_and (word_sub (word 0) (word_sub (word_and (word (640 + 8*byte_len):int64) (word 127)) (word 128))) (word 127))
        else word 0:int64)
    : int128)
    = word (2 EXP (8 * byte_len) - 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NBLOCK_WORD_INSERT_BOTH_LANES] THEN
  SPEC_TAC(`byte_len:num`,`byte_len:num`) THEN GEN_TAC THEN
  NBLOCK_MASK_PEEL_TAC 1);;

(* ------------------------------------------------------------------------- *)
(* Tail-dispatch cascade branch resolution.  With a symbolic byte_len the     *)
(* total length is X5 = word_ushr (word (640 + 8*byte_len)) 3 = 80 + byte_len *)
(* (five leading full blocks + the partial last block).  Each cmp/b.gt in the *)
(* cascade (thresholds 96,80 (taken),64,48,32,16) leaves the PC as an          *)
(* if-then-else on the signed-greater-than condition; SIXBLOCK_GT_COND        *)
(* collapses that to t < 80 + byte_len (TOTAL_LANES = 80), which the byte_len  *)
(* bounds then decide.                                                         *)
(* ------------------------------------------------------------------------- *)
