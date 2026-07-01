(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================== *)
(* AES-256-GCM proof helpers, ALGEBRA layer: stateless word/field rewrite     *)
(* lemmas the per-N-block closers reuse — Karatsuba limb extraction, the      *)
(* polyval_dot Karatsuba form, SIMD byte-shuffle / swap-halves folds, mask    *)
(* lemmas, GHASH-closure subword folds, and AES256_ENCRYPT_UNFOLD.  Pure      *)
(* facts only (WORD_BLAST / WORD_RULE), plus PMUL_NORM_CONV which one such    *)
(* lemma's proof needs.  The N-block proof MACHINERY (recursive spec, its     *)
(* bridge, the driving tactics, and the GHASH_POLYVAL_ACC_1..8 family) lives  *)
(* in gcm_aesgcm_nblock_helpers.ml.  No machine-code definition or theorem.   *)
(* ========================================================================== *)

needs "arm/proofs/base.ml";;
needs "common/aes.ml";;
needs "arm/proofs/utils/aes.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;
needs "common/karatsuba_pmul.ml";;
needs "common/polyval_ghash.ml";;

(* -------------------------------------------------------------------------- *)
(* Unfold aes256_encrypt on a literal round-key list to the aese/aesmc chain. *)
(* This is the form symbolic execution of the AESE+AESMC sequence emits, so   *)
(* the per-block ciphertext/keystream folds match the simulator.  Kept as a   *)
(* rewrite rule (not a conversion like the upstream AESENC_* ones) so it can  *)
(* be used in the closers' REWRITE_TAC lists and RULE_ASSUM_TAC calls, and    *)
(* stops at aese/aesmc rather than dissolving them into sub/shift/mix.        *)
(* -------------------------------------------------------------------------- *)

let AES256_ENCRYPT_UNFOLD = prove
 (`!(input:(128)word)
     (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
     (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
     (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
     (rk12:(128)word) (rk13:(128)word) (rk14:(128)word).
     aes256_encrypt input
       [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] =
     (let s0 = aesmc (aese input rk0) in
      let s1 = aesmc (aese s0 rk1) in
      let s2 = aesmc (aese s1 rk2) in
      let s3 = aesmc (aese s2 rk3) in
      let s4 = aesmc (aese s3 rk4) in
      let s5 = aesmc (aese s4 rk5) in
      let s6 = aesmc (aese s5 rk6) in
      let s7 = aesmc (aese s6 rk7) in
      let s8 = aesmc (aese s7 rk8) in
      let s9 = aesmc (aese s8 rk9) in
      let s10 = aesmc (aese s9 rk10) in
      let s11 = aesmc (aese s10 rk11) in
      let s12 = aesmc (aese s11 rk12) in
      let s13 = aese s12 rk13 in
      word_xor s13 rk14)`,
  REWRITE_TAC[aes256_encrypt; aes256_encrypt_round; aese; aesmc;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* ---- Karatsuba limb extraction lemmas (256-bit word_pmul layout) --------- *)

let KARATSUBA_LIMB_0_63 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (0,64) : 64 word =
    word_subword xl (0,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_64_127 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (64,64) : 64 word =
    word_xor (word_subword xl (64,64)) (word_subword mid (0,64))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_128_191 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (128,64) : 64 word =
    word_xor (word_subword xh (0,64)) (word_subword mid (64,64))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_192_255 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (192,64) : 64 word =
    word_subword xh (64,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMBS = CONJ (CONJ KARATSUBA_LIMB_0_63 KARATSUBA_LIMB_64_127)
                           (CONJ KARATSUBA_LIMB_128_191 KARATSUBA_LIMB_192_255);;

let KAR_SUBWORD_LEMMA = prove(
  `!(xi_rev:(128)word).
    word_subword
      (word_xor xi_rev
        (word_subword (word_join xi_rev xi_rev:(256)word) (64,128)))
      (0,64):(64)word =
    word_xor (word_subword xi_rev (0,64):(64)word)
             (word_subword xi_rev (64,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

(* ---- Pmul argument-order normalizer -------------------------------------- *)

let PMUL_NORM_CONV tm =
  match tm with
  | Comb(Comb(Const("word_pmul",_), a), b) ->
    if term_order a b then SPECL [a;b] WORD_PMUL_SYM
    else failwith "already normalized"
  | _ -> failwith "not word_pmul";;

(* The per-N GHASH Karatsuba specs/bridges live in the per-block closer       *)
(* files; the general (multi-N) support lemmas they need stay here.           *)

(* ---- polyval_dot expressed in Karatsuba + Prop3 form --------------------- *)

let POLYVAL_DOT_KARATSUBA = prove(
  `!(input:int128) (h:int128).
    polyval_dot input h =
    (let p_lo = word_pmul (word_subword input (0,64):(64)word)
                          (word_subword h (0,64):(64)word) : int128 in
     let p_hi = word_pmul (word_subword input (64,64):(64)word)
                          (word_subword h (64,64):(64)word) : int128 in
     let p_mid = word_pmul
        (word_xor (word_subword input (0,64):(64)word) (word_subword input (64,64)))
        (word_xor (word_subword h (0,64):(64)word) (word_subword h (64,64))) : int128 in
     let mid = word_xor (word_xor p_mid p_lo) p_hi in
     let a:64 word = word_subword p_lo (0,64) in
     let b:64 word = word_xor (word_subword p_lo (64,64)) (word_subword mid (0,64)) in
     let c:64 word = word_xor (word_subword p_hi (0,64)) (word_subword mid (64,64)) in
     let d:64 word = word_subword p_hi (64,64) in
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
     word_join g f : 128 word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[polyval_dot; polyval_reduce_prop3; LET_DEF; LET_END_DEF;
              REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[KARATSUBA_LIMBS] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC]);;

(* ---- Swap-halves subword folds + subword-of-XOR commute ------------------ *)

let SWAPHALVES128_SUBWORD_LO = prove(
  `!(h:int128). word_subword (word_swaphalves128 h) (0,64):(64)word = word_subword h (64,64)`,
  REWRITE_TAC[word_swaphalves128] THEN CONV_TAC WORD_BLAST);;

let SWAPHALVES128_SUBWORD_HI = prove(
  `!(h:int128). word_subword (word_swaphalves128 h) (64,64):(64)word = word_subword h (0,64)`,
  REWRITE_TAC[word_swaphalves128] THEN CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_XOR_COMM = prove(
  `!(a:(N)word) (b:(N)word) n.
    word_subword (word_xor a (word_xor b c)) n:(M)word =
    word_subword (word_xor a (word_xor c b)) n`,
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ---- SIMD per-lane reversal fold lemmas ---------------------------------- *)

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

let WORD_JOIN_SELF_MID = prove(
  `!a:(128)word.
     word_subword (word_join a a:(256)word) (64,128):(128)word =
     word_join (word_subword a (0,64):(64)word) (word_subword a (64,64):(64)word):(128)word`,
  CONV_TAC WORD_BLAST);;

(* Subword-of-(swapped-halves) folds for the GHASH closure. *)

let DOUBLE_SUBWORD_JOIN = prove(
  `!(x:(128)word).
    word_subword (word_subword (word_join x x:(256)word) (64,128):(128)word) (0,64):(64)word =
    word_subword x (64,64)`,
  CONV_TAC WORD_BLAST);;

let DOUBLE_SUBWORD_JOIN_HI = prove(
  `!(x:(128)word).
    word_subword (word_subword (word_join x x:(256)word) (64,128):(128)word) (64,64):(64)word =
    word_subword x (0,64)`,
  CONV_TAC WORD_BLAST);;

(* ---- Mask / word simplification lemmas ----------------------------------- *)

let MASK_IS_ONES = prove(
  `!(x:(128)word).
    word_insert (word_insert x (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word =
    (word_not(word 0):(128)word)`, CONV_TAC WORD_BLAST);;

let WORD_AND_FULLMASK_128 = prove(
  `!(x:(128)word) (y:(128)word).
    word_and x (word_insert (word_insert y (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word) = x`,
  REWRITE_TAC[MASK_IS_ONES; WORD_AND_NOT0]);;

let WORD_AND_FULLMASK_128_SYM = prove(
  `!(x:(128)word) (y:(128)word).
    word_and (word_insert (word_insert y (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word) x = x`,
  REWRITE_TAC[MASK_IS_ONES; WORD_AND_NOT0]);;

let BIF_MASK = prove(
  `!(d:(128)word) (n:(128)word) (m:(128)word).
    word_or (word_and d (word_insert (word_insert m (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word))
    (word_and n (word_not (word_insert (word_insert m (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word))) = d`,
  CONV_TAC WORD_BLAST);;

let WORD_ZX_ALLONES_64_128 = prove(
  `word_zx (word 18446744073709551615:(64)word):(128)word =
   word 18446744073709551615:(128)word`, CONV_TAC WORD_BLAST);;

let MASK_IS_ONES_64 = prove(
  `!(x:(128)word).
    word_insert (word_insert x (0,64) (word 18446744073709551615:(64)word):(128)word)
      (64,64) (word 18446744073709551615:(64)word):(128)word =
    (word_not(word 0):(128)word)`, CONV_TAC WORD_BLAST);;

let WORD_AND_MASK_64 = prove(
  `!(x:(128)word) (y:(128)word).
    word_and x (word_insert (word_insert y (0,64) (word 18446744073709551615:(64)word):(128)word)
      (64,64) (word 18446744073709551615:(64)word):(128)word) = x`,
  REWRITE_TAC[MASK_IS_ONES_64; WORD_AND_NOT0]);;

let WORD_AND_MASK_SYM_64 = prove(
  `!(x:(128)word) (y:(128)word).
    word_and (word_insert (word_insert y (0,64) (word 18446744073709551615:(64)word):(128)word)
      (64,64) (word 18446744073709551615:(64)word):(128)word) x = x`,
  REWRITE_TAC[MASK_IS_ONES_64; WORD_AND_NOT0]);;

(* Stack/pointer arithmetic normalizer *)

let STACK_PTR_CANCEL = WORD_RULE
  `!(x:(N)word) y. word_sub (word_add x y) y = x`;;

(* ---- GHASH closure lemmas ------------------------------------------------ *)

let WORD_XOR_0_LEFT = WORD_BITWISE_RULE
  `word_xor (word 0) x = (x:(N)word)`;;

let WORD_INSERT_AS_JOIN_LO = prove(
  `!(a:(128)word) (b:(128)word).
    word_insert a (0,64) (word_subword b (64,64):(128)word) =
    (word_join (word_subword a (64,64):(64)word) (word_subword b (64,64):(64)word):(128)word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_INSERT; BIT_WORD_JOIN;
              BIT_WORD_SUBWORD; DIMINDEX_64; DIMINDEX_128;
              SUB_0; LE_0; ADD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[COND_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 128 /\ ~(i < 64) ==> i - 64 < 64`;
               ARITH_RULE `i < 128 /\ ~(i < 64) ==> 64 + i - 64 = i`]);;

let WORD_INSERT_AS_JOIN_HI = prove(
  `!(a:(128)word) (b:(128)word).
    word_insert a (64,64) (word_subword b (0,64):(128)word) =
    (word_join (word_subword b (0,64):(64)word) (word_subword a (0,64):(64)word):(128)word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_INSERT; BIT_WORD_JOIN;
              BIT_WORD_SUBWORD; DIMINDEX_64; DIMINDEX_128;
              SUB_0; LE_0; ADD_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[COND_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `64 <= i /\ i < 128 ==> ~(i < 64)`;
               ARITH_RULE `64 <= i /\ i < 128 ==> i - 64 < 64`;
               ARITH_RULE `~(64 <= i /\ i < 128) /\ i < 128 ==> i < 64`;
               ARITH_RULE `0 + i = i`]);;

let REVERSEFIELDS8_SUBWORD_LO = prove(
  `!(x:(128)word).
    word_reversefields 8 (word_subword x (0,64):(64)word) =
    word_subword (word_reversefields 8 x:(128)word) (64,64):(64)word`,
  CONV_TAC WORD_BLAST);;

let REVERSEFIELDS8_SUBWORD_HI = prove(
  `!(x:(128)word).
    word_reversefields 8 (word_subword x (64,64):(64)word) =
    word_subword (word_reversefields 8 x:(128)word) (0,64):(64)word`,
  CONV_TAC WORD_BLAST);;

let WORD_REVERSEFIELDS_XOR_8_128 = prove(
  `!(x:(128)word) (y:(128)word).
    word_reversefields 8 (word_xor x y) =
    word_xor (word_reversefields 8 x) (word_reversefields 8 y)`,
  CONV_TAC WORD_BLAST);;

let KAR_MID_BRIDGE = prove(
  `!(xi:(128)word) (ct:(128)word).
    word_xor (word_subword (word_reversefields 8 xi) (64,64):(64)word)
             (word_xor (word_subword (word_reversefields 8 ct) (64,64))
                       (word_subword (word_reversefields 8 (word_xor xi ct)) (0,64))) =
    word_xor (word_subword (word_reversefields 8 (word_xor xi ct)) (0,64))
             (word_subword (word_reversefields 8 (word_xor xi ct)) (64,64))`,
  REWRITE_TAC[WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  CONV_TAC WORD_RULE);;

let HALFSWAP_XOR = prove(
  `!(a:(128)word) (b:(128)word).
    word_xor
      (word_join (word_join (word_subword a (64,64):(64)word) (word_subword a (0,64):(64)word):(128)word)
                 (word_join (word_subword a (64,64):(64)word) (word_subword a (0,64):(64)word):(128)word):(256)word)
      (word_join b b:(256)word) =
    word_join (word_xor a b:(128)word) (word_xor a b:(128)word):(256)word`,
  CONV_TAC WORD_BLAST);;

let REV8_JOIN_FOLD = prove(
  `!(lo:(64)word) (hi:(64)word).
    word_join (word_reversefields 8 lo) (word_reversefields 8 hi):(128)word =
    word_reversefields 8 (word_join hi lo:(128)word)`,
  CONV_TAC WORD_BLAST);;
