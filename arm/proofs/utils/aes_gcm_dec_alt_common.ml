(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The part of the proofs of the 8-way AES-GCM decrypt kernels               *)
(* aes128_gcm_dec_alt and aes256_gcm_dec_alt that does not depend on the key *)
(* size or the machine code: the GHASH/Karatsuba bridge and its N-block      *)
(* layer, the SIMD-fold simulation helpers, the counter core (gcm_ctr_inc    *)
(* and its relation to NIST inc32), the int128 byte-list lemmas, the decrypt *)
(* specification, and the key-size independent tactics and goal builders of  *)
(* the two proofs.  Both proofs load it.  Addresses, labels and step numbers *)
(* in the comments are those of the AES-256 kernel.                          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/aes_gcm_common.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;
needs "arm/proofs/utils/aes_xts_common.ml";;

(* ========================================================================= *)
(* N-block GHASH Karatsuba layer.                                            *)
(*                                                                           *)
(* Contents: HELPER_3 and GHASH_POLYVAL_ACC_3/4/5 (3/4/5-block Horner        *)
(* unrolling), the KARATSUBA_LIMBS lemmas, and the layer of                  *)
(* karatsuba_block_p{l,h,m}, kara_acc, pack_corrected, kara_quad_* and       *)
(* project_triples, whose KARA_ACC_PACK_HELPER equates the packed            *)
(* XOR-accumulated per-block Karatsuba triples with the XOR of the per-block *)
(* word_pmul products.                                                       *)
(*                                                                           *)
(* It builds on common/polyval_ghash.ml and common/karatsuba_pmul.ml.        *)
(* ========================================================================= *)


(* ---- GHASH spec extras (3/4/5-block Horner unrolling) ---- *)

(* Helper:                                                                   *)
(*   polyval_dot(a XOR p, h)*h^2 == a*h^3 + p*h^3 (mod Q), where             *)
(*   h^2 = polyval_dot h h and h^3 = polyval_dot h (polyval_dot h h).        *)
(* It bridges via INNER_CONG_GEN, after commuting the two factors of         *)
(* polyval_dot h h^2 (by WORD_PMUL_SYM).                                     *)

let HELPER_3 = prove
 (`!(a:int128) (p:int128) (h:int128).
    (ring_mul bool_poly (poly_of_word (polyval_dot (word_xor a p) h))
       (poly_of_word (polyval_dot h h)) ==
     ring_add bool_poly
       (ring_mul bool_poly (poly_of_word a) (poly_of_word (polyval_dot h (polyval_dot h h))))
       (ring_mul bool_poly (poly_of_word p) (poly_of_word (polyval_dot h (polyval_dot h h)))))
    mod_polyval`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
    `ring_mul bool_poly
      (ring_add bool_poly (poly_of_word (a:int128)) (poly_of_word (p:int128)))
      (poly_of_word (polyval_dot (h:int128) (polyval_dot h h)))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `polyval_dot (h:int128) (polyval_dot h h) = polyval_dot (polyval_dot (h:int128) h) h`
      SUBST1_TAC THENL
     [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:int128`; `word_xor (a:int128) (p:int128)`; `1`] INNER_CONG_GEN) THEN
    REWRITE_TAC[TWO; ONE; h_power; POLY_OF_WORD_XOR];
    MATCH_MP_TAC MOD_POLYVAL_REFL_GEN THEN
    SIMP_TAC[RING_MUL; RING_ADD; BOOL_POLY_OF_WORD] THEN
    MATCH_MP_TAC(GSYM RING_ADD_RDISTRIB) THEN REWRITE_TAC[BOOL_POLY_OF_WORD]]);;

let GHASH_POLYVAL_ACC_3 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128).
    ghash_polyval_acc h a [p:int128; q; r] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot h (polyval_dot h h)) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot h h) : 256 word)
        (word_pmul r h : 256 word)))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ghash_polyval_acc] THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_2] THEN
  REWRITE_TAC[WORD_PMUL_XOR] THEN
  MATCH_MP_TAC(ISPEC `128` MOD_POLYVAL_CANCEL_VARPOW) THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
    `poly_of_word (word_xor
      (word_xor (word_pmul (polyval_dot (word_xor (a:int128) (p:int128)) (h:int128)) (polyval_dot h h))
                (word_pmul (q:int128) (polyval_dot h h)))
      (word_pmul (r:int128) (h:int128)) : 256 word)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[POLYVAL_REDUCE_PROP3_CORRECT];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
    `poly_of_word (word_xor
      (word_xor (word_pmul (a:int128) (polyval_dot h (polyval_dot h h)))
                (word_pmul (p:int128) (polyval_dot h (polyval_dot h h))))
      (word_xor (word_pmul (q:int128) (polyval_dot h h))
                (word_pmul (r:int128) (h:int128))) : 256 word)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[POLYVAL_REDUCE_PROP3_CORRECT];
    ALL_TAC] THEN
  REWRITE_TAC[POLY_OF_WORD_XOR; POLY_OF_WORD_PMUL_2N] THEN
  MP_TAC(SPECL [`a:int128`; `p:int128`; `h:int128`] HELPER_3) THEN
  REWRITE_TAC[mod_polyval] THEN DISCH_TAC THEN
  ABBREV_TAC `pX = ring_mul bool_poly (poly_of_word (polyval_dot (word_xor (a:int128) (p:int128)) (h:int128))) (poly_of_word (polyval_dot (h:int128) h))` THEN
  ABBREV_TAC `pY = ring_add bool_poly
    (ring_mul bool_poly (poly_of_word (a:int128)) (poly_of_word (polyval_dot (h:int128) (polyval_dot h h))))
    (ring_mul bool_poly (poly_of_word (p:int128)) (poly_of_word (polyval_dot (h:int128) (polyval_dot h h))))` THEN
  ABBREV_TAC `pQ = ring_mul bool_poly (poly_of_word (q:int128)) (poly_of_word (polyval_dot (h:int128) h))` THEN
  ABBREV_TAC `pR = ring_mul bool_poly (poly_of_word (r:int128)) (poly_of_word (h:int128))` THEN
  SUBGOAL_THEN
    `pX IN ring_carrier bool_poly /\ pY IN ring_carrier bool_poly /\ pQ IN ring_carrier bool_poly /\ pR IN ring_carrier bool_poly`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["pX"; "pY"; "pQ"; "pR"] THEN
    SIMP_TAC[RING_MUL; RING_ADD; BOOL_POLY_OF_WORD];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `ring_add bool_poly (ring_add bool_poly pX pQ) pR =
     ring_add bool_poly pX (ring_add bool_poly pQ pR)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM RING_ADD_ASSOC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOD_POLYVAL_ADD THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOD_POLYVAL_REFL_GEN THEN ASM_SIMP_TAC[RING_ADD]]);;

(* ========================================================================= *)
(* GHASH_POLYVAL_ACC_4: the 4-block Horner unrolling, derived directly from  *)
(* GHASH_POLYVAL_ACC_BATCHED for the list [p;q;r;s]; it unfolds h_power 0..3 *)
(* to the polyval_dot chain (h, h^2, h^3, h^4).                              *)
(* ========================================================================= *)

let GHASH_POLYVAL_ACC_4 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128).
    ghash_polyval_acc h a [p:int128; q; r; s] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot h h) : 256 word)
        (word_pmul s h : 256 word))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;

(* ========================================================================= *)
(* GHASH_POLYVAL_ACC_5: the 5-block Horner unrolling, derived directly from  *)
(* GHASH_POLYVAL_ACC_BATCHED for the list [p;q;r;s;t]; it unfolds h_power    *)
(* 0..4 to the polyval_dot chain (h, h^2, h^3, h^4, h^5).                    *)
(* ========================================================================= *)

let GHASH_POLYVAL_ACC_5 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot h h) : 256 word)
        (word_pmul t h : 256 word)))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;

(* ---- the N-block Karatsuba layer ---- *)
let WORD_XOR_0_LEFT = WORD_BITWISE_RULE `word_xor (word 0) x = (x:(N)word)`;;

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

let BYTESWAP128_SUBWORD_LO = prove(
  `!(h:int128). word_subword (byteswap128 h) (0,64):(64)word = word_subword h (64,64)`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let BYTESWAP128_SUBWORD_HI = prove(
  `!(h:int128). word_subword (byteswap128 h) (64,64):(64)word = word_subword h (0,64)`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

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

(* ========================================================================= *)
(* Packing the accumulated Karatsuba triples.                                *)
(*                                                                           *)
(* KARA_ACC_PACK_HELPER is proved by induction on the block list from two    *)
(* structural lemmas:                                                        *)
(*                                                                           *)
(*   KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN:                                    *)
(*      pack_corrected (pl_k, ph_k, pm_k) = pmul input_k h_k (256-bit)       *)
(*      under the precondition that hk's low half = karatsuba_mid h_k.       *)
(*                                                                           *)
(*   PACK_CORRECTED_XOR (additivity / linearity):                            *)
(*      pack_corrected commutes with XOR in all three arguments.             *)
(*                                                                           *)
(* kara_acc XOR-folds the per-block (pl, ph, pm), pack_corrected distributes *)
(* over XOR, and each block contributes pmul input_k h_k, so the packed      *)
(* accumulator is the XOR of the per-block products (kara_quad_pmul).        *)
(* ========================================================================= *)

(* Pack-corrected: combines (pl, ph, pm) into the 256-bit Karatsuba layout
   (with mid corrected by XOR pl XOR ph). *)
let pack_corrected = new_definition
 `pack_corrected (pl:int128) (ph:int128) (pm:int128) :256 word =
   word_xor (word_xor
     (word_zx pl :256 word)
     (word_shl (word_zx (word_xor (word_xor pl ph) pm) :256 word) 64))
    (word_shl (word_zx ph :256 word) 128)`;;

(* Per-block pack identity. *)
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

(* pack_corrected is XOR-additive in each argument. *)
let PACK_CORRECTED_XOR = prove
 (`!pl1 ph1 pm1 pl2 ph2 pm2:int128.
   pack_corrected (word_xor pl1 pl2) (word_xor ph1 ph2) (word_xor pm1 pm2) =
   word_xor (pack_corrected pl1 ph1 pm1) (pack_corrected pl2 ph2 pm2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pack_corrected; WORD_ZX_XOR; WORD_SHL_XOR] THEN
  CONV_TAC WORD_RULE);;

(* One kara_acc step (KARA_ACC_CONS_DESTR) and the linearity of kara_acc
   (KARA_ACC_FIRST): starting at (pl0, ph0, pm0) is the same as starting at
   (0,0,0) and XOR-ing the start into the result. *)
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

(* Lists of quads (input, h_tw, hk, h), one per block: kara_quad_pmul XORs the
   products word_pmul input h into acc; kara_quad_ok is the bridge precondition
   that every triple comes from a real key h (h_tw = byteswap128 h, and the low
   half of hk is karatsuba_mid h); project_triples drops the h. *)
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

(* The inductive helper: under kara_quad_ok, kara_quad_pmul quads acc is acc
   XOR the packed kara_acc of the projected triples. *)
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

(* ============================================================================
   The GMULTn builder for the band proofs.

   `build_GMULTn_fast n` returns a pair (PACKn_ID, GMULTn_FULL_CORRECT_BA):
     - PACKn_ID               : decN_tL = XOR_k (word_pmul a_k b_k)  (256-bit)
     - GMULTn_FULL_CORRECT_BA : the machine's Karatsuba-limb byteform =
                                polyval_reduce_prop3 (XOR_k word_pmul a_k b_k)

   Method: prove `decN_tL = XOR_k dec1[k]` structurally by XOR-AC over opaque
   pmul atoms (`AC WORD_XOR_ACI`, no bit-blast; a direct WORD_RULE proof of
   the 256-bit identity does not scale with N), then fold each single-block
   `dec1[k]` to `word_pmul a_k b_k` by PMUL_KARATSUBA.  This is the shared
   GHASH-bridge multiply lemma of the 2..8-block bands.

   It needs PMUL_KARATSUBA (common/karatsuba_pmul.ml) and KARATSUBA_LIMBS
   (above); the shared Prop3 reduction lemma GMULT_REDUCE_PROP3 and its
   helper V0LO are proved here.
   ========================================================================= *)


(* XOR is associative and commutative; WORD_XOR_ACI is the rewrite set of the
   structural `decN_tL = XOR_k dec1[k]` normalization (opaque pmul atoms, no
   bit-blast). *)
let WORD_XOR_ACI = WORD_RULE
  `(!x y:N word. word_xor x y = word_xor y x) /\
   (!x y z:N word. word_xor (word_xor x y) z = word_xor x (word_xor y z)) /\
   (!x y z:N word. word_xor x (word_xor y z) = word_xor y (word_xor x z))`;;

(* Helper: the low 64-bit lane of v0 = word_join aa bb XOR wa.  It makes the
   `word_pmul _ W` atoms of GMULT and Prop3 syntactically identical; pmul is
   opaque to BITBLAST, so the wv-inputs must match before the lane blast. *)
let V0LO = prove(
  `!aa bb:64 word. !wa:int128.
     word_subword (word_xor (word_join aa bb:int128) wa) (0,64):64 word =
     word_xor bb (word_subword wa (0,64):64 word)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* The shared Prop3 reduction: the GMULT/assembly W-reduction byteform over an
   abstract 256-bit accumulator t equals polyval_reduce_prop3 t.  aa/bb/cc/dd
   are t's four 64-bit lanes and w = 0xC200000000000000.  It serves every block
   count: an N-block group reduces its accumulated 256-bit sum once. *)
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

let mk_sub v lo = mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, v), mk_pair(mk_small_numeral lo,`64`));;

let blk_lo k =
  let a = mk_var(Printf.sprintf "a%d" k,`:int128`) and b = mk_var(Printf.sprintf "b%d" k,`:int128`) in
  mk_comb(mk_comb(`word_pmul:64 word->64 word->128 word`, mk_sub a 0), mk_sub b 0);;

let blk_hi k =
  let a = mk_var(Printf.sprintf "a%d" k,`:int128`) and b = mk_var(Printf.sprintf "b%d" k,`:int128`) in
  mk_comb(mk_comb(`word_pmul:64 word->64 word->128 word`, mk_sub a 64), mk_sub b 64);;

let blk_mid k =
  let a = mk_var(Printf.sprintf "a%d" k,`:int128`) and b = mk_var(Printf.sprintf "b%d" k,`:int128`) in
  let xa = mk_comb(mk_comb(`word_xor:64 word->64 word->64 word`, mk_sub a 0), mk_sub a 64) in
  let xb = mk_comb(mk_comb(`word_xor:64 word->64 word->64 word`, mk_sub b 0), mk_sub b 64) in
  let pmid = mk_comb(mk_comb(`word_pmul:64 word->64 word->128 word`, xa), xb) in
  let xor128 x y = mk_comb(mk_comb(`word_xor:128 word->128 word->128 word`,x),y) in
  xor128 (xor128 pmid (blk_lo k)) (blk_hi k);;

let xor_fold128 f n =
  let xs = map f (0--(n-1)) in
  let rec go = function [x] -> x | x::xs -> mk_comb(mk_comb(`word_xor:128 word->128 word->128 word`,x), go xs) | [] -> failwith "empty" in
  go xs;;

let mk_decN_tL n =
  let zx t = mk_comb(`word_zx:128 word->256 word`, t) in
  let shl t k = mk_comb(mk_comb(`word_shl:256 word->num->256 word`, t), mk_small_numeral k) in
  let xor256 x y = mk_comb(mk_comb(`word_xor:256 word->256 word->256 word`,x),y) in
  xor256 (xor256 (zx (xor_fold128 blk_lo n)) (shl (zx (xor_fold128 blk_mid n)) 64))
         (shl (zx (xor_fold128 blk_hi n)) 128);;

let blkvars n = List.concat (map (fun k -> [mk_var(Printf.sprintf "a%d" k,`:int128`); mk_var(Printf.sprintf "b%d" k,`:int128`)]) (0--(n-1)));;

let dec1_at k =
  subst [mk_var(Printf.sprintf "a%d" k,`:int128`),`a0:int128`;
         mk_var(Printf.sprintf "b%d" k,`:int128`),`b0:int128`] (mk_decN_tL 1);;

let xor256_fold ts = match ts with
  | x::r -> List.fold_left (fun a y->mk_comb(mk_comb(`word_xor:256 word->256 word->256 word`,a),y)) x r
  | []->failwith"";;

(* decN_tL = XOR_k dec1[k], structural XOR-AC (no bit-blast) *)
let build_SPLIT n =
  let lf = REWRITE_CONV[WORD_ZX_XOR; WORD_SHL_XOR] (mk_decN_tL n)
  and rf = REWRITE_CONV[WORD_ZX_XOR; WORD_SHL_XOR] (xor256_fold (map dec1_at (0--(n-1)))) in
  TRANS lf (TRANS (AC WORD_XOR_ACI (mk_eq(rhs(concl lf), rhs(concl rf)))) (SYM rf));;

let pack1_at k =
  let ak=mk_var(Printf.sprintf "a%d" k,`:int128`) and bk=mk_var(Printf.sprintf "b%d" k,`:int128`) in
  prove(mk_eq(dec1_at k, mk_comb(mk_comb(`word_pmul:int128->int128->256 word`,ak),bk)),
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REWRITE_RULE[LET_DEF;LET_END_DEF] PMUL_KARATSUBA] THEN
    REWRITE_TAC[WORD_ZX_XOR; WORD_SHL_XOR] THEN CONV_TAC WORD_RULE);;

let build_PACKn n =
  let split = build_SPLIT n in
  TRANS split (GEN_REWRITE_CONV ONCE_DEPTH_CONV (map pack1_at (0--(n-1))) (rhs(concl split)));;

let build_GMULTn_fast n =
  let pack_id = build_PACKn n in
  let tL = lhs(concl pack_id) in
  let gmr = REWRITE_RULE[REWRITE_RULE[LET_DEF;LET_END_DEF] KARATSUBA_LIMBS]
              (SPEC tL (REWRITE_RULE[LET_DEF;LET_END_DEF] GMULT_REDUCE_PROP3)) in
  (pack_id, GENL (blkvars n) (TRANS gmr (AP_TERM `polyval_reduce_prop3` pack_id)));;

(* ========================================================================= *)
(* AES-GCM counter-mode helpers (binary-agnostic spec layer).                *)
(*                                                                           *)
(* The counter core of the proof: the per-block counter increment of the     *)
(* kernel (gcm_ctr_inc), its lane-byte form (GCM_CTR_INC_LANES), the NIST SP *)
(* 800-38D inc32 and the byteswap bridge between them, and the counter       *)
(* iterator gcm_ctr_inc_iter, a definition, so that block k's counter        *)
(* composes in a recursion or an N-block induction.                          *)
(*                                                                           *)
(* This counter vocabulary is private, next to the shared ctr_block of       *)
(* aes_gcm_spec.ml, because gcm_ctr_inc is the update in exactly the form    *)
(* the simulation produces (rev32, add, rev32 on the top lane of the counter *)
(* register): the simulated postconditions of the proofs are stated with     *)
(* gcm_ctr_inc and gcm_ctr_inc_iter (and with the proof's own gcm_ctr_add    *)
(* and gcm_ctr_raw).  Restating them would mean re-simulating; instead the   *)
(* exported theorems are moved to ctr_block nonce c by                       *)
(* GCM_CTR_INC_ITER_INC32 below and the bridges GCM_CTR_INC_ITER_CTR_BLOCK   *)
(* and GCM_CTR_INC_ITER_NIST_IVEC further down.                              *)
(* ========================================================================= *)


(* ========================================================================= *)
(* The AES-GCM counter increment (the kernel's rev32, add, rev32).           *)
(*                                                                           *)
(* gcm_ctr_inc ivec = ivec with its top 32-bit lane byte-reversed, +1, and   *)
(* byte-reversed back.                                                       *)
(* ========================================================================= *)

let gcm_ctr_inc = new_definition
 `gcm_ctr_inc (ivec:(128)word) : (128)word =
   word_insert ivec (96,32)
     (word_bytereverse
        (word_add (word_bytereverse
                     (word_subword ivec (96,32):(32)word))
                  (word 1:(32)word)))`;;

(* gcm_ctr_inc as the byte-level lane form the simulation produces: the top  *)
(* 32-bit lane is the byte-reversed top lane of ctr0 plus one, byte-reversed *)
(* back, and the low 96 bits are those of ctr0, all built from the 8-bit     *)
(* subwords of ctr0.  The proofs rewrite between gcm_ctr_inc ctr0 and this   *)
(* form; GCM_CTR_INC2..7_LANES and GCM_CTR_ADD_LANES are built from it.      *)
let GCM_CTR_INC_LANES = prove(
 `!ctr0:int128.
    gcm_ctr_inc ctr0 =
    word_join
    (word_join
     (word_join
      (word_join
       (word_subword
        (word_add
         (word_join
          (word_join (word_subword ctr0 (96,8):(8)word) (word_subword ctr0 (104,8):(8)word)
           :(16)word)
          (word_join (word_subword ctr0 (112,8):(8)word) (word_subword ctr0 (120,8):(8)word)
           :(16)word) :(32)word)
         (word 1:(32)word)) (0,8) :(8)word)
       (word_subword
        (word_add
         (word_join
          (word_join (word_subword ctr0 (96,8):(8)word) (word_subword ctr0 (104,8):(8)word)
           :(16)word)
          (word_join (word_subword ctr0 (112,8):(8)word) (word_subword ctr0 (120,8):(8)word)
           :(16)word) :(32)word)
         (word 1:(32)word)) (8,8) :(8)word) :(16)word)
      (word_join
       (word_subword
        (word_add
         (word_join
          (word_join (word_subword ctr0 (96,8):(8)word) (word_subword ctr0 (104,8):(8)word)
           :(16)word)
          (word_join (word_subword ctr0 (112,8):(8)word) (word_subword ctr0 (120,8):(8)word)
           :(16)word) :(32)word)
         (word 1:(32)word)) (16,8) :(8)word)
       (word_subword
        (word_add
         (word_join
          (word_join (word_subword ctr0 (96,8):(8)word) (word_subword ctr0 (104,8):(8)word)
           :(16)word)
          (word_join (word_subword ctr0 (112,8):(8)word) (word_subword ctr0 (120,8):(8)word)
           :(16)word) :(32)word)
         (word 1:(32)word)) (24,8) :(8)word) :(16)word) :(32)word)
     (word_join
      (word_join (word_subword ctr0 (88,8):(8)word) (word_subword ctr0 (80,8):(8)word) :(16)word)
      (word_join (word_subword ctr0 (72,8):(8)word) (word_subword ctr0 (64,8):(8)word) :(16)word)
      :(32)word) :(64)word)
    (word_join
     (word_join
      (word_join (word_subword ctr0 (56,8):(8)word) (word_subword ctr0 (48,8):(8)word) :(16)word)
      (word_join (word_subword ctr0 (40,8):(8)word) (word_subword ctr0 (32,8):(8)word) :(16)word)
      :(32)word)
     (word_join
      (word_join (word_subword ctr0 (24,8):(8)word) (word_subword ctr0 (16,8):(8)word) :(16)word)
      (word_join (word_subword ctr0 (8,8):(8)word) (word_subword ctr0 (0,8):(8)word) :(16)word)
      :(32)word) :(64)word) :(128)word`,
  GEN_TAC THEN REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

(* ========================================================================= *)
(* The byteswap bridge from gcm_ctr_inc to NIST SP 800-38D inc32             *)
(* ========================================================================= *)

(* GCM_CTR_INC_INC32: the NIST inc32 and the kernel's gcm_ctr_inc are        *)
(* conjugate by a full 128-bit byte reversal.  inc32 increments the low 32   *)
(* bits of its argument (the NIST big-endian counter) and keeps the top 96;  *)
(* gcm_ctr_inc increments the top 32-bit lane read byte-reversed.  So        *)
(* gcm_ctr_inc x = word_bytereverse (inc32 (word_bytereverse x)).            *)
let GCM_CTR_INC_INC32 = prove
 (`!x:128 word. gcm_ctr_inc x = word_bytereverse (inc32 (word_bytereverse x))`,
  GEN_TAC THEN REWRITE_TAC[gcm_ctr_inc; inc32] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BITBLAST_TAC);;

(* ========================================================================= *)
(* The counter iterator: block k's counter block is gcm_ctr_inc_iter k ctr0. *)
(* It is a definition, so that it composes in a recursion or an N-block      *)
(* induction; it equals ITER k gcm_ctr_inc, so the ITER lemmas apply.        *)
(* ========================================================================= *)

let gcm_ctr_inc_iter = define
 `gcm_ctr_inc_iter 0 (x:128 word) = x /\
  gcm_ctr_inc_iter (SUC k) (x:128 word) = gcm_ctr_inc (gcm_ctr_inc_iter k x)`;;

(* The iterated NIST bridge: it lets the specification state block k's       *)
(* counter NIST-faithfully (ITER k inc32 over the byte-reversed ivec) while  *)
(* the proof folds the kernel's lanes with gcm_ctr_inc_iter.                 *)
let GCM_CTR_INC_ITER_INC32 = prove
 (`!k x:128 word.
     gcm_ctr_inc_iter k x = word_bytereverse (ITER k inc32 (word_bytereverse x))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[gcm_ctr_inc_iter; ITER; WORD_BYTEREVERSE_BYTEREVERSE];
    ASM_REWRITE_TAC[gcm_ctr_inc_iter; ITER; GCM_CTR_INC_INC32;
                    WORD_BYTEREVERSE_BYTEREVERSE]]);;

(* ========================================================================= *)
(* Byte-list view of a block list, for a byte_list_at(out_p,len)             *)
(* postcondition, on the XTS substrate int128_to_bytes.                      *)
(* ========================================================================= *)

(* Flatten an int128 block list to a byte list (APPEND of int128_to_bytes),  *)
(* exactly the XTS APPEND-of-int128_to_bytes shape.                          *)
let int128_list_to_bytes = define
 `int128_list_to_bytes ([]:int128 list) : byte list = [] /\
  int128_list_to_bytes (CONS w ws) =
    APPEND (int128_to_bytes w) (int128_list_to_bytes ws)`;;

(* LENGTH of the flattened byte list = 16 * number of blocks.                *)
let LENGTH_INT128_TO_BYTES = prove
 (`!w:int128. LENGTH(int128_to_bytes w) = 16`,
  REWRITE_TAC[int128_to_bytes; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let LENGTH_INT128_LIST_TO_BYTES = prove
 (`!ws. LENGTH(int128_list_to_bytes ws) = 16 * LENGTH ws`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[int128_list_to_bytes; LENGTH; LENGTH_APPEND;
                  LENGTH_INT128_TO_BYTES] THEN ARITH_TAC);;

(* ========================================================================= *)
(* Byte-extraction sublemmas for the whole-block byte_list_at bridges of the *)
(* proofs: a bytes128 read seen as its 16 bytes8 reads, and byte i of an     *)
(* int128 (or of a flattened int128 list) as a word_subword.                 *)
(* BYTES128_TO_BYTES8_THM itself is in aes_xts_common.ml.                    *)
(* ========================================================================= *)

let BYTES128_TO_BYTES8_0 =
  REWRITE_RULE[ADD_CLAUSES; WORD_ADD_0] (SPEC `0` BYTES128_TO_BYTES8_THM);;

let SUBWORD_BYTES_TO_INT128 = prove(
 `!b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 i. i < 16
   ==> word_subword (bytes_to_int128 [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]) (8*i,8):byte =
       EL i [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[bytes_to_int128] THEN REWRITE_TAC EL_16_8_CLAUSES THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC WORD_BLAST);;

let BYTE8_OF_BYTES128 = prove(
 `!p s i. i < 16 ==> read (memory :> bytes8 (word_add p (word i))) s =
                     word_subword (read (memory :> bytes128 p) s) (8*i,8)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [BYTES128_TO_BYTES8_0] THEN
  ASM_SIMP_TAC[SUBWORD_BYTES_TO_INT128] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN REWRITE_TAC[WORD_ADD_0]);;

let EL_INT128_TO_BYTES = prove(
 `!w i. i < 16 ==> EL i (int128_to_bytes w):byte = word_subword w (8*i,8)`,
  GEN_TAC THEN REWRITE_TAC[int128_to_bytes] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC EL_16_8_CLAUSES THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REWRITE_TAC[]);;

(* num DIV/MOD step lemmas for the int128_list_to_bytes per-byte unfolding.  *)
let DIV16_STEP = prove
 (`!i. 16 <= i ==> i DIV 16 = SUC((i - 16) DIV 16)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i = (i - 16) + 1 * 16` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC]);;

let MOD16_STEP = prove
 (`!i. 16 <= i ==> i MOD 16 = (i - 16) MOD 16`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i MOD 16 = ((i - 16) + 1 * 16) MOD 16` SUBST1_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[MOD_MULT_ADD]]);;

(* byte i of the flattened block list = byte (i MOD 16) of block (i DIV 16). *)
let EL_INT128_LIST_TO_BYTES = prove
 (`!cts i. i < 16 * LENGTH cts
     ==> EL i (int128_list_to_bytes cts) =
         word_subword (EL (i DIV 16) cts) (8 * (i MOD 16), 8):byte`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; int128_list_to_bytes; MULT_CLAUSES] THENL
   [REWRITE_TAC[LT] THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH(int128_to_bytes h) = 16` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_INT128_TO_BYTES]; ALL_TAC] THEN
  ASM_CASES_TAC `i < 16` THENL
   [ASM_SIMP_TAC[EL_APPEND] THEN
    SUBGOAL_THEN `i DIV 16 = 0 /\ i MOD 16 = i`
      (fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th; EL; HD]) THENL
     [ASM_SIMP_TAC[DIV_LT; MOD_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_INT128_TO_BYTES];
    ASM_SIMP_TAC[EL_APPEND] THEN
    SUBGOAL_THEN `i - 16 < 16 * LENGTH(t:int128 list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `16 <= i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DIV16_STEP; MOD16_STEP; EL; TL]]);;

(* ========================================================================= *)
(* Generic GCM machinery (direction-agnostic).                               *)
(*                                                                           *)
(* Nothing from here to the decrypt-specific section below depends on the    *)
(* direction: it is word and SIMD algebra, the GHASH/Karatsuba bridge layer, *)
(* exec-parameterized steppers, and N-block byteform merge and close tactics *)
(* that would serve the encrypt kernels as well.                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* SIMD REV64 fold-back lemmas.  The ARM simulator expands REV64.16B into a  *)
(* 4-level nested word_join/word_subword byte tree (128->64->32->16->8).     *)
(* These lemmas collapse it back to word_reversefields 8 as soon as it       *)
(* appears, so the large byte tree never builds up.                          *)
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

(* The tails compute Karatsuba middle terms with
   `ext vD.16b,vN.16b,vN.16b,#8`, which the stepper models on a 128-bit
   register as `word_subword (word_join vN vN:256 word) (64,128):128 word`
   (a rotation by 64).  Only lane 0 of such a result is read (by an
   `eor .8b` or a `pmull .1d`), that is the projection
   `word_subword (<ext form>) (0,64)`, which is the plain lane
   `word_subword vN (64,64)`, the value an `ins vD.d[0],vN.d[1]` would give.
   EXT8_LANE0_IS_SUBWORD_HI rewrites that composed projection, not the
   standalone register: that would also fire on the byteswap/REV64
   machinery, which uses the same word_subword (word_join a a) (64,128)
   shape.  So the bridges see plain lanes, and ABBREV_INNER_PMULS_TAC
   numbers the qq atoms as for the ins form.  This is the identity
   SJ_COLLAPSE of the band machinery further down, stated here so that the
   per-step normalizer GCM_SIMD_SIMPLIFY_CORE_TAC can use it. *)
let EXT8_LANE0_IS_SUBWORD_HI = prove(
  `!(w:(128)word).
    word_subword (word_subword (word_join w w:(256)word) (64,128):(128)word) (0,64):(64)word =
    word_subword w (64,64)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Structural normalization lemmas for the GHASH bridge close (word_insert
   comes from an ins, mov vD.d[i], and the nested word_subword from an ext). *)
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
(* GHASH bridge lemmas: helpers for showing that the Karatsuba + Prop3       *)
(* reduction the assembly computes equals the spec-level polyval_dot /       *)
(* ghash_polyval_acc, so that the symbolic Q19 result at the tag_p store can *)
(* be bridged to the postcondition.                                          *)
(* ------------------------------------------------------------------------- *)

let KARATSUBA_LIMBS_LET = prove(
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

let GHASH_1BLOCK_CORRECT = prove(
  `!acc block h:int128.
    polyval_dot (word_xor acc block) h = ghash_polyval_acc h acc [block]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ghash_polyval_acc; polyval_dot]);;

let BYTESWAP128_INVOLUTION = prove(
  `!x:int128. byteswap128(byteswap128 x) = x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128] THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* A GHASH bridge helper lemma.                                              *)
(* ------------------------------------------------------------------------- *)

(* word_subword (word_insert x (0,64) y) (0,64) = word_subword y (0,64),     *)
(* which drops the leftover tag tree x from the Karatsuba cross-term of the  *)
(* GHASH byte form.                                                          *)
let INSERT_SUBWORD_KILL = prove(
  `!(x:(128)word) (y:(128)word).
     word_subword ((word_insert x (0,64) y):(128)word) (0,64):(64)word
     = word_subword y (0,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Scalable (a)+(b) decomposition of the GHASH multiply+reduce bridge.       *)
(*                                                                           *)
(* The 8-way kernels accumulate the Karatsuba products of a group of up to 8 *)
(* blocks in Q17/Q18/Q19 and apply one shared Prop3 reduction per group.     *)
(* Factoring the bridge as (a)+(b) makes both pieces reusable at every block *)
(* count (1..8), composed with the list-generic GHASH_POLYVAL_ACC_BATCHED    *)
(* (common/polyval_ghash.ml):                                                *)
(*   (a) PMUL_KARATSUBA (common/karatsuba_pmul.ml): the per-block 3-pmull    *)
(*       (lo/hi/mid) byteform = word_pmul a b (the 256-bit product);         *)
(*   (b) GMULT_REDUCE_PROP3 (above): the assembly's W-reduction byteform     *)
(*       over an abstract 256-bit accumulator t = polyval_reduce_prop3 t.    *)
(* ------------------------------------------------------------------------- *)

(* The full GHASH multiply+reduce bridge: the byte-level Karatsuba/Prop3 the *)
(* assembly computes (the left-hand side, over 64-bit pmul limbs) equals the *)
(* spec-level polyval_dot.  Derived from (a) PMUL_KARATSUBA, (b)             *)
(* GMULT_REDUCE_PROP3 and KARATSUBA_LIMBS_LET (the lanes of word_pmul a b    *)
(* are the limbs), instead of a single monolithic BITBLAST.                  *)
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
  (* Compose (a)+(b):
       polyval_dot a b = polyval_reduce_prop3 (word_pmul a b)        [def];
       word_pmul a b = the Karatsuba 256-bit assembly K  [(a) PMUL_KARATSUBA];
       polyval_reduce_prop3 K = the W-reduction byteform over K's lanes
                                           [GSYM (b) GMULT_REDUCE_PROP3];
       K's lanes = the p_lo/cross/p_hi limbs           [KARATSUBA_LIMBS_LET];
     then the two byteforms are identical up to the pmul argument order
     [WORD_PMUL_SYM]. *)
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[polyval_dot] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  GEN_REWRITE_TAC RAND_CONV
    [GSYM (REWRITE_RULE[LET_DEF; LET_END_DEF] GMULT_REDUCE_PROP3)] THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] KARATSUBA_LIMBS_LET] THEN
  REWRITE_TAC[WORD_PMUL_SYM] THEN REFL_TAC);;

let SIMD_SIMPLIFY_RULES = [REV64_LOWER_LANE; REV64_UPPER_LANE; REV64_128];;

let SIMD_SIMPLIFY_ASSUM_TAC =
  RULE_ASSUM_TAC(fun th ->
    try REWRITE_RULE SIMD_SIMPLIFY_RULES th with _ -> th);;

(* ------------------------------------------------------------------------- *)
(* REV32 (vector) per-32-bit-lane reversefields bridge.                      *)
(*                                                                           *)
(* The ISA model (arm/proofs/instruction.ml) defines arm_REV32_VEC with      *)
(*   usimd4 (word_reversefields esize) n,                                    *)
(* so arm_REV32_VEC_ALT (its EXPAND_SIMD_RULE form) leaves, per 32-bit lane, *)
(*   word_reversefields esize (word_subword n (32k,32)).                     *)
(* WORD_SIMPLE_SUBWORD_CONV does not reduce through word_reversefields, so   *)
(* that wrapper stays stuck, and a later positional RAND_CONV lands on a     *)
(* non-combination and fails ("RAND_CONV: Not a combination").  The decoder  *)
(* only emits esize 8 or 16 (decode.ml: esize = 8 << size with size in       *)
(* {0,1}; sizes 2 and 3 are UNDEFINED), so the two per-lane rewrites below,  *)
(* typed at :(32)word so that they never touch the 64-bit-lane               *)
(* word_reversefields of REV64 above, cover every REV32 the decoder can      *)
(* produce and let the subword chain reduce fully to the word_join /         *)
(* word_subword byte form the bridges expect.                                *)
(* ------------------------------------------------------------------------- *)
let WORD_REVERSEFIELDS_8_32 = prove
 (`word_reversefields 8 (x:(32)word) =
     word_join
       (word_join (word_subword x (0,8):(8)word) (word_subword x (8,8):(8)word):(16)word)
       (word_join (word_subword x (16,8):(8)word) (word_subword x (24,8):(8)word):(16)word)`,
  CONV_TAC WORD_BLAST);;

let WORD_REVERSEFIELDS_16_32 = prove
 (`word_reversefields 16 (x:(32)word) =
     word_join (word_subword x (0,16):(16)word) (word_subword x (16,16):(16)word)`,
  CONV_TAC WORD_BLAST);;

(* Reduce the stuck per-lane word_reversefields first (this fires only on a  *)
(* concrete esize 8 or 16, which the decoder supplies), then run the normal  *)
(* subword collapse.  With the ORELSEC inside a single TOP_DEPTH_CONV, the   *)
(* conversion never fails, and on terms without a 32-bit-lane reversefields  *)
(* it is a no-op.                                                            *)
let REV32_LANE_SUBWORD_CONV =
  TOP_DEPTH_CONV
    (GEN_REWRITE_CONV I [WORD_REVERSEFIELDS_8_32; WORD_REVERSEFIELDS_16_32]
     ORELSEC WORD_SIMPLE_SUBWORD_CONV);;

(* Per-step SIMD simplifier core: fold REV64 trees, cancel double half-swaps,
   collapse the lane-0 projections of ext (EXT8_LANE0_IS_SUBWORD_HI) and
   normalize nested subwords, also through REV32 lanes.  It runs after each
   GHASH step, so that the terms stay small. *)
let GCM_SIMD_SIMPLIFY_CORE_TAC =
  SIMD_SIMPLIFY_ASSUM_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [WORD_SWAP_HALVES_INVOLUTION; EXT8_LANE0_IS_SUBWORD_HI]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(REV32_LANE_SUBWORD_CONV)) th
    with _ -> th);;

(* The REV64 fold needs two passes: the first normalizes the nested
   word_subword tree, the second lets the REV64 lane rules (REV64_LOWER_LANE,
   REV64_UPPER_LANE, REV64_128) match.  Two passes reach a fixpoint on the
   terms of these proofs. *)
let GCM_SIMD_SIMPLIFY_TAC =
  GCM_SIMD_SIMPLIFY_CORE_TAC THEN GCM_SIMD_SIMPLIFY_CORE_TAC;;

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

(* Straight-line steps that keep the earlier states (ARM_VSTEPS_TAC), each
   followed by the SIMD fold; no branch resolution.  Used for short windows of
   the band tails, such as the stores and the ext/rev64 pair after the GHASH
   bridge: earlier facts such as the GHASH accumulators (Q17/Q18/Q19) and the
   store read-backs stay, and the fold keeps the REV64 byte trees bounded. *)
let ARM_VSTEPS_FOLD_TAC exec range =
  MAP_EVERY (fun n -> ARM_VSTEPS_TAC exec [n] THEN GCM_SIMD_SIMPLIFY_TAC) (range);;

(* A stepper for the windows with the REV64s of GHASH: the single step and
   discard of ARM_STEPS_TAC with the SIMD fold before each discard.  Per step:
     ARM_VERBOSE_STEP_TAC  -- advance to state s<n>
     GCM_SIMD_SIMPLIFY_TAC -- fold the REV64 byte tree into Q19
     DISCARD_OLDSTATE_TAC  -- drop the reads of earlier states
     CLARIFY_TAC
   The fold has to come before the discard: it collapses the byte tree into
   the bounded GHASH accumulator term in Q19, which then survives the
   discard.  Discarding at every step keeps the assumption list short. *)
let ARM_STEPS_FOLD_DISCARD_TAC exec snums =
  MAP_EVERY
    (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_TAC THEN
              DISCARD_OLDSTATE_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;

(* Discard the flag facts (read NF/ZF/CF/VF) but keep read PC, whose final
   value ENSURES_FINAL_STATE_TAC needs for the PC postcondition. *)
let DISCARD_COUNTER_ONLY_TAC =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    let s = string_of_term(concl th) in
    try String.sub s 0 7 = "read NF" ||
        String.sub s 0 7 = "read ZF" ||
        String.sub s 0 7 = "read CF" ||
        String.sub s 0 7 = "read VF"
    with _ -> false)));;

(* ------------------------------------------------------------------------- *)
(* GHASH bridge close.  At the bridge state of a one-block tail the assembly *)
(* holds in Q19 the Karatsuba+Prop3 GHASH of word_xor (brev xi) (brev ct)    *)
(* with key byteswap128 h (the key table holds H twisted, and the GHASH key  *)
(* is byteswap128 (read htable_p)).  GMULT_FULL_CORRECT_BA, with             *)
(*   b := byteswap128 h,                                                     *)
(* makes the lane operands match; the helpers below abbreviate the Karatsuba *)
(* pmul limbs to opaque atoms, merge atoms that are equal up to argument     *)
(* order (WORD_PMUL_SYM, the congruence PMUL_CONG_128), and leave a          *)
(* structural XOR/join/subword identity for the bit-blasting tactics.        *)
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

(* Abbreviate each innermost fully applied word_pmul to a fresh qqN:int128. *)
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

(* For each pair of pmul-atom definitions, try to prove the atoms equal (the
   same product up to argument order, by WORD_PMUL_SYM, with operands equal by
   WORD_BLAST) and rewrite to merge them. *)
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

(* Half projection helpers for the lane-fold close. *)
let JOINMID = prove(
  `!q:int128. word_subword (word_join q q :(256)word) (64,128):int128 =
     word_join (word_subword q (0,64):64 word) (word_subword q (64,64):64 word)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let QQ0SPLIT = prove(
  `!q:int128. q = word_join (word_subword q (64,64):64 word) (word_subword q (0,64):64 word)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ========================================================================= *)
(* N-block GHASH bridge infrastructure, used by the 2..8-block bands.        *)
(*                                                                           *)
(* Helper lemmas for the 2-product GHASH bridge (independent of the byte     *)
(* form, so they hold for either direction) and the pmul-atom merge tactics. *)
(* ========================================================================= *)

(* word_join lane split: reduces a 128-bit word_join equality to two 64-bit  *)
(* lane equalities (so the final close is two small flat XOR identities).    *)
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

(* Per-lane reversefields: word_reversefields 8 on a full int128 commutes    *)
(* with the 64-bit lane projection (with a lane swap).                       *)
let RF8_SUBWORD = prove(
  `(!x:int128. word_subword (word_reversefields 8 x) (0,64):64 word =
               word_reversefields 8 (word_subword x (64,64):64 word)) /\
   (!x:int128. word_subword (word_reversefields 8 x) (64,64):64 word =
               word_reversefields 8 (word_subword x (0,64):64 word))`,
  CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Subword lane extraction through word_zx / word_shl of the 256-bit         *)
(* Karatsuba assembly (for a 64-bit source).                                 *)
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

(* Collapse a 64-bit lane of subword (subword (join a a) (64,128)) to a      *)
(* plain lane of a (this is the duplicated mid-half that the wv operand of   *)
(* the W-reduction produces).                                                *)
let SUBSUB_JOIN_DUP = prove(
  `(!a:128 word. word_subword (word_subword (word_join a a :256 word) (64,128) :128 word) (0,64) :64 word
                 = word_subword a (64,64)) /\
   (!a:128 word. word_subword (word_subword (word_join a a :256 word) (64,128) :128 word) (64,64) :64 word
                 = word_subword a (0,64))`,
  CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Abbreviate every `word_subword (a:int128) (lo,64)` subterm in the goal to *)
(* a fresh 64-bit variable, so the residual is a flat word_xor identity over *)
(* 64-bit variables that WORD_BITWISE_TAC closes.                            *)
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

(* Fast closer for the operand-equality subgoal of a merge: flatten the      *)
(* 256-bit Karatsuba lanes to 64-bit lanes, abbreviate them, and close by    *)
(* WORD_BITWISE_TAC instead of a WORD_BLAST of the whole terms.              *)
let FAST_OPERAND_TAC : tactic =
  REWRITE_TAC[SUBW_XOR_256; SUBW_ZX_256; SUBW_SHL64_256; SUBW_SHL128_256;
              SUBW_ZX128_256; SUBW_SHL64_128_256; SUBW_SHL128_128_256] THEN
  REWRITE_TAC[WORD_XOR_0; SUBSUB_JOIN_DUP; WORD_SUBWORD_SUBWORD;
              JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  ABBREV_ALL_SUBWORDS_TAC THEN
  WORD_BITWISE_TAC;;

(* Targeted pmul-atom merge for the 2-block bridge: one structurally         *)
(* determined pair per call; FAST_OPERAND_TAC closes the operand equalities. *)
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

(* ========================================================================= *)
(* GMULT2 fast-reduce bridge.  GMULT2_FULL_CORRECT_BA is the 2-block fused   *)
(* multiply+reduce: the assembly's byteform that XOR-accumulates two         *)
(* Karatsuba triples and then runs the shared W-reduction equals             *)
(*   polyval_reduce_prop3 (word_pmul a0 b0 XOR word_pmul a1 b1).             *)
(* It is built from PMUL_KARATSUBA and GMULT_REDUCE_PROP3 (the W-reduction   *)
(* is proved once), so the reduction is never re-blasted.  MERGE_2BLK_TAC    *)
(* reconciles the per-block operand transpose (rev64 and h on one side, brev *)
(* and byteswap128 on the other).                                            *)
(* ========================================================================= *)

(* GMULT2_FULL_CORRECT_BA: the 2-block fused multiply+reduce byteform =      *)
(* polyval_reduce_prop3 (word_pmul a0 b0 XOR word_pmul a1 b1), built by the  *)
(* GMULTn builder above.                                                     *)
let _, GMULT2_FULL_CORRECT_BA = build_GMULTn_fast 2;;

(* ========================================================================= *)
(* AES-GCM decryption: the whole-block output and GHASH specification.       *)
(*                                                                           *)
(* The kernel processes whole 16-byte blocks only, so these specifications   *)
(* read the input byte buffer `x` as its len DIV 16 whole blocks, and the    *)
(* proof uses them only at len = 16 * N, N >= 1.  Each band's readable       *)
(* wrapper states its postcondition as                                       *)
(*   gcm_dec_pt_bytes (16 * N) x ctr0 keys      (the output) and             *)
(*   gcm_dec_final_xi (16 * N) x xi h           (the tag),                   *)
(* with the block decomposition hidden.  The per-N unfold lemmas             *)
(* GCM_DEC_GHASH_BLOCKS_WHOLE_N and GCM_DEC_PT_BYTES_WHOLE_N (N = 1..8)      *)
(* rewrite these back to the explicit N-block list a band's body produces,   *)
(* so the wrappers need no simulation.                                       *)
(*                                                                           *)
(* Decryption differs from encryption only in what GHASH reads: output block *)
(* k is word_xor ciphertext_k keystream_k (aes_ctr above), while GHASH runs  *)
(* over the raw ciphertext blocks `bytes_to_int128 (SUB_LIST (16*k,16) x)`,  *)
(* not over the plaintext.                                                   *)
(*                                                                           *)
(* The vocabulary is that of the band theorems: the base counter `ctr0` (the *)
(* ivec), the lane-order AES (aes256_encrypt or aes128_encrypt) with         *)
(* `gcm_ctr_inc_iter`, the GHASH key `byteswap128 h`, and `word_bytereverse` *)
(* per block (which is the same as word_reversefields 8 at :128).            *)
(* ========================================================================= *)


(* ----------------------------------------------------------------------------
   The int128 block-list view of a byte buffer: `m` consecutive 16-byte blocks
   starting at block index `i` (byte offset 16*i), each read as a big int128.
   ------------------------------------------------------------------------- *)
let gcm_dec_blocks_from = define
 `gcm_dec_blocks_from (i:num) 0 (x:byte list) : int128 list = [] /\
  gcm_dec_blocks_from (i:num) (SUC m) (x:byte list) =
    CONS (bytes_to_int128 (SUB_LIST (16 * i, 16) x))
         (gcm_dec_blocks_from (i + 1) m x)`;;

let LENGTH_GCM_DEC_BLOCKS_FROM = prove
 (`!m i x. LENGTH (gcm_dec_blocks_from i m x) = m`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[gcm_dec_blocks_from; LENGTH]);;

(* Head-step: peel the first block. *)
let GCM_DEC_BLOCKS_FROM_STEP = prove
 (`!m i x. gcm_dec_blocks_from i (SUC m) x =
           CONS (bytes_to_int128 (SUB_LIST (16 * i, 16) x))
                (gcm_dec_blocks_from (i + 1) m x)`,
  REWRITE_TAC[gcm_dec_blocks_from]);;

(* ----------------------------------------------------------------------------
   GHASH input block list (decrypt): the len DIV 16 whole blocks of the raw
   ciphertext input (encrypt GHASHes its output instead, the one genuine
   dec/enc difference).
   ------------------------------------------------------------------------- *)
let gcm_dec_ghash_blocks = new_definition
 `gcm_dec_ghash_blocks (len:num) (x:byte list) : int128 list =
    gcm_dec_blocks_from 0 (len DIV 16) x`;;

(* The final GHASH accumulator Xi written to tag_p: byte-reverse in, run
   ghash_polyval_acc over the byte-reversed block list keyed by byteswap128 h,
   byte-reverse out.  This is the tag_p postcondition of the band bodies. *)
let gcm_dec_final_xi = new_definition
 `gcm_dec_final_xi (len:num) (x:byte list) (xi:int128) (h:int128) : int128 =
    word_bytereverse
      (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
         (MAP word_bytereverse (gcm_dec_ghash_blocks len x)))`;;

(* ----------------------------------------------------------------------------
   Per-N unfold lemmas at len = 16*N, N = 1..8 (one per readable band
   theorem): the whole-buffer specs as the explicit N-block list
     [bytes_to_int128 (SUB_LIST (0,16) x); ...;
      bytes_to_int128 (SUB_LIST (16*(N-1),16) x)].
   ------------------------------------------------------------------------- *)
let gcm_dec_whole_blocks_tm n =
  mk_list(map (fun i -> subst [mk_small_numeral (16 * i),`ofs:num`]
                          `bytes_to_int128 (SUB_LIST (ofs,16) (x:byte list))`)
              (0--(n-1)), `:int128`);;

(* gcm_dec_blocks_from 0 ((16 * n) DIV 16) x -> the explicit n-block list. *)
let GCM_DEC_BLOCKS_FROM_UNFOLD_TAC n =
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC(map (num_CONV o mk_small_numeral) (rev (1--n))) THEN
  REWRITE_TAC[gcm_dec_blocks_from] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let build_ghash_blocks_whole n =
  prove(mk_forall(`x:byte list`,
          mk_eq(list_mk_comb(`gcm_dec_ghash_blocks`,
                             [mk_small_numeral (16 * n); `x:byte list`]),
                gcm_dec_whole_blocks_tm n)),
        GEN_TAC THEN REWRITE_TAC[gcm_dec_ghash_blocks] THEN
        GCM_DEC_BLOCKS_FROM_UNFOLD_TAC n);;

let GCM_DEC_GHASH_BLOCKS_WHOLE_1 = build_ghash_blocks_whole 1;;

let GCM_DEC_GHASH_BLOCKS_WHOLE_2 = build_ghash_blocks_whole 2;;

let GCM_DEC_GHASH_BLOCKS_WHOLE_3 = build_ghash_blocks_whole 3;;

let GCM_DEC_GHASH_BLOCKS_WHOLE_4 = build_ghash_blocks_whole 4;;

let GCM_DEC_GHASH_BLOCKS_WHOLE_5 = build_ghash_blocks_whole 5;;

let GCM_DEC_GHASH_BLOCKS_WHOLE_6 = build_ghash_blocks_whole 6;;

let GCM_DEC_GHASH_BLOCKS_WHOLE_7 = build_ghash_blocks_whole 7;;

let GCM_DEC_GHASH_BLOCKS_WHOLE_8 = build_ghash_blocks_whole 8;;

(* The 12-slot aws-lc key table as one predicate over the GHASH input key h
   (the slot values are the byteswapped polyval_dot powers and the packed
   Karatsuba mids).  Expand it (REWRITE_TAC[htable_mem_dec] + let_CONV) before
   stepping, so that the table loads resolve. *)
let htable_mem_dec = new_definition
 `htable_mem_dec (h:int128) (ptr:int64) (s:armstate) <=>
    let hb = byteswap128 h in
    let h2 = byteswap128 (polyval_dot hb hb) in
    let h3 = byteswap128 (polyval_dot (polyval_dot hb hb) hb) in
    let h4 = byteswap128 (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) in
    let h5 = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) in
    let h6 = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) in
    let h7 = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) hb) in
    let h8 = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) hb) hb) in
    read (memory :> bytes128 ptr) s = h /\
    read (memory :> bytes128 (word_add ptr (word 16))) s =
      word_join (karatsuba_mid h2) (karatsuba_mid h) /\
    read (memory :> bytes128 (word_add ptr (word 32))) s = h2 /\
    read (memory :> bytes128 (word_add ptr (word 48))) s = h3 /\
    read (memory :> bytes128 (word_add ptr (word 64))) s =
      word_join (karatsuba_mid h4) (karatsuba_mid h3) /\
    read (memory :> bytes128 (word_add ptr (word 80))) s = h4 /\
    read (memory :> bytes128 (word_add ptr (word 96))) s = h5 /\
    read (memory :> bytes128 (word_add ptr (word 112))) s =
      word_join (karatsuba_mid h6) (karatsuba_mid h5) /\
    read (memory :> bytes128 (word_add ptr (word 128))) s = h6 /\
    read (memory :> bytes128 (word_add ptr (word 144))) s = h7 /\
    read (memory :> bytes128 (word_add ptr (word 160))) s =
      word_join (karatsuba_mid h8) (karatsuba_mid h7) /\
    read (memory :> bytes128 (word_add ptr (word 176))) s = h8`;;

(* ------------------------------------------------------------------------- *)
(* Shared band machinery: the KEEPGH stepper and the byte-reversed tag.      *)
(* ------------------------------------------------------------------------- *)

(* The tail's Karatsuba mids use ext vD.16b,vN.16b,vN.16b,#8 where AWS-LC's
   code uses ins vD.d[0],vN.d[1], and only lane 0 of the result is read (by
   an .8b eor or a .1d pmull).  The stepper models the ext as
   word_subword (word_join vN vN) (64,128), a rotation by 64 bits, and the
   per-step normalizer GCM_SIMD_SIMPLIFY_CORE_TAC folds its lane-0 projection
   back to the plain lane word_subword vN (64,64) (EXT8_LANE0_IS_SUBWORD_HI),
   so the tail bridges see the operand shapes of the ins form.
   AUTO_MERGE_MIDS_KM_TAC below pairs the mids of the N >= 3 bridges whatever
   their qq numbering. *)

(* The KEEPGH stepper: after each step, discard every fact about an older
   state except those that read the GHASH registers Q16-Q19. *)
let DISCARD_OLDSTATE_KEEPGH_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_ghreg t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> n="Q16"||n="Q17"||n="Q18"||n="Q19" | _ -> false)
    | Comb(a,b) -> mentions_ghreg a || mentions_ghreg b | Abs(_,t2) -> mentions_ghreg t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_ghreg (concl thm) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else if not(mem v us) then true else true);;

(* The per-step normalizer of the KEEPGH stepper, for the GHASH multiply and
   reduction windows of the band tails.  It is one pass of the rewrites of
   GCM_SIMD_SIMPLIFY_CORE_TAC rather than the double pass of
   GCM_SIMD_SIMPLIFY_TAC (the second pass only matters for the block-boundary
   REV64 folds, which the Q19 bridge redoes), applied only to the Q-register
   reads and memoized in gcm_simd_kgh_tbl (GCM_SIMD_SIMPLIFY_MEMO_TAC below).
   WB_PREP_TAC clears the table (CLEAR_KEEPGH_MEMO_TAC) at the start of each
   tail proof. *)
let gcm_simd_kgh_tbl : (term,unit) Hashtbl.t = Hashtbl.create 4096;;

let CLEAR_KEEPGH_MEMO_TAC : tactic =
  fun (asl,w) -> Hashtbl.clear gcm_simd_kgh_tbl; ALL_TAC (asl,w);;

(* The tag load ld1/ext/rev64 leaves Q19 as word_join (reversefields lo)
   (reversefields hi) of xi; this is word_bytereverse xi, the form in which
   the GHASH accumulator closes against the postcondition. *)
let Q19_BREVXI = prove
 (`word_join (word_reversefields 8 (word_subword (xi:int128) (0,64):int64))
             (word_reversefields 8 (word_subword xi (64,64):int64)):int128 =
   word_bytereverse xi`,
  CONV_TAC WORD_BLAST);;

(* ========================================================================= *)
(* Band lemmas for the 3..8-block whole-blocks tails (len_bits = 128*N).     *)
(* ========================================================================= *)

(* ---- shared N>=3 band machinery ---- *)

let collect_pmuls p t = let rec collect t acc = let acc = if p t then t::acc else acc in
  match t with Comb(a,b)->collect a (collect b acc)|Abs(_,b)->collect b acc|_->acc in setify(collect t []);;

let isWpmul t = try fst(dest_const(repeat rator t))="word_pmul" && rand t=`word 13979173243358019584:64 word` with _->false;;

let SJ_COLLAPSE = prove
 (`!w:128 word. word_subword (word_subword (word_join w w:256 word) (64,128):128 word) (0,64):64 word
                = word_subword w (64,64)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let SJ_COLLAPSE2 = prove
 (`!w:128 word. word_subword (word_subword (word_join w w:256 word) (64,128):128 word) (64,64):64 word
                = word_subword w (0,64)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let word_xor_left_comm = WORD_RULE `word_xor (a:64 word) (word_xor b c) = word_xor b (word_xor a c)`;;

let xor_pair_comm = WORD_RULE `word_xor (a:64 word) b = word_xor b a`;;

let term_leq t1 t2 = String.compare (string_of_term t1) (string_of_term t2) <= 0;;

let rec bubble_conv tm = match tm with
  | Comb(Comb(Const("word_xor",_), a), b) ->
    (match b with
     | Comb(Comb(Const("word_xor",_), b1), _) ->
       if term_leq a b1 then AP_TERM (mk_comb(rator(rator tm), a)) (bubble_conv b)
       else let th1 = PART_MATCH lhs word_xor_left_comm tm in
         let new_rhs = rhs(concl th1) in TRANS th1 (AP_TERM (rator new_rhs) (bubble_conv (rand new_rhs)))
     | _ -> if term_leq a b then REFL tm else PART_MATCH lhs xor_pair_comm tm)
  | _ -> REFL tm;;

let rec bubble_sort_conv tm =
  let rec count_xors t = match t with Comb(Comb(Const("word_xor",_), _), r) -> 1 + count_xors r | _ -> 0 in
  let n = count_xors tm in
  let rec apply_n_times k acc = if k <= 0 then acc else apply_n_times (k-1) (TRANS acc (bubble_conv (rhs(concl acc)))) in
  apply_n_times n (REFL tm);;

let rec bubble_fix tm = let th = bubble_sort_conv tm in let r = rhs(concl th) in
  if r = tm then th else TRANS th (bubble_fix r);;

let LANE_FINISH_TAC : tactic =
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[SJ_COLLAPSE; SJ_COLLAPSE2] THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;

let WA_UNIFY_TAC : tactic = fun (asl,w) ->
  let l=lhs w and r=rhs w in
  let iswa t = isWpmul t && not(can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwa=hd(collect_pmuls iswa l) and rwa=hd(collect_pmuls iswa r) in
  if lwa=rwa then ALL_TAC (asl,w) else
  let wa_eq = prove(mk_eq(rwa,lwa), MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_RULE) in
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [wa_eq] (asl,w);;

let WV_UNIFY_TAC : tactic = fun (asl,w) ->
  let l=lhs w and r=rhs w in
  let iswv t = isWpmul t && (can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwv=hd(collect_pmuls iswv l) and rwv=hd(collect_pmuls iswv r) in
  if lwv=rwv then ALL_TAC (asl,w) else
  let in_eq = BITBLAST_RULE (mk_eq(rand(rator rwv), rand(rator lwv))) in
  let wv_eq = AP_THM (AP_TERM `word_pmul:64 word->64 word->128 word` in_eq) `word 13979173243358019584:64 word` in
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [wv_eq] (asl,w);;

let ABBREV_WAWV_TAC : tactic = fun (asl,w) ->
  let l=lhs w in
  let iswa t = isWpmul t && not(can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwa=hd(collect_pmuls iswa l) in
  (ABBREV_TAC (mk_eq(`WAz:128 word`, lwa)) THEN
   (fun (asl,w) -> let l=lhs w in
     (match collect_pmuls isWpmul l with wv::_ -> ABBREV_TAC (mk_eq(`WVz:128 word`, wv)) | [] -> ALL_TAC) (asl,w)))
  (asl,w);;

let pmul_mult_hpow t =
  let m = rand t in
  if can(find_term(fun u->u=`h2:int128`)) m then "H2" else
  if can(find_term(fun u->u=`h3:int128`)) m then "H3" else
  if can(find_term(fun u->u=`h4:int128`)) m then "H4" else
  if can(find_term(fun u->u=`h5:int128`)) m then "H5" else
  if can(find_term(fun u->u=`h6:int128`)) m then "H6" else
  if can(find_term(fun u->u=`h7:int128`)) m then "H7" else
  if can(find_term(fun u->u=`h8:int128`)) m then "H8" else
  if can(find_term(fun u->u=`h:int128`)) m then "H1" else
  if can(find_term(fun u->u=`word 13979173243358019584:64 word`)) m then "W" else "?";;

let WB_MID_FIX = [WORD_SUBWORD_INSERT_INNER; WORD_SUBWORD_INSERT_OUTER; INSERT_SUBWORD_KILL;
                  WORD_INSERT_SUBWORD; JOINMID; JOIN_SUBWORD_RULES; RF8_SUBWORD;
                  WORD_SUBWORD_SUBWORD; WORD_SUBWORD_XOR];;

let POLYVAL_DOT_SYM = prove
 (`!a b:int128. polyval_dot a b = polyval_dot b a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polyval_dot] THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_PMUL_SYM]);;

let GCM_CTR_INC2_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc ctr0)`,
        subst [`word 2:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

let _, GMULT3_FULL_CORRECT_BA = build_GMULTn_fast 3;;

let spec_to_byteform_wb3 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h3))
          (word_pmul (word_bytereverse cph1) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph2) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`] GHASH_POLYVAL_ACC_3)] THEN
  SUBGOAL_THEN `polyval_dot (byteswap128 h) (polyval_dot (byteswap128 h) (byteswap128 h)) = byteswap128 h3`
    (fun th -> REWRITE_TAC[th]) THENL
  [ONCE_REWRITE_TAC[POLYVAL_DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* Shared merge machinery (MERGE_ANY_TAC, MERGE_QQPAIR_KM_TAC).  MERGE_2BLK_TAC
   pairs the qq atoms by taking the first candidate with a compatible
   signature; at N = 8 that greedy choice pairs machine-lo with spec-hi atoms
   and leaves atoms that cannot be merged.  MERGE_ONE_ANY_TAC uses the same
   pairing signature but tries every candidate pair (by FIRST, backtracking
   when the WORD_BLAST operand close fails), so a bad pick does not stick. *)

let MERGE_ONE_ANY_TAC : tactic = fun (asl,w) ->
  let is_pmul t = try let (hd,a)=strip_comb t in fst(dest_const hd)="word_pmul" && List.length a=2 with _->false in
  let is_wordconst t = try is_comb t && fst(dest_const(rator t))="word" && is_numeral(rand t) with _->false in
  let is_keyvar n = String.length n>=2 && n.[0]='k' &&
                    (try let _ = int_of_string (String.sub n 1 (String.length n-1)) in true with _->false) in
  let goalvars = setify(map (fun t->fst(dest_var t))
    (find_terms (fun t->is_var t && type_of t=`:int128` &&
      (let n=fst(dest_var t) in String.length n>=2 && String.sub n 0 2="qq")) w)) in
  let defs = List.filter (fun (_,th)->let c=concl th in is_eq c && is_var(rhs c) &&
    is_pmul(lhs c) && mem (fst(dest_var(rhs c))) goalvars) asl in
  let fvnames t = sort (<) (List.filter (fun n -> not(is_keyvar n))
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
  let rec allpairs_acc = function
    | [] -> []
    | (v,op2,sg)::rest ->
        let cands =
          if is_wordconst op2
          then List.filter (fun (v2,op2b,_)-> v2<>v && is_wordconst op2b && op2b=op2) rest
          else List.filter (fun (v2,op2b,sg2)-> v2<>v && not(is_wordconst op2b) && sg2=sg) rest in
        (map (fun (v2,_,_) -> (v,v2)) cands) @ allpairs_acc rest in
  let pairs = allpairs_acc items in
  if pairs = [] then failwith "MERGE_ONE_ANY_TAC: nothing to merge" else
  let close_op = FAST_OPERAND_TAC ORELSE CONV_TAC WORD_BLAST in
  let cand_tac (v1,v2) =
    SUBGOAL_THEN (mk_eq(v1,v2))
      (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]))
     THENL [EXPAND_TAC(fst(dest_var v1)) THEN EXPAND_TAC(fst(dest_var v2)) THEN
            ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN close_op)
             ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
                     MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN close_op));
            ALL_TAC] in
  FIRST (map cand_tac pairs) (asl,w);;

let MERGE_ANY_TAC : tactic = REPEAT MERGE_ONE_ANY_TAC;;

(* Stepping machinery for the tails of bands 3..8.  Keeping all of Q16-Q19
   across the long stores window (ARM_STEPS_FOLD_KEEPGH_TAC) makes the per-step
   GCM_SIMD_SIMPLIFY pass rescan a growing set of assumptions, quadratic
   overall.  Instead the window is stepped keeping only the latest read Q18
   fact (the carried GHASH mid; the store readbacks carry themselves forward),
   which is then named midacc, and the bridge expands it once. *)
let DISCARD_OLDSTATE_KEEPQ18_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_q18 t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> n="Q18" | _ -> false)
    | Comb(a,b) -> mentions_q18 a || mentions_q18 b | Abs(_,t2) -> mentions_q18 t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_q18 (concl thm) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else true);;

let state_num_of_q18_fact th =
  try let c = concl th in
      if not(is_eq c) then None else
      match lhs c with
        Comb(Comb(Const("read",_),Const("Q18",_)),Var(sn,_)) when String.length sn > 1 && sn.[0]='s' ->
          Some(int_of_string(String.sub sn 1 (String.length sn - 1)))
      | _ -> None
  with _ -> None;;

let DISCARD_STALE_Q18_TAC : tactic = fun (asl,w) ->
  let nums = List.filter_map (fun (_,th) -> state_num_of_q18_fact th) asl in
  match nums with
  | [] | [_] -> ALL_TAC (asl,w)
  | _ -> let mx = List.fold_left max 0 nums in
         DISCARD_ASSUMPTIONS_TAC (fun th ->
           match state_num_of_q18_fact th with
           | Some k -> k < mx
           | None -> false) (asl,w);;

(* The per-step normalizer here is the single pass GCM_SIMD_SIMPLIFY_CORE_TAC,
   not the double pass GCM_SIMD_SIMPLIFY_TAC: the second pass is a full
   traversal of the carried GHASH terms and only folds the fresh REV64 byte
   trees at the block boundaries, which the Q19 bridge redoes downstream
   (WORD_BYTEREVERSE_REVERSEFIELDS, RF8_SUBWORD). *)
let ARM_STEPS_FOLD_Q18LATEST_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_CORE_TAC THEN
              DISCARD_STALE_Q18_TAC THEN DISCARD_OLDSTATE_KEEPQ18_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;

(* The merge of two given qq atoms, with karatsuba_mid unfolded inside the
   closing WORD_BLAST: the midacc expansion exposes machine mids whose spec
   partners are still folded in karatsuba_mid. *)
let MERGE_QQPAIR_KM_TAC (n1:string) (n2:string) : tactic =
  SUBGOAL_THEN (mk_eq(mk_var(n1,`:128 word`), mk_var(n2,`:128 word`)))
    (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [EXPAND_TAC n1 THEN EXPAND_TAC n2 THEN REWRITE_TAC[karatsuba_mid] THEN
   ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
     (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC WB_MID_FIX THEN CONV_TAC WORD_BLAST)))
    ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
            MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
            (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC WB_MID_FIX THEN CONV_TAC WORD_BLAST))));
   ALL_TAC];;

(* WA_UNIFY_TAC with BITBLAST_RULE in place of WORD_RULE, which overflows the
   stack on the larger wa inputs of the midacc bridges. *)
let WA_UNIFY_BB_TAC : tactic = fun (asl,w) ->
  let l=lhs w and r=rhs w in
  let iswa t = isWpmul t && not(can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwa=hd(collect_pmuls iswa l) and rwa=hd(collect_pmuls iswa r) in
  if lwa=rwa then ALL_TAC (asl,w) else
  let in_eq = BITBLAST_RULE (mk_eq(rand(rator rwa), rand(rator lwa))) in
  let mult_eq = BITBLAST_RULE (mk_eq(rand rwa, rand lwa)) in
  let wa_eq = MATCH_MP (ISPECL [rand(rator rwa); rand rwa; rand(rator lwa); rand lwa] PMUL_CONG_128)
                (CONJ in_eq mult_eq) in
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [wa_eq] (asl,w);;

(* Name-agnostic pairing of the leftover Karatsuba-mid qq atoms.  The per-step
   normalizer (GCM_SIMD_SIMPLIFY_CORE_TAC with EXT8_LANE0_IS_SUBWORD_HI) folds
   the ext-form Karatsuba-mid lanes to the plain lanes, but the qq numbers
   ABBREV_INNER_PMULS_TAC assigns are not stable across bands.  So this pairs
   the leftover mid pmuls by H-power, which depends only on the key operand h2,
   h3, ... and not on the data-side ext form: after MERGE_ANY_TAC has merged
   everything it can, the only residual mismatch is a set of Karatsuba-mid qq
   atoms that occur only on the left-hand side against others that occur only
   on the right-hand side, and each left one merges with the right one of the
   same H-power (MERGE_QQPAIR_KM_TAC, which closes by WORD_BLAST and so does
   not depend on the form). *)
let AUTO_MERGE_MIDS_KM_TAC : tactic = fun (asl,w) ->
  let rec xleaves t = match t with
    | Comb(Comb(Const("word_xor",_),a),b) -> xleaves a @ xleaves b | _ -> [t] in
  let qqs_in t = setify(map (fun v->fst(dest_var v))
     (List.filter (fun v-> let n=fst(dest_var v) in String.length n>=2 && String.sub n 0 2="qq")
        (frees t))) in
  let hpow n = try let (_,th)=List.find(fun(_,th)->let c=concl th in
       is_eq c && is_var(rhs c) && fst(dest_var(rhs c))=n) asl in pmul_mult_hpow(lhs(concl th))
     with _->"?" in
  let ll = xleaves(lhs w) and rl = xleaves(rhs w) in
  let dl = subtract (setify ll) (setify rl) and dr = subtract (setify rl) (setify ll) in
  let lqq = subtract (setify(List.concat_map qqs_in dl)) (setify(List.concat_map qqs_in dr)) in
  let rqq = subtract (setify(List.concat_map qqs_in dr)) (setify(List.concat_map qqs_in dl)) in
  let used = ref [] in
  let pairs = List.filter_map (fun ln ->
     let hp = hpow ln in
     try let rn = List.find (fun rn -> not(mem rn !used) && hpow rn = hp) rqq in
         used := rn :: !used; Some(ln,rn)
     with _ -> None) lqq in
  (EVERY (map (fun (a,b) -> MERGE_QQPAIR_KM_TAC a b) pairs)) (asl,w);;

(* The midacc bridges can leave a stray zero limb in each 64-bit lane (the
   carried mid enters the reduction as word 0 XOR ...): LANE_FINISH_Z_TAC
   collapses it before the bubble sort, then finishes as LANE_FINISH_TAC. *)
let ZSUB0 = prove(`word_subword (word 0:int128) (0,64):64 word = word 0`, CONV_TAC WORD_BLAST);;

let ZSUB0b = prove(`word_subword (word 0:int128) (64,64):64 word = word 0`, CONV_TAC WORD_BLAST);;

let LANE_FINISH_Z_TAC : tactic =
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[SJ_COLLAPSE; SJ_COLLAPSE2] THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[ZSUB0; ZSUB0b; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;

let GCM_CTR_INC3_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))`,
        subst [`word 3:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

let _, GMULT4_FULL_CORRECT_BA = build_GMULTn_fast 4;;

let spec_to_byteform_wb4 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h4))
           (word_pmul (word_bytereverse cph1) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph2) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph3) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`] GHASH_POLYVAL_ACC_4)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let GCM_CTR_INC4_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))`,
        subst [`word 4:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

let _, GMULT5_FULL_CORRECT_BA = build_GMULTn_fast 5;;

let spec_to_byteform_wb5 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
         word_bytereverse cph3; word_bytereverse cph4] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h5))
            (word_pmul (word_bytereverse cph1) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph2) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph3) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph4) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`] GHASH_POLYVAL_ACC_5)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ========================================================================= *)
(* The 6-block band: GHASH_POLYVAL_ACC_6, GMULT6_FULL_CORRECT_BA and         *)
(* spec_to_byteform_wb6.  GHASH_POLYVAL_ACC_6 is proved from                 *)
(* GHASH_POLYVAL_ACC_BATCHED like the 4- and 5-block forms in the N-block    *)
(* GHASH Karatsuba layer above.                                              *)
(* ========================================================================= *)
let GHASH_POLYVAL_ACC_6 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128) (u:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t; u] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul t (polyval_dot h h) : 256 word)
        (word_pmul u h : 256 word))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t; u]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;

let GCM_CTR_INC5_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))`,
        subst [`word 5:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

let _, GMULT6_FULL_CORRECT_BA = build_GMULTn_fast 6;;

let spec_to_byteform_wb6 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
         word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_xor
             (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h6))
             (word_pmul (word_bytereverse cph1) (byteswap128 h5)))
            (word_pmul (word_bytereverse cph2) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph3) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph4) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph5) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`; `word_bytereverse cph5:int128`] GHASH_POLYVAL_ACC_6)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ========================================================================= *)
(* The 7-block band: GHASH_POLYVAL_ACC_7 (proved like GHASH_POLYVAL_ACC_6),  *)
(* GMULT7_FULL_CORRECT_BA and spec_to_byteform_wb7.                          *)
(* ========================================================================= *)
let GHASH_POLYVAL_ACC_7 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128) (u:int128) (v:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t; u; v] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul t (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul u (polyval_dot h h) : 256 word)
        (word_pmul v h : 256 word)))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t; u; v]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;

let GCM_CTR_INC6_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))))`,
        subst [`word 6:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

let _, GMULT7_FULL_CORRECT_BA = build_GMULTn_fast 7;;

let spec_to_byteform_wb7 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
         word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
         word_bytereverse cph6] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_xor
             (word_xor
              (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h7))
              (word_pmul (word_bytereverse cph1) (byteswap128 h6)))
             (word_pmul (word_bytereverse cph2) (byteswap128 h5)))
            (word_pmul (word_bytereverse cph3) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph4) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph5) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph6) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`; `word_bytereverse cph5:int128`;
            `word_bytereverse cph6:int128`] GHASH_POLYVAL_ACC_7)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ========================================================================= *)
(* The 8-block band: GHASH_POLYVAL_ACC_8 (proved like GHASH_POLYVAL_ACC_6),  *)
(* GMULT8_FULL_CORRECT_BA and spec_to_byteform_wb8.                          *)
(* ========================================================================= *)
let GHASH_POLYVAL_ACC_8 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128) (u:int128) (v:int128) (w:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t; u; v; w] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul t (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul u (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul v (polyval_dot h h) : 256 word)
        (word_pmul w h : 256 word))))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t; u; v; w]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `7`; num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;

let GCM_CTR_INC7_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))))`,
        subst [`word 7:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

let _, GMULT8_FULL_CORRECT_BA = build_GMULTn_fast 8;;

let spec_to_byteform_wb8 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h8 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
         word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
         word_bytereverse cph6; word_bytereverse cph7] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_xor
             (word_xor
              (word_xor
               (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h8))
               (word_pmul (word_bytereverse cph1) (byteswap128 h7)))
              (word_pmul (word_bytereverse cph2) (byteswap128 h6)))
             (word_pmul (word_bytereverse cph3) (byteswap128 h5)))
            (word_pmul (word_bytereverse cph4) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph5) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph6) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph7) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`; `word_bytereverse cph5:int128`;
            `word_bytereverse cph6:int128`; `word_bytereverse cph7:int128`] GHASH_POLYVAL_ACC_8)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* The shared front WB_FRONT_BUF of bands 5..8: its statement and the term   *)
(* builders of the simulated postconditions.                                 *)
(* ------------------------------------------------------------------------- *)

(* ---- the and-mask on the 5..8 front: 16 * nblk - 1 rounded down to a
   multiple of 128 is 0 for 1 <= nblk <= 8 (AND_MASK_16NBLK_ANY states it for
   any nblk). ---- *)
let AND_MASK_16NBLK = prove
 (`!nblk. 1 <= nblk /\ nblk <= 8
        ==> word_and (word_sub (word (16 * nblk)) (word 1))
                     (word 18446744073709551488):int64 = word 0`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= n /\ n <= 8 <=>
    n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV);;

let wb_front_frame_tm = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblk); memory :> bytes(tag_p:int64, 16);
                 memory :> bytes(ivec_p:int64, 16); memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31]`;;

(* gcm_ctr_inc^k ctr0 for k = 1..7, as the lanes the counter setup of the
   front computes (GCM_CTR_INC_LANES to GCM_CTR_INC7_LANES). *)
let wb_ctr_lanes_thms =
  [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES;
   GCM_CTR_INC5_LANES; GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES];;

(* The raw counter accumulator kept in v30, machine-level vocabulary like
   gcm_ctr_inc (no exported statement mentions it): the counter block
   byte-grouped as rev32 reads it, with w added to its top 32-bit lane.
   rev32 of it is gcm_ctr_add w ctr0, the AES input block for counter w, and
   add v30.4s,v30.4s,v31.4s (v31 = word 2^96) takes gcm_ctr_raw w ctr0 to
   gcm_ctr_raw (word_add w (word 1)) ctr0.  It is defined here because
   wb_front_postcond below states Q30 with it; its lane lemmas (SUBW_RAW_*,
   GCM_CTR_RAW_INCR) come with the counter algebra below and its fold tactics
   (REV32_FOLD_TAC, CTR_RAW_INCR_FOLD_TAC) with the main-loop proof. *)
let gcm_ctr_raw_def = new_definition
 `gcm_ctr_raw (w:32 word) (ctr0:int128) : int128 =
   word_join
    (word_join
      (word_add
        (word_join
          (word_join (word_subword ctr0 (96,8):8 word) (word_subword ctr0 (104,8):8 word):16 word)
          (word_join (word_subword ctr0 (112,8):8 word) (word_subword ctr0 (120,8):8 word):16 word):32 word)
        w)
      (word_join (word_join (word_subword ctr0 (64,8):8 word) (word_subword ctr0 (72,8):8 word):16 word)
        (word_join (word_subword ctr0 (80,8):8 word) (word_subword ctr0 (88,8):8 word):16 word):32 word):64 word)
    (word_join
      (word_join (word_join (word_subword ctr0 (32,8):8 word) (word_subword ctr0 (40,8):8 word):16 word)
        (word_join (word_subword ctr0 (48,8):8 word) (word_subword ctr0 (56,8):8 word):16 word):32 word)
      (word_join (word_join (word_subword ctr0 (0,8):8 word) (word_subword ctr0 (8,8):8 word):16 word)
        (word_join (word_subword ctr0 (16,8):8 word) (word_subword ctr0 (24,8):8 word):16 word):32 word):64 word):int128`;;

(* ---- term builders for the simulated postconditions ----------------------
   wb_front_postcond (below), wbn_front_prebranch_postcond,
   wbn_front_prefix_postcond, wbn_front_postcond_i0 and
   wbn_prepretail_post_raw each describe the final state of a simulation (of
   the front, the shared prefix or the prepretail): the aligned_bytes_loaded
   fact and every `read _ sN = _` assumption (folded by wb_front_fold_tac),
   with sN abstracted to s, in the order the simulator leaves them.  They are
   built from the term families below. *)

(* h-power towers: dot j = polyval_dot^(j-1) over byteswap128 h *)
let rec hdot j = if j = 1 then `byteswap128 h`
  else mk_comb(mk_comb(`polyval_dot:int128->int128->int128`, hdot (j-1)), `byteswap128 h`);;

(* counter i: gcm_ctr_inc^i ctr0 *)
let mk_ctr i =
  let rec go n = if n = 0 then `ctr0:int128`
    else mk_comb(`gcm_ctr_inc`, go (n-1)) in go i;;

(* input block i as the 128-bit lane the kernel loads *)
let mk_cph i = subst [mk_small_numeral(16*i),`nnn:num`]
  `bytes_to_int128 (SUB_LIST (nnn,16) (ibytes:byte list))`;;

(* the conjunct `read c s = v`, and the postcondition \s. c1 /\ ... /\ cn *)
let wbp_rd c v = mk_eq(list_mk_icomb "read" [c; `s:armstate`], v);;

let wbp_post cs = mk_abs(`s:armstate`, list_mk_conj cs);;

(* htable_mem_dec slot values: H^j (h itself for j = 1), and the packed
   karatsuba mids of H^(j+1) and H^j *)
let wbp_hpow j = if j = 1 then `h:int128` else mk_comb(`byteswap128`, hdot j);;

let wbp_hmid j = mk_comb(mk_comb(`word_join:int64->int64->int128`,
  mk_comb(`karatsuba_mid`, wbp_hpow (j+1))), mk_comb(`karatsuba_mid`, wbp_hpow j));;

(* read (memory :> bytes128 (base + 16 * i)) s *)
let wbp_mem128 base i =
  let addr = if i = 0 then base
    else subst [base,`bbb:int64`; mk_small_numeral(16*i),`nnn:num`] `word_add bbb (word nnn):int64` in
  subst [addr,`aaa:int64`] `read (memory :> bytes128 (aaa:int64)) s:int128`;;

let wbp_htable_reads =
  conjuncts(rhs(concl((REWRITE_CONV[htable_mem_dec] THENC TOP_DEPTH_CONV let_CONV)
    `htable_mem_dec h htable_p s`)));;

(* NZCV after cmp a, #n and after cmp a, b *)
let wbp_cmpi_flags a n = map (subst [a,`aaa:int64`; mk_small_numeral n,`nnn:num`])
  [`read NF s <=> ival (word_sub aaa (word nnn):int64) < &0`;
   `read ZF s <=> val (word_sub aaa (word nnn):int64) = 0`;
   `read CF s <=> nnn <= val (aaa:int64)`;
   `read VF s <=> ~(ival (aaa:int64) - &nnn = ival (word_sub aaa (word nnn):int64))`];;

let wbp_cmp_flags a b = map (subst [a,`aaa:int64`; b,`bbb:int64`])
  [`read NF s <=> ival (word_sub aaa bbb:int64) < &0`;
   `read ZF s <=> val (word_sub aaa bbb:int64) = 0`;
   `read CF s <=> val (bbb:int64) <= val (aaa:int64)`;
   `read VF s <=> ~(ival (aaa:int64) - ival (bbb:int64) = ival (word_sub aaa bbb:int64))`];;

(* the raw counter words: wbp_bytes4 x [a;b;c;d] joins the bytes of x at bit
   offsets a, b, c, d; wbp_lane b is the 32-bit lane of ctr0 at bit b, grouped
   as gcm_ctr_raw groups it, and wbp_revlane b the same bytes reversed *)
let wbp_bytes4 x offs =
  let byte k = mk_comb(mk_icomb(`word_subword:A word->num#num->8 word`, x),
                       mk_pair(mk_small_numeral k, `8`)) in
  let j16 a b = mk_comb(mk_comb(`word_join:8 word->8 word->16 word`, a), b)
  and j32 a b = mk_comb(mk_comb(`word_join:16 word->16 word->32 word`, a), b) in
  match map byte offs with
    [a;b;c;d] -> j32 (j16 a b) (j16 c d)
  | _ -> failwith "wbp_bytes4";;

let wbp_lane b = wbp_bytes4 `ctr0:int128` [b; b+8; b+16; b+24];;

let wbp_revlane b = wbp_bytes4 `ctr0:int128` [b+24; b+16; b+8; b];;

let wbp_add32 x n = mk_comb(mk_comb(`word_add:32 word->32 word->32 word`, x),
                            mk_comb(`word:num->32 word`, mk_small_numeral n));;

let wbp_join128 a b c d =
  let j64 x y = mk_comb(mk_comb(`word_join:32 word->32 word->64 word`, x), y) in
  mk_comb(mk_comb(`word_join:64 word->64 word->128 word`, j64 a b), j64 c d);;

(* v30 after the front's adds: top lane + w, then + 1, the other lanes + 0 *)
let wbp_raw_acc w =
  wbp_join128 (wbp_add32 (wbp_add32 (wbp_lane 96) w) 1) (wbp_add32 (wbp_lane 64) 0)
              (wbp_add32 (wbp_lane 32) 0) (wbp_add32 (wbp_lane 0) 0);;

(* rev32 of the raw counter with top lane + w: the AES input for counter w *)
let wbp_rev_ctr w =
  wbp_join128 (wbp_bytes4 (wbp_add32 (wbp_lane 96) w) [0; 8; 16; 24])
              (wbp_revlane 64) (wbp_revlane 32) (wbp_revlane 0);;

(* ========================================================================= *)
(* The shared front prefix: the entry pc+0x1c to the 0x448 b.ge (pc+1096),   *)
(* steps 1..267, proved once (WBN_FRONT_PREBRANCH) for the front of bands    *)
(* 5..8 (WB_FRONT_BUF) and the front of the >=9 bands (WBN_FRONT_PREFIX).    *)
(*                                                                           *)
(* It loads ivec, the tag and the 15 round keys, computes the 8 counter      *)
(* blocks and runs the 8 keystream towers up to the final aese (aes13); it   *)
(* reads no input block and no key-table entry, and its one data-dependent   *)
(* branch, the dispatch b.le at step 8, falls through for nblk >= 5.  So it  *)
(* is proved on the union band 5 <= nblk /\ 128 * nblk < 2 EXP 64, with X5   *)
(* kept general by the _ANY mask lemmas and the raw NF/VF/ZF/CF facts of the *)
(* cmp x0,x5 kept.  Each consumer then chains a short leg by                 *)
(* ENSURES_TRANS_SIMPLE: WB_FRONT_BUF takes the 0x448 b.ge in the 5..8 band  *)
(* and runs steps 268..273 to the seam s273; WBN_FRONT_PREFIX falls through  *)
(* in the >=9 band and runs steps 268..295 to s295.                          *)
(*                                                                           *)
(* The helpers below (state_num_of_read_q30, DISCARD_STALE_Q30_TAC and the   *)
(* _ANY mask lemmas) also serve the nblk >= 9 fronts, including the 9..16    *)
(* leg (WBN_FRONT_TO_PREP_916).                                              *)
(* ========================================================================= *)

(* keep only the latest read Q30 fact *)
let state_num_of_read_q30 th =
  let c = concl th in
  try (match lhs c with
       | Comb(Comb(Const("read",_),q),st) when string_of_term q = "Q30" ->
           let s = fst(dest_var st) in
           if String.length s > 1 && s.[0] = 's'
           then int_of_string (String.sub s 1 (String.length s - 1)) else (-1)
       | _ -> (-1))
  with _ -> (-1);;

let DISCARD_STALE_Q30_TAC : tactic = fun (asl,w) ->
  let nums = List.filter (fun n -> n >= 0)
    (List.map (fun (_,th) -> state_num_of_read_q30 th) asl) in
  if nums = [] then ALL_TAC (asl,w) else
  let mx = itlist max nums (-1) in
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let n = state_num_of_read_q30 th in n >= 0 && n < mx) (asl,w);;

(* the two nblk-dependent scalar values, for any nblk:
   x9 = len_bits >> 3 = 16 * nblk (USHR_128NBLK_ANY) and
   x5 = (x9 - 1) AND -128 = 128 * ((nblk - 1) DIV 8) (AND_MASK_16NBLK_ANY) *)
let USHR_128NBLK_ANY = prove
 (`!nblk. 128 * nblk < 2 EXP 64
        ==> word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN AP_TERM_TAC THEN ARITH_TAC);;

(* d = 128 * ((nblk - 1) DIV 8) = 0 for 1 <= nblk <= 8, so X5 = in_p and the
   <=8 band takes the b.ge to the tail *)
let D_ZERO_LE8 = prove
 (`!nblk. 1 <= nblk /\ nblk <= 8 ==> 128 * ((nblk - 1) DIV 8) = 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(nblk - 1) DIV 8 = 0` (fun th -> REWRITE_TAC[th; MULT_CLAUSES]) THEN
  MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC);;

(* The dispatch cmp x9,#0x40 ; b.le to the small-message path at 0x34/0x38   *)
(* (front steps 7, 8), with x9 = word (16 * nblk) from the lsr x9,x1,#3: for *)
(* nblk >= 5 the b.le falls through (16 * nblk >= 80 > 64) and the front     *)
(* runs on; nblk <= 4 takes the small-message path (WB_FUSED_kBLOCK).        *)
(* GUARD_LE_FALLTHRU resolves the branch condition for 5 <= nblk, by         *)
(* arithmetic on word (16 * nblk) alone; the prefix stepper adds it to the   *)
(* assumptions before stepping 7--8, so that the stepper folds the branch to *)
(* the fall-through.                                                         *)
let GUARD_LE_FALLTHRU = prove
 (`!nblk. 5 <= nblk /\ 16 * nblk < 2 EXP 63
      ==> (~(~(val (word_sub (word (16 * nblk):int64) (word 64)) = 0) /\
             (ival (word_sub (word (16 * nblk):int64) (word 64)) < &0 <=>
              ~(ival (word (16 * nblk):int64) - &64 =
                ival (word_sub (word (16 * nblk):int64) (word 64))))) <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word (16 * nblk):int64) (word 64) = word(16 * nblk - 64)`
    SUBST1_TAC THENL
   [MP_TAC(SPECL [`16 * nblk`; `64`] (INST_TYPE[`:64`,`:N`] WORD_SUB)) THEN
    ASM_SIMP_TAC[ARITH_RULE `5 <= nblk ==> 64 <= 16 * nblk`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[IVAL_WORD_SMALL;
               ARITH_RULE `16 * nblk < 2 EXP 63 ==> 16 * nblk - 64 < 2 EXP 63`] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `(16 * nblk - 64) MOD 2 EXP 64 = 16 * nblk - 64` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* The union hypotheses contain 5 <= nblk but not 1 <= nblk
   (wbn_front_hyps_uni_tm above), so ASSUME `1 <= nblk` would add a
   hypothesis that is not in the goal, and the justification of the
   enclosing SUBGOAL_THEN would fail (Failure "ABS").  So this tactic keeps
   only the assumptions 5 <= nblk and 128 * nblk < 2 EXP 64, from which
   ARITH_TAC derives the bounds needed by USHR_128NBLK_ANY,
   AND_MASK_16NBLK_ANY and INPUT_BYTES_TO_BYTE128_LANES. *)
let NBLK_ARITH_UNI_TAC =
  MP_TAC(ASSUME `5 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

(* ---- buffer-form band statements ---------------------------------------- *)
let mk_outp_read i =
  let addr = if i = 0 then `out_p:int64`
    else subst [mk_small_numeral(16*i),`nnn:num`] `word_add out_p (word nnn):int64` in
  subst [addr,`aaa:int64`] `read (memory :> bytes128 (aaa:int64)) s:int128`;;

let mk_ghash_list k =
  mk_flist(map (fun i -> mk_comb(`word_bytereverse:int128->int128`, mk_cph i)) (0--(k-1)));;

(* The band-exit counter write-back conjunct in spine form,
   read [ivec_p] = gcm_ctr_inc_iter k ctr0, used by mk_band_goal and closed
   by WB_IVEC_CLOSE_TAC in the band tails. *)
let mk_ivec_conj k = subst [mk_small_numeral k,`kkk:num`]
    `read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter kkk ctr0`;;

(* ---- recomposition machinery -------------------------------------------- *)
let arith_16k k = ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `16` (mk_small_numeral k),
                                   mk_small_numeral(16*k)));;

let arith_128k k = ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `128` (mk_small_numeral k),
                                    mk_small_numeral(128*k)));;

(* doubled frame for ENSURES_FRAME_SUBSUMED (F ,, F subsumes to F) *)
let fdbl_at k =
  let fs = subst [mk_small_numeral(16*k),`sss:num`]
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(out_p:int64, sss); memory :> bytes(tag_p:int64, 16);
                memory :> bytes(ivec_p:int64, 16); memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31]` in
  mk_binop `(,,):(armstate->armstate->bool)->(armstate->armstate->bool)->(armstate->armstate->bool)` fs fs;;

let mk_habbrev j =
  let hv = mk_var("h"^string_of_int j, `:int128`) in
  ABBREV_TAC (mk_eq(hv, mk_comb(`byteswap128:int128->int128`, hdot j))) THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`byteswap128:int128->int128`, hv), hdot j)) ASSUME_TAC THENL
  [EXPAND_TAC ("h"^string_of_int j) THEN REWRITE_TAC[BYTESWAP128_INVOLUTION]; ALL_TAC];;

(* The 4 seam memory cells the weak precondition drops, which the tail never
   reads (proving the back-legs without them checks this): [sp+72] is the
   zero the front stores next to the reduction constant at [sp+64]; tag_p and
   ivec_p are consumed only through Q19, Q16 (the tag) and Q0..Q7, Q30 (the
   counter); in_p block 0 arrives pre-loaded in Q9. *)
let wbn_tail_drop_lhs = [
  `read (memory :> bytes64 (word_add stackpointer (word 72))) (s:armstate)`;
  `read (memory :> bytes128 tag_p) (s:armstate)`;
  `read (memory :> bytes128 ivec_p) (s:armstate)`;
  `read (memory :> bytes128 in_p) (s:armstate)`];;

(* Replace the fixed per-band X9 count with a generic value.  The residual   *)
(* tail is shared by fixed bands (return_value = 16*r) and shifted           *)
(* whole-call tails (return_value = 16*nblk), and it does not write X9.      *)
let wbn_replace_x9 value pred =
  let sv, body = dest_abs pred in
  let x9lhs = subst [sv,`s:armstate`] `read X9 s` in
  let cs = conjuncts body in
  let cs' = map (fun c ->
    if is_eq c && lhs c = x9lhs then mk_eq(x9lhs,value) else c) cs in
  mk_abs(sv, end_itlist (curry mk_conj) cs');;

(* 5-cell drop: the 4 memory cells plus dead X1; X9 stays in the contract.   *)
let wbn_tail_drop_lhs5 = wbn_tail_drop_lhs @ [`read X1 (s:armstate)`];;

let wbn_band_return k =
  subst [mk_small_numeral(16*k),`sss:num`] `word sss:int64`;;

(* ========================================================================= *)
(* 2. The symbolic counter layer.                                            *)
(*                                                                           *)
(* gcm_ctr_add w ivec adds w to the top 32-bit lane of ivec read             *)
(* byte-reversed, which gives the loop invariant a closed form of the        *)
(* counter at a symbolic block index (GCM_CTR_INC_ITER_AS_ADD):              *)
(*   gcm_ctr_inc_iter k x = gcm_ctr_add (word k) x.                          *)
(* The layer (gcm_ctr_add, GCM_CTR_ADD_LANES, GCM_CTR_INC_ITER_AS_ADD, and   *)
(* the SUBW_RAW lemmas and GCM_CTR_RAW_INCR of gcm_ctr_raw, which is defined *)
(* before wb_front_postcond) comes here, ahead of the nblk > 8 proof,        *)
(* because WB_IVEC_CLOSE_TAC below uses it for the counter write-back of the *)
(* band tails.                                                               *)
(*                                                                           *)
(* A direct BITBLAST of GCM_CTR_ADD_LANES does not scale: its BDD would      *)
(* contain the symbolic 32-bit addend.  The factoring below keeps every      *)
(* BITBLAST wiring-only, so that word_add never meets the BDD.               *)
(* ========================================================================= *)

let gcm_ctr_add = new_definition
 `gcm_ctr_add (w:32 word) (ivec:128 word) : 128 word =
   word_insert ivec (96,32)
     (word_bytereverse
        (word_add (word_bytereverse (word_subword ivec (96,32):(32)word)) w))`;;

let GCM_CTR_ADD_1 = prove
 (`gcm_ctr_add (word 1) = gcm_ctr_inc`,
  REWRITE_TAC[FUN_EQ_THM; gcm_ctr_add; gcm_ctr_inc]);;

(* wiring-only: byte decomposition of the byte-reversed top lane *)
let BREV_TOP_LANE = prove
 (`!ctr0:int128.
     word_bytereverse (word_subword ctr0 (96,32):32 word) =
     word_join
      (word_join (word_subword ctr0 (96,8):8 word) (word_subword ctr0 (104,8):8 word):16 word)
      (word_join (word_subword ctr0 (112,8):8 word) (word_subword ctr0 (120,8):8 word):16 word)`,
  GEN_TAC THEN BITBLAST_TAC);;

(* wiring-only: insert of brev s as the byte-join tower; s stays free, so the
   abstract add never enters the BDD *)
let INSERT_BREV_WIRING = prove
 (`!(ctr0:int128) (s:32 word).
     word_insert ctr0 (96,32) (word_bytereverse s) : 128 word =
     word_join
      (word_join
       (word_join
        (word_join (word_subword s (0,8):8 word) (word_subword s (8,8):8 word):16 word)
        (word_join (word_subword s (16,8):8 word) (word_subword s (24,8):8 word):16 word)
        :32 word)
       (word_join
        (word_join (word_subword ctr0 (88,8):8 word) (word_subword ctr0 (80,8):8 word):16 word)
        (word_join (word_subword ctr0 (72,8):8 word) (word_subword ctr0 (64,8):8 word):16 word)
        :32 word) :64 word)
      (word_join
       (word_join
        (word_join (word_subword ctr0 (56,8):8 word) (word_subword ctr0 (48,8):8 word):16 word)
        (word_join (word_subword ctr0 (40,8):8 word) (word_subword ctr0 (32,8):8 word):16 word)
        :32 word)
       (word_join
        (word_join (word_subword ctr0 (24,8):8 word) (word_subword ctr0 (16,8):8 word):16 word)
        (word_join (word_subword ctr0 (8,8):8 word) (word_subword ctr0 (0,8):8 word):16 word)
        :32 word) :64 word)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* the generic-w lanes lemma: RHS built programmatically from
   GCM_CTR_INC_LANES with `w` for `word 1` (exactly the Q-lane shape the
   front simulation produces); proof is pure rewriting *)
let GCM_CTR_ADD_LANES =
  let lanes_w = subst [`w:32 word`,`word 1:32 word`]
    (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES)))) in
  let gl = list_mk_forall([`w:32 word`;`ctr0:int128`],
    mk_eq(list_mk_comb(`gcm_ctr_add`,[`w:32 word`;`ctr0:int128`]), lanes_w)) in
  prove(gl,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[gcm_ctr_add; BREV_TOP_LANE; INSERT_BREV_WIRING]);;

(* algebra of the symbolic add *)
let SUBWORD_INSERT_TOP = prove
 (`!(x:int128) (v:32 word). word_subword (word_insert x (96,32) v : int128) (96,32) = v`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let INSERT_INSERT_TOP = prove
 (`!(x:int128) (u:32 word) (v:32 word).
     word_insert (word_insert x (96,32) (u:32 word) : int128) (96,32) (v:32 word) : int128 =
     word_insert x (96,32) v`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let BREV_BREV_32 = prove
 (`!s:32 word. word_bytereverse (word_bytereverse s) = s`,
  GEN_TAC THEN BITBLAST_TAC);;

let INSERT_SELF_TOP = prove
 (`!x:int128. word_insert x (96,32) (word_subword x (96,32):32 word) : int128 = x`,
  GEN_TAC THEN BITBLAST_TAC);;

let GCM_CTR_ADD_COMPOSE = prove
 (`!(u:32 word) (v:32 word) (x:int128).
     gcm_ctr_add v (gcm_ctr_add u x) = gcm_ctr_add (word_add u v) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gcm_ctr_add] THEN
  REWRITE_TAC[SUBWORD_INSERT_TOP; INSERT_INSERT_TOP; BREV_BREV_32] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let GCM_CTR_ADD_0 = prove
 (`!x:int128. gcm_ctr_add (word 0) x = x`,
  GEN_TAC THEN REWRITE_TAC[gcm_ctr_add; WORD_ADD_0; BREV_BREV_32; INSERT_SELF_TOP]);;

(* the closed form the ENSURES_WHILE invariant needs: counter at symbolic
   block index k *)
let GCM_CTR_INC_ITER_AS_ADD = prove
 (`!k x:int128. gcm_ctr_inc_iter k x = gcm_ctr_add (word k) x`,
  INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[gcm_ctr_inc_iter; GCM_CTR_ADD_0];
    ASM_REWRITE_TAC[gcm_ctr_inc_iter] THEN
    REWRITE_TAC[GSYM GCM_CTR_ADD_1; GCM_CTR_ADD_COMPOSE] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[ADD1; GSYM WORD_ADD] THEN
    CONV_TAC WORD_RULE]);;

(* The 4 lane-extraction lemmas of gcm_ctr_raw, which prove GCM_CTR_RAW_INCR
   without a WORD_BLAST over the symbolic w (which does not scale, as for
   GCM_CTR_ADD_LANES above).  Each is WORD_SIMPLE_SUBWORD_CONV, which extracts
   the lane, then WORD_BLAST: w only appears added to the top lane, so the
   addend never enters the BDD. *)
let SUBW_RAW_96 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (96,32):32 word =
   word_add (word_join (word_join (word_subword ctr0 (96,8):8 word) (word_subword ctr0 (104,8):8 word):16 word)
     (word_join (word_subword ctr0 (112,8):8 word) (word_subword ctr0 (120,8):8 word):16 word):32 word) w`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;

let SUBW_RAW_64 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (64,32):32 word =
   word_join (word_join (word_subword ctr0 (64,8):8 word) (word_subword ctr0 (72,8):8 word):16 word)
     (word_join (word_subword ctr0 (80,8):8 word) (word_subword ctr0 (88,8):8 word):16 word):32 word`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;

let SUBW_RAW_32 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (32,32):32 word =
   word_join (word_join (word_subword ctr0 (32,8):8 word) (word_subword ctr0 (40,8):8 word):16 word)
     (word_join (word_subword ctr0 (48,8):8 word) (word_subword ctr0 (56,8):8 word):16 word):32 word`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;

let SUBW_RAW_0 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (0,32):32 word =
   word_join (word_join (word_subword ctr0 (0,8):8 word) (word_subword ctr0 (8,8):8 word):16 word)
     (word_join (word_subword ctr0 (16,8):8 word) (word_subword ctr0 (24,8):8 word):16 word):32 word`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;

(* The increment add v30.4s,v30.4s,v31.4s (v31 = word 2^96) is a lane-wise
   32-bit add: the model emits it as a word_join of
   word_add (word_subword v30 lane) (word c), with c = 1 on the top lane and
   0 on the others.  It advances the raw counter by 1. *)
let GCM_CTR_RAW_INCR = prove
 (`word_join
    (word_join
     (word_add (word_subword (gcm_ctr_raw w ctr0) (96,32):32 word) (word 1))
     (word_add (word_subword (gcm_ctr_raw w ctr0) (64,32):32 word) (word 0)):64 word)
    (word_join
     (word_add (word_subword (gcm_ctr_raw w ctr0) (32,32):32 word) (word 0))
     (word_add (word_subword (gcm_ctr_raw w ctr0) (0,32):32 word) (word 0)):64 word):int128 =
    gcm_ctr_raw (word_add w (word 1)) ctr0`,
  REWRITE_TAC[SUBW_RAW_96; SUBW_RAW_64; SUBW_RAW_32; SUBW_RAW_0; WORD_ADD_0] THEN
  GEN_REWRITE_TAC RAND_CONV [gcm_ctr_raw_def] THEN
  REWRITE_TAC[WORD_RULE
    `!(x:32 word) w. word_add (word_add x w) (word 1) = word_add x (word_add w (word 1))`]);;

(* ------------------------------------------------------------------------- *)
(* The band-tail ivec write-back closer.                                     *)
(*                                                                           *)
(* Each band r stores rev32(v30) to [ivec_p] at the end of its tail.  The    *)
(* counter register comes in from the seam as                                *)
(*   Q30 = gcm_ctr_raw (word 8) ctr0,                                        *)
(* and the cascade decrements it 8 - r times by sub v30 (the exact-8 drain,  *)
(* r = 8, not at all), so the stored value is                                *)
(*   rev32 (gcm_ctr_raw (word r) ctr0) = gcm_ctr_add (word r) ctr0           *)
(*                                     = gcm_ctr_inc_iter r ctr0.            *)
(* The close runs entirely in 32-bit-lane algebra (SUBW_RAW_* pin the sub    *)
(* cascade to the top lane, GCM_CTR_ADD_LANES gives the reversed target), so *)
(* that no 128-bit blast meets the symbolic counter.                         *)
(* ------------------------------------------------------------------------- *)
let sub_chain c n =
  let rec build acc k = if k=0 then acc
    else build (mk_comb(mk_comb(`word_sub:32 word->32 word->32 word`,acc),
                        mk_comb(`word:num->32 word`,mk_small_numeral c))) (k-1) in
  let lh = build `x:32 word` n in
  WORD_RULE(mk_eq(lh, if c=0 then `x:32 word`
                       else mk_comb(mk_comb(`word_sub:32 word->32 word->32 word`,`x:32 word`),
                                    mk_comb(`word:num->32 word`,mk_small_numeral n))));;

let SUBW_NORM r = WORD_RULE(subst[mk_small_numeral(8-r),`d:num`; mk_small_numeral r,`rr:num`]
  `word_sub (word_add (x:32 word) (word 8)) (word d) = word_add x (word rr)`);;

let WB_IVEC_CLOSE_TAC r =
  REWRITE_TAC[GCM_CTR_INC_ITER_AS_ADD] THEN
  REWRITE_TAC[sub_chain 1 (8-r); sub_chain 0 (8-r)] THEN
  REWRITE_TAC[gcm_ctr_raw_def; SUBW_RAW_96; SUBW_RAW_64; SUBW_RAW_32; SUBW_RAW_0] THEN
  REWRITE_TAC[SUBW_NORM r; WORD_SUB_0] THEN
  GEN_REWRITE_TAC RAND_CONV [GCM_CTR_ADD_LANES] THEN
  W(fun (_,gw) ->
     let atom = find_term (fun t -> match t with
       | Comb(Comb(Const("word_add",_),_),Comb(Const("word",_),_)) -> true | _ -> false) gw in
     SPEC_TAC(atom, `aa:32 word`)) THEN
  GEN_TAC THEN CONV_TAC WORD_BLAST;;

(* ========================================================================= *)
(* The small-message path, nblk <= 4.  The b.le at 0x38 (front step 8)       *)
(* branches to L256_dec_small (0x1334), which loads the counter, the tag and *)
(* the round keys and dispatches on x9 (through L256_dec_small_ge3 for nblk  *)
(* >= 3) to L256_dec_small_seed_k.  small_seed_k seeds the GHASH accumulator *)
(* with Xi' * H^k and enters the chain small_blk_k, .., small_blk_1 at       *)
(* small_blk_k: each decrypts one block and folds its ciphertext into the    *)
(* accumulator with the matching power of H; small_blk_1 also reduces,       *)
(* stores the tag, the counter and the last plaintext block, and             *)
(* L256_dec_small_done branches to L256_dec_frame_restore (0x119c, pc+4508), *)
(* the core exit.                                                            *)
(*                                                                           *)
(* WB_FUSED_kBLOCK (k = 1..4) proves each path from the core entry pc+0x1c,  *)
(* and mk_band_from_fused restates it as the band goal mk_band_goal k by     *)
(* ENSURES_PRECONDITION_THM, without re-simulation (prove_band needs         *)
(* 5 <= nblk).  The four proofs share the tactics that follow: the KEEPGHALL *)
(* discard and stepper, which keep the GHASH accumulators across a window,   *)
(* JOIN_IS_CTR0, INLINE_SELFCONTAINED and DEC_BRIDGE_ROUTEB_TAC, the GHASH   *)
(* bridge for k >= 2; the k = 1 bridge has its own lemmas and closer.        *)
(* ========================================================================= *)

(* KEEPGHALL discard: drop every fact that mentions an older state, except
   the facts about Q16-Q26 and Q30 and the key-table reads, so that the GHASH
   accumulators and their operands survive. *)
let DISCARD_OLDSTATE_KEEPGHALL_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_htbl t = match t with
      Var("htable_p",_) -> true
    | Comb(a,b) -> mentions_htbl a || mentions_htbl b | Abs(_,t2) -> mentions_htbl t2 | _ -> false in
  let rec mentions_ghreg t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> n="Q16"||n="Q17"||n="Q18"||n="Q19"||n="Q20"||n="Q21"||n="Q22"||n="Q23"||n="Q24"||n="Q25"||n="Q26"||n="Q30" | _ -> false)
    | Comb(a,b) -> mentions_ghreg a || mentions_ghreg b | Abs(_,t2) -> mentions_ghreg t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_ghreg (concl thm) then false else
    if (match concl thm with
        | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),cmp),_)),_) -> mentions_htbl cmp
        | _ -> false) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else if not(mem v us) then true else true);;

(* The per-step normalizer of the small path, Q-scoped and fixpoint-memoized.
   GCM_SIMD_SIMPLIFY_CORE_QSCOPED_TAC applies the three rewrite passes of
   GCM_SIMD_SIMPLIFY_CORE_TAC to the `read Qn s = ...` assumptions only, and
   skips those whose conclusion gcm_simd_fixpt_tbl records as already at a
   fixpoint.  In the KEEPGHALL windows the discard keeps the whole multi-block
   GHASH accumulator history, so the assumption list grows large, and most of
   it (memory reads, nonoverlapping facts, flags) is never rewritten by the
   SIMD rules.  The passes act on an assumption through its conclusion alone,
   so skipping a recorded fixpoint gives the same result as applying them.
   CLEAR_KEEPGHALL_MEMO_TAC empties the table at the start of each
   WB_FUSED_kBLOCK proof, so that each proof is hermetic. *)
let gcm_simd_fixpt_tbl : (term,unit) Hashtbl.t = Hashtbl.create 8192;;

let CLEAR_KEEPGHALL_MEMO_TAC : tactic =
  fun (asl,w) -> Hashtbl.clear gcm_simd_fixpt_tbl; ALL_TAC (asl,w);;

(* Block 0's AES input is rev32 of rev32 of the loaded counter block ctr0,
   which the simulation leaves as the join of the sixteen bytes of ctr0. *)
let JOIN_IS_CTR0 = prove(
 `word_join
    (word_join
     (word_join
      (word_join (word_subword (ctr0:int128) (120,8):8 word) (word_subword ctr0 (112,8):8 word):16 word)
      (word_join (word_subword ctr0 (104,8):8 word) (word_subword ctr0 (96,8):8 word):16 word):32 word)
     (word_join
      (word_join (word_subword ctr0 (88,8):8 word) (word_subword ctr0 (80,8):8 word):16 word)
      (word_join (word_subword ctr0 (72,8):8 word) (word_subword ctr0 (64,8):8 word):16 word):32 word):64 word)
    (word_join
     (word_join
      (word_join (word_subword ctr0 (56,8):8 word) (word_subword ctr0 (48,8):8 word):16 word)
      (word_join (word_subword ctr0 (40,8):8 word) (word_subword ctr0 (32,8):8 word):16 word):32 word)
     (word_join
      (word_join (word_subword ctr0 (24,8):8 word) (word_subword ctr0 (16,8):8 word):16 word)
      (word_join (word_subword ctr0 (8,8):8 word) (word_subword ctr0 (0,8):8 word):16 word):32 word):64 word):int128
  = ctr0`,
  CONV_TAC WORD_BLAST);;

(* INLINE_SELFCONTAINED reg st npass: rewrite `read reg st = ...` with the
   facts about the other states until its right side mentions no other state
   (at most npass rounds), so that the older states can be discarded. *)
let INLINE_SELFCONTAINED reg st npass : tactic = fun (asl,w) ->
  let lhs_t = parse_term (Printf.sprintf "read %s %s" reg st) in
  let rec nonSt tm = match tm with
      Comb(Comb(Const("read",_),_),stv) ->
        (match stv with Var(n,_) when n<>st -> [stv] | _ -> [])
    | Comb(a,b) -> union (nonSt a) (nonSt b) | Abs(_,t) -> nonSt t | _ -> [] in
  let target_rhs aslx =
    try rhs(concl(snd(List.find (fun (_,th) -> try lhs(concl th)=lhs_t with _->false) aslx)))
    with Not_found -> `T` in
  let rec go n (asl,w) =
    if n <= 0 then ALL_TAC (asl,w)
    else if nonSt (target_rhs asl) = [] then ALL_TAC (asl,w)
    else
      let picks = mapfilter (fun (_,th) ->
        match concl th with
        | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),stv)),_)
            when (match stv with Var(nm,_)->nm<>st|_->false) -> th
        | _ -> fail()) asl in
      (RULE_ASSUM_TAC(fun th ->
         if (try lhs(concl th) = lhs_t with _ -> false)
         then REWRITE_RULE picks th else th) THEN go (n-1)) (asl,w) in
  go npass (asl,w);;

(* DEC_BRIDGE_ROUTEB_TAC: the GHASH bridge close for k >= 2.  The bridges
   BRIDGE_CLOSE_{2,3,4}_CPH*_TAC below are thin wrappers of it: they share the
   prelude and the finisher and differ only in the spec equation spec_eq and
   in three identities between Karatsuba products that MERGE_2BLK_TAC does
   not pair.  The machine multiplies the seed and block 0 by H^k separately,
   the spec multiplies their XOR once, so each identity says that a product
   whose operand is an XOR is the XOR of the products of the two parts:
   bridge_qq_land distributes the product over the XOR (CONJUNCT1
   WORD_PMUL_XOR); bridge_qq_mid, for the middle product, whose operands are
   nested subword/join terms, folds the two parts and compares the operands
   (PMUL_CONG_128, WORD_BLAST).  The caller passes the bridge state sN,
   spec_eq (from its spec_to_byteform lemma, GMULTk_FULL_CORRECT_BA at its
   dec_bridge_specl list and the H-power facts) and the three
   (product, part, part) name triples. *)
let bridge_qq_land (a,b,c) : tactic =
  SUBGOAL_THEN (parse_term (Printf.sprintf "(%s:int128) = word_xor %s %s" a b c))
    (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC [a;b;c] THEN
    GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 WORD_PMUL_XOR] THEN
    REWRITE_TAC[WORD_XOR_ACI]; ALL_TAC];;

let bridge_qq_mid (a,b,c) : tactic =
  SUBGOAL_THEN (parse_term (Printf.sprintf "(%s:int128) = word_xor %s %s" a b c))
    (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC [a;b;c] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM (CONJUNCT1 WORD_PMUL_XOR)] THEN
    MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC];;

let FOLD_MID2 = prove(
  `word_xor
     (word_pmul
       (word_xor
         (word_subword
           (word_subword
             (word_join (word_reversefields 8 (cph:int128)) (word_reversefields 8 cph):256 word) (64,128):128 word)
            (0,64):64 word)
         (word_reversefields 8 (word_subword cph (64,64):64 word)))
       (word_xor (word_subword (h:int128) (0,64):64 word) (word_subword h (64,64):64 word)))
     (word_pmul
       (word_xor
         (word_subword
           (word_subword
             (word_join
               (word_join (word_reversefields 8 (word_subword (xi:int128) (0,64):64 word))
                          (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word)
               (word_join (word_reversefields 8 (word_subword xi (0,64):64 word))
                          (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word):256 word)
             (64,128):128 word)
            (0,64):64 word)
         (word_reversefields 8 (word_subword xi (64,64):64 word)))
       (word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word))) : int128
   = word_pmul (word_xor (word_subword h (64,64):64 word) (word_subword h (0,64):64 word))
       (word_xor
         (word_xor (word_reversefields 8 (word_subword xi (64,64):64 word))
                   (word_reversefields 8 (word_subword cph (64,64):64 word)))
         (word_xor (word_reversefields 8 (word_subword xi (0,64):64 word))
                   (word_reversefields 8 (word_subword cph (0,64):64 word))))`,
  REWRITE_TAC[JOINMID; JOIN_SUBWORD_RULES; WORD_SUBWORD_SUBWORD; RF8_SUBWORD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM (CONJUNCT1 WORD_PMUL_XOR)] THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
  MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* ---- nblk = 2 ---- *)

let spec_to_byteform_2 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1] =
       polyval_reduce_prop3
        (word_xor
          (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h2))
          (word_pmul (word_bytereverse cph1) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`] GHASH_POLYVAL_ACC_2)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let dec_bridge_specl_2_cph1 =
  [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h2:int128`;
   `word_bytereverse cph1:int128`; `byteswap128 h:int128`];;

(* The GMULT3_FULL_CORRECT_BA operands for nblk = 3: block 0 with the tag
   folded in times H^3, block 1 times H^2, block 2 times H (byte-reversed
   blocks, byteswapped key powers). *)
let dec_bridge_specl_3_cph2 =
  [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h3:int128`;
   `word_bytereverse cph1:int128`; `byteswap128 h2:int128`;
   `word_bytereverse cph2:int128`; `byteswap128 h:int128`];;

let dec_bridge_specl_4_cph3 =
  [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h4:int128`;
   `word_bytereverse cph1:int128`; `byteswap128 h3:int128`;
   `word_bytereverse cph2:int128`; `byteswap128 h2:int128`;
   `word_bytereverse cph3:int128`; `byteswap128 h:int128`];;

(* ========================================================================= *)
(* The bridge to the band goals.  The postcondition and the frame of         *)
(* WB_FUSED_kBLOCK are those of mk_band_goal k under cph_i :=                *)
(* bytes_to_int128 (SUB_LIST (16 * i,16) ibytes); only the preconditions     *)
(* differ (the band goal reads the whole input buffer and states             *)
(* htable_mem_dec, the fused theorems read each block and each table slot),  *)
(* bridged by INPUT_BYTES_TO_BYTE128_LANES and the htable_mem_dec unfold.    *)
(* The side conditions of the fused theorems on hk, h2 .. h4 discharge by    *)
(* HK_LOW/HI_IS_KARA, karatsuba_mid and BYTESWAP128_INVOLUTION.              *)
(* ========================================================================= *)

let HK_LOW_IS_KARA = prove
 (`!a b:64 word. word_subword (word_join a b:int128) (0,64):64 word = b`,
  CONV_TAC WORD_BLAST);;

let HK_HI_IS_KARA = prove
 (`!a b:64 word. word_subword (word_join a b:int128) (64,64):64 word = a`,
  CONV_TAC WORD_BLAST);;

(* The instantiation of the fused theorems (s42_fused_specl_args k): the
   H powers as the lets of htable_mem_dec compute them (hb = byteswap128 h,
   h2 = byteswap128 (polyval_dot hb hb), h3 and h4 one more polyval_dot
   each), the packed Karatsuba mids hk and h3k, and the input blocks of
   ibytes. *)
let s42_hb_tm = `byteswap128 (h:int128)`;;

let rec s42_hdot_raw j =
  if j <= 1 then s42_hb_tm
  else mk_comb(mk_comb(`polyval_dot:int128->int128->int128`, s42_hdot_raw (j-1)), s42_hb_tm);;

let s42_hpow j = mk_comb(`byteswap128:int128->int128`, s42_hdot_raw j);;

let s42_km t = mk_comb(`karatsuba_mid`, t);;

let s42_mk_join a b = mk_comb(mk_comb(`word_join:(64)word->(64)word->int128`, a), b);;

let s42_hk_tm  = s42_mk_join (s42_km (s42_hpow 2)) (s42_km `h:int128`);;

let s42_h3k_tm = s42_mk_join (s42_km (s42_hpow 4)) (s42_km (s42_hpow 3));;

let s42_cph_tm i = subst [mk_small_numeral(16*i),`nnn:num`]
  `bytes_to_int128 (SUB_LIST (nnn,16) (ibytes:byte list))`;;

let s42_ptr_args = [`pc:num`;`stackpointer:int64`;`out_p:int64`;`tag_p:int64`;`ivec_p:int64`;
                `in_p:int64`;`key_p:int64`;`htable_p:int64`];;

(* ------------------------------------------------------------------------- *)
(* The readable band theorems and the <=8-block dispatch theorem.            *)
(*                                                                           *)
(* They follow from the BUF band theorems without simulation: only the       *)
(* presentation of the input and the output changes, by bridges that do not  *)
(* involve the machine, applied through ENSURES_PRECONDITION_THM and         *)
(* ENSURES_POSTCONDITION_THM.  The bridges come in two layers (neither is a  *)
(* named specification):                                                     *)
(*   1. byte_list_at plumbing (BYTE_LIST_AT_TO_READ_BYTES,                   *)
(*      BYTE_LIST_AT_WHOLE_CTR, prove_wb_wrapper): the per-block stores and  *)
(*      the explicit ghash_polyval_acc -> gcm_dec_pt_bytes and               *)
(*      gcm_dec_final_xi;                                                    *)
(*   2. NIST vocabulary (htable_mem_8, GCM_DEC_FINAL_XI_NIST,                *)
(*      nist_input_block_bytes): the twisted-key POLYVAL objects -> the      *)
(*      SP 800-38D nist_ghash under the free NIST hash key H, with           *)
(*      byteswap128 h = ghash_twist H.                                       *)
(* The eight AESn_GCM_DEC_ALT_{1..8}BLOCK statements are written out         *)
(* literally, as the specification.  DISPATCH covers len_bits = 128 * nblk   *)
(* for 1 <= nblk <= 8; longer inputs are the nblk > 8 proof below, and       *)
(* len_bits = 0 and the non-multiples of 128, which return 0 without         *)
(* touching memory, are handled in the subroutine theorems further below.    *)
(* ------------------------------------------------------------------------- *)

(* ---- step 1: input bridge (byte_list_at -> the whole-buffer read) ---- *)
let BYTE_LIST_AT_TO_READ_BYTES = prove
 (`!bl (ptr:int64) (len:int64) s.
    byte_list_at bl ptr len s /\ LENGTH bl = val len
    ==> read (memory :> bytes (ptr, val len)) s = num_of_bytelist bl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[byte_list_at] THEN STRIP_TAC THEN
  SUBGOAL_THEN `num_of_bytelist (bl:byte list) = num_of_bytelist (SUB_LIST (0, val (len:int64)) bl)` SUBST1_TAC THENL
   [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`val (len:int64)`; `ptr:int64`; `bl:byte list`; `s:armstate`] BYTE_LIST_TO_NUM_THM) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(fun th -> ASM_REWRITE_TAC[GSYM th]));;

let ghash_wholes = [GCM_DEC_GHASH_BLOCKS_WHOLE_1;GCM_DEC_GHASH_BLOCKS_WHOLE_2;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_3;GCM_DEC_GHASH_BLOCKS_WHOLE_4;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_5;GCM_DEC_GHASH_BLOCKS_WHOLE_6;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_7;GCM_DEC_GHASH_BLOCKS_WHOLE_8];;

(* ------------------------------------------------------------------------- *)
(* NIST-vocabulary bridge layer (the statement shape of the 4-way kernels).  *)
(*   - htable_mem_8: htable_mem_4-style named memory predicate over h_power  *)
(*     indexing, for the 12-slot AWS-LC key table (packed Karatsuba mids).   *)
(*   - GCM_DEC_FINAL_XI_NIST: gcm_dec_final_xi = byte-reversed nist_ghash    *)
(*     under byteswap128 h = ghash_twist H (Gueron Prop 1 via                *)
(*     NIST_GHASH_IS_POLYVAL from common/ghash_nist_bridge.ml).              *)
(*   - nist_input_block_bytes: the NIST (big-endian) view of input block i   *)
(*     of a byte list, with the LIST_OF_SEQ_NIST_INPUT bridges to            *)
(*     gcm_dec_ghash_blocks.                                                 *)
(*   - wordlist_from_memory key condensation: KEY_READS_FROM_WORDLIST and    *)
(*     RK_ETA_15 relate the round-key list rk to the 15 bytes128 key reads.  *)
(* ------------------------------------------------------------------------- *)

(* ---- karatsuba_mid ignores the byteswap of its argument ---- *)
let KARATSUBA_MID_BYTESWAP = prove
 (`!x:int128. karatsuba_mid (byteswap128 x) = karatsuba_mid x`,
  GEN_TAC THEN REWRITE_TAC[karatsuba_mid; byteswap128] THEN
  CONV_TAC WORD_BLAST);;

(* ---- h_power 0..7 unfolded to the explicit left-nested dot chains ---- *)
let H_POWER_UNFOLD_7 = prove
 (`h_power (hb:int128) 0 = hb /\
   h_power hb 1 = polyval_dot hb hb /\
   h_power hb 2 = polyval_dot (polyval_dot hb hb) hb /\
   h_power hb 3 = polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb /\
   h_power hb 4 = polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb /\
   h_power hb 5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb /\
   h_power hb 6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) hb /\
   h_power hb 7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) hb) hb`,
  REWRITE_TAC[num_CONV `7`; num_CONV `6`; num_CONV `5`; num_CONV `4`;
              num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;

(* ---- htable_mem_dec in h_power form, without the nested lets ---- *)
let HTABLE_MEM_DEC_H_POWER = prove
 (`!(h:int128) (ptr:int64) (s:armstate).
     htable_mem_dec h ptr s <=>
     read (memory :> bytes128 ptr) s = byteswap128 (h_power (byteswap128 h) 0) /\
     read (memory :> bytes128 (word_add ptr (word 16))) s =
       word_join (karatsuba_mid (h_power (byteswap128 h) 1))
                 (karatsuba_mid (h_power (byteswap128 h) 0)) /\
     read (memory :> bytes128 (word_add ptr (word 32))) s = byteswap128 (h_power (byteswap128 h) 1) /\
     read (memory :> bytes128 (word_add ptr (word 48))) s = byteswap128 (h_power (byteswap128 h) 2) /\
     read (memory :> bytes128 (word_add ptr (word 64))) s =
       word_join (karatsuba_mid (h_power (byteswap128 h) 3))
                 (karatsuba_mid (h_power (byteswap128 h) 2)) /\
     read (memory :> bytes128 (word_add ptr (word 80))) s = byteswap128 (h_power (byteswap128 h) 3) /\
     read (memory :> bytes128 (word_add ptr (word 96))) s = byteswap128 (h_power (byteswap128 h) 4) /\
     read (memory :> bytes128 (word_add ptr (word 112))) s =
       word_join (karatsuba_mid (h_power (byteswap128 h) 5))
                 (karatsuba_mid (h_power (byteswap128 h) 4)) /\
     read (memory :> bytes128 (word_add ptr (word 128))) s = byteswap128 (h_power (byteswap128 h) 5) /\
     read (memory :> bytes128 (word_add ptr (word 144))) s = byteswap128 (h_power (byteswap128 h) 6) /\
     read (memory :> bytes128 (word_add ptr (word 160))) s =
       word_join (karatsuba_mid (h_power (byteswap128 h) 7))
                 (karatsuba_mid (h_power (byteswap128 h) 6)) /\
     read (memory :> bytes128 (word_add ptr (word 176))) s = byteswap128 (h_power (byteswap128 h) 7)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[htable_mem_dec] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[H_POWER_UNFOLD_7; KARATSUBA_MID_BYTESWAP; BYTESWAP128_INVOLUTION]);;

(* ---- the named key-table predicate over the abstract key hk ---- *)
(* htable_mem_8 hk ptr s is the shared predicate of aes_gcm_spec.ml, and
   HTABLE_MEM_8_FLAT (aes_gcm_common.ml) states it as 12 flat conjuncts.
   hk is the POLYVAL-side key (byteswap128 of the h slot in memory); with
   hk = ghash_twist H this is the analogue of the htable_mem_4 (ghash_twist
   ...) hypothesis of the 4-way kernels, extended to 8 powers and 12 slots
   (the AWS-LC layout with packed Karatsuba mids). *)
let HTABLE_MEM_DEC_IS_HTABLE_MEM_8 = prove
 (`!(h:int128) (ptr:int64) (s:armstate).
     htable_mem_dec h ptr s <=> htable_mem_8 (byteswap128 h) ptr s`,
  REWRITE_TAC[HTABLE_MEM_DEC_H_POWER; HTABLE_MEM_8_FLAT]);;

(* word_bytereverse = word_reversefields 8 at :128. *)
let BREV_RF8_128 = prove
 (`word_bytereverse (x:int128) = word_reversefields 8 x`,
  REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM] WORD_BYTEREVERSE_REVERSEFIELDS]);;

let BREV_RF8_INV_128 = prove
 (`!x:int128. word_bytereverse (word_reversefields 8 x) = x`,
  REWRITE_TAC[GSYM BREV_RF8_128; WORD_BYTEREVERSE_BYTEREVERSE]);;

(* ---- the tag spec in nist_ghash vocabulary ---- *)
(* The band statements quantify the raw h slot of the key table; the 4-way
   kernels quantify the NIST key H with the twist applied in the hypothesis.
   The two are related by byteswap128 h = ghash_twist H, under which
   gcm_dec_final_xi is a byte-reversed nist_ghash (Gueron Prop 1 via
   NIST_GHASH_IS_POLYVAL). *)
let GCM_DEC_FINAL_XI_NIST = prove
 (`!(H:int128) (h:int128) len x xi.
     byteswap128 h = ghash_twist H
     ==> gcm_dec_final_xi len x xi h =
         word_bytereverse
           (nist_ghash H (word_bytereverse xi)
              (MAP word_bytereverse (gcm_dec_ghash_blocks len x)))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[gcm_dec_final_xi; NIST_GHASH_IS_POLYVAL]);;

(* ---- the NIST (big-endian) view of input block i ---- *)
let nist_input_block_bytes = new_definition
 `nist_input_block_bytes (x:byte list) (i:num) : int128 =
    word_reversefields 8 (bytes_to_int128 (SUB_LIST (16 * i, 16) x))`;;

(* list_of_seq (nist_input_block_bytes x) N =
   MAP word_bytereverse (gcm_dec_ghash_blocks (16*N) x) *)
let build_list_of_seq_nist n =
  let goal = list_mk_forall([`x:byte list`],
    mk_eq(list_mk_comb(`list_of_seq:(num->int128)->num->int128 list`,
            [mk_comb(`nist_input_block_bytes`,`x:byte list`); mk_small_numeral n]),
          mk_comb(`MAP (word_bytereverse:int128->int128)`,
            list_mk_comb(`gcm_dec_ghash_blocks`, [mk_small_numeral(16*n);`x:byte list`])))) in
  prove(goal,
    GEN_TAC THEN REWRITE_TAC[el (n-1) ghash_wholes; MAP] THEN
    REWRITE_TAC(map num_CONV (map mk_small_numeral (rev(1--n)))) THEN
    REWRITE_TAC[LIST_OF_SEQ; o_DEF; nist_input_block_bytes; BREV_RF8_128] THEN
    CONV_TAC NUM_REDUCE_CONV);;

let LIST_OF_SEQ_NIST_INPUT = map build_list_of_seq_nist (1--8);;

(* byteswap128 (byteswap128 (ghash_twist H)) = ghash_twist H, for the
   instantiation h := byteswap128 (ghash_twist H). *)
let bsw_inv = SPEC `ghash_twist H` BYTESWAP128_INVOLUTION;;

(* d = 128*((nblk-1) DIV 8) > 128 for nblk >= 17 (the main-loop skip b.ge then
   falls through) *)
let D_GT_128 = prove
 (`!nblk. 17 <= nblk ==> (128 < 128 * (nblk - 1) DIV 8 <=> T)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `2 <= q ==> 128 < 128 * q`) THEN
  SUBGOAL_THEN `16 <= nblk - 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN ASM_ARITH_TAC);;

(* The raw counter absorbs a prior gcm_ctr_add into its offset:
      gcm_ctr_raw v (gcm_ctr_add u x) = gcm_ctr_raw (word_add u v) x
   (GCM_CTR_RAW_ABSORB below, with the lane lemmas it needs; gcm_ctr_raw_def is
   defined before wb_front_postcond, whose Q30 conjunct uses it).
   INNER_TAIL_FEED_TAC uses its numeral form GCM_CTR_RAW_ABSORB_NUM to match
   the shifted tail's Q30 precondition (the shift sets ctr0 :=
   gcm_ctr_add (word (8*(q+1))) ctr0) against the seam's Q30.  The proof works
   lane by lane: gcm_ctr_raw reads only the four 32-bit lanes of its argument
   and gcm_ctr_add changes only the lane (96,32), so the low three lanes pass
   through and the top lane composes the two adds; no blast meets the symbolic
   32-bit addend. *)
let BREV_LANE_64 = prove
 (`!ctr0:int128.
     word_join (word_join (word_subword ctr0 (64,8):8 word) (word_subword ctr0 (72,8):8 word):16 word)
       (word_join (word_subword ctr0 (80,8):8 word) (word_subword ctr0 (88,8):8 word):16 word) =
     word_bytereverse (word_subword ctr0 (64,32):32 word)`,
  GEN_TAC THEN BITBLAST_TAC);;

let BREV_LANE_32 = prove
 (`!ctr0:int128.
     word_join (word_join (word_subword ctr0 (32,8):8 word) (word_subword ctr0 (40,8):8 word):16 word)
       (word_join (word_subword ctr0 (48,8):8 word) (word_subword ctr0 (56,8):8 word):16 word) =
     word_bytereverse (word_subword ctr0 (32,32):32 word)`,
  GEN_TAC THEN BITBLAST_TAC);;

let BREV_LANE_0 = prove
 (`!ctr0:int128.
     word_join (word_join (word_subword ctr0 (0,8):8 word) (word_subword ctr0 (8,8):8 word):16 word)
       (word_join (word_subword ctr0 (16,8):8 word) (word_subword ctr0 (24,8):8 word):16 word) =
     word_bytereverse (word_subword ctr0 (0,32):32 word)`,
  GEN_TAC THEN BITBLAST_TAC);;

(* gcm_ctr_raw in 32-bit-lane form: top lane = word_add(brev of z top lane) w,
   the other three lanes = byte-reverse of z's lanes. *)
let GCM_CTR_RAW_LANEFORM = prove
 (`!w z:int128. gcm_ctr_raw w z =
    word_join
     (word_join (word_add (word_bytereverse (word_subword z (96,32):32 word)) w)
                (word_bytereverse (word_subword z (64,32):32 word)):64 word)
     (word_join (word_bytereverse (word_subword z (32,32):32 word))
                (word_bytereverse (word_subword z (0,32):32 word)):64 word):int128`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN
  REWRITE_TAC[GSYM BREV_TOP_LANE; GSYM BREV_LANE_64; GSYM BREV_LANE_32; GSYM BREV_LANE_0]);;

(* the low 3 lanes are unaffected by an insert into the top 32-bit lane *)
let SUBWORD_INSERT_LOW_LANE = prove
 (`!(x:int128) (nw:32 word).
     (word_subword (word_insert x (96,32) nw : int128) (0,32):32 word = word_subword x (0,32)) /\
     (word_subword (word_insert x (96,32) nw : int128) (32,32):32 word = word_subword x (32,32)) /\
     (word_subword (word_insert x (96,32) nw : int128) (64,32):32 word = word_subword x (64,32))`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN BITBLAST_TAC);;

let GCM_CTR_RAW_ABSORB = prove
 (`!(u:32 word) (v:32 word) (x:int128).
     gcm_ctr_raw v (gcm_ctr_add u x) = gcm_ctr_raw (word_add u v) x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GCM_CTR_RAW_LANEFORM] THEN
  REWRITE_TAC[gcm_ctr_add] THEN
  REWRITE_TAC[SUBWORD_INSERT_TOP; SUBWORD_INSERT_LOW_LANE; BREV_BREV_32] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC]);;

let GCM_CTR_RAW_ABSORB_NUM = prove
 (`!a b (x:int128).
     gcm_ctr_raw (word b) (gcm_ctr_add (word a) x) = gcm_ctr_raw (word (a + b)) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GCM_CTR_RAW_ABSORB] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* pure-arith closer for the nblk >= 17 side conditions *)
let NBLK_ARITH_TAC =
  MP_TAC(ASSUME `17 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

(* pure-arith closer for the union-band side conditions *)
let NBLK_ARITH_GE9_TAC =
  MP_TAC(ASSUME `9 <= nblk`) THEN
  MP_TAC(ASSUME `128 * nblk < 2 EXP 64`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* 5. GHASH 8-block extension algebra (no simulation).                       *)
(*                                                                           *)
(* The invariant's Q19 is the byte-reversed GHASH fold                       *)
(*   ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)                 *)
(*     (MAP word_bytereverse (list_of_seq blk (8 * i)))                      *)
(* over the raw ciphertext blocks blk k =                                    *)
(* bytes_to_int128 (SUB_LIST (16*k,16) ibytes), k < 8i.  The loop body and   *)
(* the prepretail each fold one more 8-block group (blocks 8i..8i+7, one     *)
(* Horner step per block, each block byte-reversed and XORed into the        *)
(* accumulator), so the fold over 8(i+1) blocks must equal the fold over 8i  *)
(* blocks continued by the 8 Horner steps, in the machine's 8-block          *)
(* byteform.  This is list algebra over GHASH_ACC_APPEND                     *)
(* (common/polyval_ghash.ml) and list_of_seq.                                *)
(* ------------------------------------------------------------------------- *)

(* list_of_seq splits at any offset (APPEND-at-end recursion, induct on n) *)
let LIST_OF_SEQ_SPLIT = prove
 (`!(f:num->int128) m n. list_of_seq f (m + n) =
     APPEND (list_of_seq f m) (list_of_seq (\j. f (m + j)) n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; list_of_seq; APPEND_NIL] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; list_of_seq; APPEND_ASSOC]);;

(* generic group-extension of the byte-reversed GHASH fold: split m+n *)
let GHASH_ACC_GROUP_EXTEND = prove
 (`!(g:num->int128) H acc m n.
    ghash_polyval_acc H acc (MAP word_bytereverse (list_of_seq g (m + n))) =
    ghash_polyval_acc H
      (ghash_polyval_acc H acc (MAP word_bytereverse (list_of_seq g m)))
      (MAP word_bytereverse (list_of_seq (\j. g (m + j)) n))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_OF_SEQ_SPLIT; MAP_APPEND; GHASH_ACC_APPEND]);;

(* clean 8-element unfold of list_of_seq (numerals, no SUC towers) *)
let LIST_OF_SEQ_8 = prove
 (`!f:num->int128. list_of_seq f 8 =
    [f 0; f 1; f 2; f 3; f 4; f 5; f 6; f 7]`,
  GEN_TAC THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[num_CONV `8`; num_CONV `7`; num_CONV `6`;
    num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`;
    LIST_OF_SEQ])) THEN
  REWRITE_TAC[o_THM] THEN CONV_TAC(DEPTH_CONV NUM_SUC_CONV) THEN REWRITE_TAC[]);;

(* The main lemma: extend the invariant's GHASH fold by one 8-block group.   *)
(* The right-hand side is the 8*i fold continued by a fold over the 8 new    *)
(* raw ciphertext blocks 8*i .. 8*i+7.  BODY_Q19_CLOSE_ALGEBRA rewrites with *)
(* it, at blk := \k. bytes_to_int128 (SUB_LIST (16*k,16) ibytes).            *)
let GHASH_ACC_8BLOCK_EXTEND = prove
 (`!(blk:num->int128) H acc i.
    ghash_polyval_acc H acc
      (MAP word_bytereverse (list_of_seq blk (8 * (i + 1)))) =
    ghash_polyval_acc H
      (ghash_polyval_acc H acc (MAP word_bytereverse (list_of_seq blk (8 * i))))
      (MAP word_bytereverse
        [blk (8 * i); blk (8 * i + 1); blk (8 * i + 2); blk (8 * i + 3);
         blk (8 * i + 4); blk (8 * i + 5); blk (8 * i + 6); blk (8 * i + 7)])`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `8 * (i + 1) = 8 * i + 8` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GHASH_ACC_GROUP_EXTEND] THEN
  REWRITE_TAC[LIST_OF_SEQ_8] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ADD_CLAUSES]);;

(* The body GHASH-close bridge: spec_to_byteform_wb8 of the <=8-block chain  *)
(* generalized from the tail's incoming accumulator word_bytereverse xi to   *)
(* an arbitrary one, acc (the running fold that Q19 holds at the start of    *)
(* the loop body).  The H-power hypotheses and the machine byteform on the   *)
(* right are the same, and so is the proof (GHASH_POLYVAL_ACC_8, the         *)
(* hypotheses, WORD_RULE), which does not depend on the accumulator being    *)
(* xi.  BODY_Q19_CLOSE_ALGEBRA composes it with GHASH_ACC_8BLOCK_EXTEND      *)
(* (acc := the invariant's 8*i fold) to close the loop body's Q19.           *)
let SPEC_TO_BYTEFORM_WB8_ACC = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 =
   polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 =
   polyval_dot
   (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h5 =
   polyval_dot
   (polyval_dot
    (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h6 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h7 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot
      (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
      (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h8 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot
      (polyval_dot
       (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
       (byteswap128 h))
      (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (acc:int128)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
        word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
        word_bytereverse cph6; word_bytereverse cph7] =
       polyval_reduce_prop3
       (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_xor acc (word_bytereverse cph0)) (byteswap128 h8))
        (word_pmul (word_bytereverse cph1) (byteswap128 h7)))
        (word_pmul (word_bytereverse cph2) (byteswap128 h6)))
        (word_pmul (word_bytereverse cph3) (byteswap128 h5)))
        (word_pmul (word_bytereverse cph4) (byteswap128 h4)))
        (word_pmul (word_bytereverse cph5) (byteswap128 h3)))
        (word_pmul (word_bytereverse cph6) (byteswap128 h2)))
       (word_pmul (word_bytereverse cph7) (byteswap128 h)))`,
  STRIP_TAC THEN REWRITE_TAC[GHASH_POLYVAL_ACC_8] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* The composed Q19 close of the loop body: the invariant's Q19 conjunct at  *)
(* i+1 equals the machine 8-block byteform with the invariant's own 8*i fold *)
(* as the incoming accumulator, by GHASH_ACC_8BLOCK_EXTEND (the 8*(i+1) fold *)
(* as the 8 new blocks on top of the 8*i fold) and SPEC_TO_BYTEFORM_WB8_ACC  *)
(* (acc := that 8*i fold).  The whole GHASH algebra of the body close is     *)
(* settled here, without simulation; build_q19_reduce_clean and              *)
(* build_q19_reduce_clean_idx (below) instantiate it for the Q19 closes of   *)
(* the loop body and the prepretail.                                         *)
let BODY_Q19_CLOSE_ALGEBRA = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 =
   polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 =
   polyval_dot
   (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h5 =
   polyval_dot
   (polyval_dot
    (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h6 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h7 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot
      (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
      (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h8 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot
      (polyval_dot
       (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
       (byteswap128 h))
      (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        (MAP word_bytereverse
         (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes))
          (8 * (i+1)))) =
        polyval_reduce_prop3
        (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
         (word_pmul (word_xor (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
           (MAP word_bytereverse
            (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) (8 * i))))
           (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+0),16) ibytes)))) (byteswap128 h8))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+1),16) ibytes))) (byteswap128 h7)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+2),16) ibytes))) (byteswap128 h6)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+3),16) ibytes))) (byteswap128 h5)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+4),16) ibytes))) (byteswap128 h4)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+5),16) ibytes))) (byteswap128 h3)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+6),16) ibytes))) (byteswap128 h2)))
        (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+7),16) ibytes))) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[GHASH_ACC_8BLOCK_EXTEND; MAP] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * i = 16 * (8*i+0)`] THEN
  MATCH_MP_TAC SPEC_TO_BYTEFORM_WB8_ACC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The GHASH reduction as a value equality.                                  *)
(*                                                                           *)
(* At the wire-in state (s289 in the loop body, s242 in the prepretail) the  *)
(* three Karatsuba accumulators are complete,                                *)
(*   PL = Q17 = Sum_k karatsuba_block_pl,                                    *)
(*   PH = Q19 = Sum_k karatsuba_block_ph,                                    *)
(*   PM = Q18 = Sum_k karatsuba_block_pm,                                    *)
(* with the reduction constant in Q16.  The simulation keeps them            *)
(* abbreviated (opaque), so after the reduction (in the loop body up to the  *)
(* eor3 at 0x9d0, s326) Q19 is the byteform on the left of                   *)
(* WBN_MACHINE_REDUCE_IS_PROP3_PACK below, over PL, PH and PM.  The lemma    *)
(* states that this byteform is                                              *)
(* polyval_reduce_prop3 (pack_corrected PL PH PM), with no outer             *)
(* word_reversefields: the form of BODY_Q19_CLOSE_ALGEBRA's right-hand side. *)
(*                                                                           *)
(* It is derived from the shared statement of this reduction,                *)
(* POLYVAL_REDUCE_G2 (aes_gcm_common.ml): pack_corrected (the zx/shl packing *)
(* the N-block GHASH Karatsuba layer is stated in) is karatsuba_join         *)
(* (PACK_CORRECTED_KARATSUBA_JOIN), so the right-hand side is                *)
(* polyval_reduce_g2 PL PH PM, and the byteform is the same xor of the same  *)
(* two pmuls up to rearrangement.  The statement keeps pack_corrected        *)
(* because KARA_ACC_PACK_HELPER, which packs the eight per-block triples in  *)
(* the Q19 close below, is stated with it.                                   *)
(* ------------------------------------------------------------------------- *)

let PACK_CORRECTED_KARATSUBA_JOIN = prove
 (`!pl ph pm:int128. pack_corrected pl ph pm = karatsuba_join pl ph pm`,
  REWRITE_TAC[pack_corrected; karatsuba_join] THEN BITBLAST_TAC);;

let POLYVAL_REDUCE_G2_KARATSUBA_JOIN = prove
 (`!p1 p2 p3:int128.
     polyval_reduce_g2 p1 p2 p3 = polyval_reduce_prop3 (karatsuba_join p1 p2 p3)`,
  REWRITE_TAC[karatsuba_join; POLYVAL_REDUCE_G2]);;

(* ------------------------------------------------------------------------- *)
(* Block-algebra reconciliation facts.  They bridge the machine's            *)
(* accumulators at the wire-in state (Q17/Q19/Q18 = the separable sums       *)
(* PL/PH/PM, in raw word_reversefields / word_join / byteswap128-tower form) *)
(* to the kara_acc projection of an 8-quad list, so that                     *)
(* KARA_ACC_PACK_HELPER and KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN pack them to *)
(* the sum of the word_pmul input_k h_k, the argument of                     *)
(* polyval_reduce_prop3 in BODY_Q19_CLOSE_ALGEBRA.  All are WORD_BLAST       *)
(* identities over free variables.                                           *)
(* ------------------------------------------------------------------------- *)

(* fact 1: the two byte-reversal spellings coincide (the machine uses        *)
(* word_reversefields 8, the spec and kara side word_bytereverse).           *)
let WRF8_IS_BYTEREVERSE = prove
 (`!x:int128. word_reversefields 8 x = word_bytereverse x`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* fact 2: karatsuba_mid is byteswap-invariant (it XORs the two 64-bit       *)
(* halves, and byteswap128 swaps them).  It lets the htable mid cell         *)
(* `karatsuba_mid h` satisfy the precondition `word_subword hk (0,64) =      *)
(* karatsuba_mid (byteswap128 h)` of KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN.    *)
let KMID_BYTESWAP_INV = prove
 (`!h:int128. karatsuba_mid h = karatsuba_mid (byteswap128 h)`,
  GEN_TAC THEN REWRITE_TAC[karatsuba_mid; byteswap128] THEN CONV_TAC WORD_BLAST);;

(* fact 3 (block-0 SOFAR lane collapse): block 0's operand enters as a       *)
(* rot64'd word_join of the running accumulator SOFAR with the first         *)
(* ciphertext block.  The reduction takes the (64,64) / (0,64) sub-lane of   *)
(* the XOR of the two joins, which collapses to the plain (0,64) / (64,64)   *)
(* sub-lane of `word_xor S X`.                                               *)
let LANE_COLLAPSE = prove
 (`(!S X:int128. word_subword (word_xor (word_subword (word_join S S:256 word) (64,128):128 word)
                            (word_subword (word_join X X:256 word) (64,128):128 word)) (64,64):64 word
    = word_subword (word_xor S X) (0,64):64 word) /\
   (!S X:int128. word_subword (word_xor (word_subword (word_join S S:256 word) (64,128):128 word)
                            (word_subword (word_join X X:256 word) (64,128):128 word)) (0,64):64 word
    = word_subword (word_xor S X) (64,64):64 word)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* fact 4 (the mid-input lanes of a pmull2/pmull pair): the machine computes *)
(* the PM mid products two blocks at a time (a pmull2, then a pmull, over    *)
(* the packed lanes of blocks A and B), and the (64,64) / (0,64) sub-lane of *)
(* the XOR of the hi-join and the lo-join recovers each block's (lo XOR hi)  *)
(* mid-input.  PM_LANE_HI' and PM_LANE_LO' (used by build_q19_reduce_clean   *)
(* and build_q19_reduce_clean_idx) spell it in the (0,64)^(64,64) lane order *)
(* that karatsuba_block_pm produces: WORD_RULE treats the first argument of  *)
(* word_pmul as atomic, so the lane XOR must match syntactically.            *)
let PM_LANE_HI' = prove
 (`!A B:int128.
    word_subword (word_xor (word_join (word_subword (A:int128) (64,64):64 word) (word_subword (B:int128) (64,64):64 word):128 word)
                           (word_join (word_subword A (0,64):64 word) (word_subword B (0,64):64 word):128 word)) (64,64):64 word
    = word_xor (word_subword A (0,64):64 word) (word_subword A (64,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let PM_LANE_LO' = prove
 (`!A B:int128.
    word_subword (word_xor (word_join (word_subword (A:int128) (64,64):64 word) (word_subword (B:int128) (64,64):64 word):128 word)
                           (word_join (word_subword A (0,64):64 word) (word_subword B (0,64):64 word):128 word)) (0,64):64 word
    = word_xor (word_subword B (0,64):64 word) (word_subword B (64,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* The block-0 and block-1 PM mid-inputs.  The first pmull2/pmull pair folds *)
(* in the running accumulator SOFAR, so block 0's operand enters as a        *)
(* rot64'd word_join of SOFAR with the first ciphertext block (not the plain *)
(* packed pair the later blocks use).  These two lane lemmas recover the     *)
(* block-0 (outer (64,64), over word_xor SOFAR cph0) and block-1 (outer      *)
(* (0,64), over cph1) mid-inputs, in karatsuba_block_pm's (0,64)^(64,64)     *)
(* lane order, by WORD_BLAST over free ss (= SOFAR), xx0 (= rev cph0) and    *)
(* xx1 (= rev cph1).  With PM_LANE_HI' and PM_LANE_LO' (the plain pairs      *)
(* {2,3}, {4,5}, {6,7}) they reduce all 8 machine PM mid-inputs to the kara  *)
(* form, so that PROJ_PM (in the builders below) closes.                     *)
let LANE_COLLAPSE_PM_A = prove
 (`!ss xx0 xx1:int128.
    word_subword
     (word_xor
      (word_join
       (word_subword (word_xor (word_subword (word_join (ss:int128) ss:256 word) (64,128):128 word)
                               (word_subword (word_join (xx0:int128) xx0:256 word) (64,128):128 word)) (0,64):64 word)
       (word_subword xx1 (64,64):64 word):128 word)
      (word_join
       (word_subword (word_xor (word_subword (word_join (ss:int128) ss:256 word) (64,128):128 word)
                               (word_subword (word_join (xx0:int128) xx0:256 word) (64,128):128 word)) (64,64):64 word)
       (word_subword xx1 (0,64):64 word):128 word)) (64,64):64 word
    = word_xor (word_subword (word_xor ss xx0) (0,64):64 word)
               (word_subword (word_xor ss xx0) (64,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let LANE_COLLAPSE_PM_B = prove
 (`!ss xx0 xx1:int128.
    word_subword
     (word_xor
      (word_join
       (word_subword (word_xor (word_subword (word_join (ss:int128) ss:256 word) (64,128):128 word)
                               (word_subword (word_join (xx0:int128) xx0:256 word) (64,128):128 word)) (0,64):64 word)
       (word_subword xx1 (64,64):64 word):128 word)
      (word_join
       (word_subword (word_xor (word_subword (word_join (ss:int128) ss:256 word) (64,128):128 word)
                               (word_subword (word_join (xx0:int128) xx0:256 word) (64,128):128 word)) (64,64):64 word)
       (word_subword xx1 (0,64):64 word):128 word)) (0,64):64 word
    = word_xor (word_subword xx1 (0,64):64 word) (word_subword xx1 (64,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Wire-in tactics.  The extract stashes pl/ph/pm at the wire-in state into  *)
(* refs, before the ABBREV that makes the reduce window small; the close     *)
(* (run at the Q19 postcondition conjunct) rebuilds the CLEAN theorem from   *)
(* those refs and accepts it after mapping its concrete byteform LHS back to *)
(* the goal's PL/PH/PM-abbreviated form and the 8*(i+1) = 8*i+8 index        *)
(* normalization the postcondition preparation applied.                      *)
let wbn_q19_pl = ref `T` and wbn_q19_ph = ref `T` and wbn_q19_pm = ref `T`;;

let WBN_Q19_EXTRACT_ABBREV_TAC (sN:string) : tactic =
  fun (asl,w) ->
    let st = mk_var(sN,`:armstate`) in
    let get_rhs q =
      let c = find (fun c -> match c with
        | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),qc),s)),_) when qc=q && s=st -> true
        | _ -> false) (map (concl o snd) asl) in
      rand c in
    wbn_q19_pl := get_rhs `Q17`;
    wbn_q19_ph := get_rhs `Q19`;
    wbn_q19_pm := get_rhs `Q18`;
    (ABBREV_TAC (mk_eq(`PL:int128`, !wbn_q19_pl)) THEN
     ABBREV_TAC (mk_eq(`PH:int128`, !wbn_q19_ph)) THEN
     ABBREV_TAC (mk_eq(`PM:int128`, !wbn_q19_pm))) (asl,w);;

(* Push a read through the frame's write chain to `read c s` with
   COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV (common/components.ml), using the
   nonoverlapping assumptions, then close it by the precondition fact
   `read c s = value`.  The preservation legs of the _EXT theorems below apply
   it to each conjunct of R. *)
let WBN_PUSH_LHS_READ_TAC : tactic =
  W(fun (asl,w) ->
    let thl = map snd asl in
    let cxt = (NONOVERLAPPING_DRIVERS thl, FILTER_CANONIZE_ASSUMPTIONS thl) in
    CONV_TAC(LAND_CONV(COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV cxt))) THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* 9b. The raw counter Q30 in the loop invariant.                            *)
(*                                                                           *)
(* The first instruction of the body,                                        *)
(*   0x4bc  rev32 v5, v30                                                    *)
(* reads Q30, the running counter in the form the kernel keeps it, so the    *)
(* invariant must pin Q30, or Q5 stays symbolic in `read Q30 s0` and the     *)
(* body cannot close.  Every other vector register that the body reads       *)
(* before writing it is pinned by another conjunct.                          *)
(*                                                                           *)
(* gcm_ctr_raw w ctr0 is that form: each 32-bit lane of ctr0 byte-reversed,  *)
(* as rev32 reads it, with w added to the top lane.  The body computes rev32 *)
(* of v30, the AES input of block 8i+13, then add v30,v30,v31, which with    *)
(* v31 = word 2^96 advances the top lane to 8i+14, and so on for the 8       *)
(* blocks of the group.  So wbn_loop_invariant_raw has the conjunct          *)
(*   read Q30 s = gcm_ctr_raw (word (8 * i + 13)) ctr0                       *)
(* (inherited by wbn_loop_inv_core_raw).  WBN_FRONT_BUF's postcondition      *)
(* carries Q30 as a raw lane tower, which WBN_LOOP_INVARIANT_ENTRY_RAW       *)
(* rewrites to gcm_ctr_raw (word 13) ctr0 at i = 0 (gcm_ctr_raw_def, with    *)
(* the adds of 12 and 1 merged); the 8 adds of the body advance it from      *)
(* 8i+13 to 8(i+1)+13 = 8i+21.                                               *)
(*                                                                           *)
(* gcm_ctr_raw_def is defined with the front's term builders, and its lane   *)
(* lemmas (SUBW_RAW_*, GCM_CTR_RAW_INCR) are in Sec 2; this section has the  *)
(* two fold tactics.                                                         *)
(* ------------------------------------------------------------------------- *)

(* REV32_FOLD_TAC qd sn wtm: after a step rev32 vd,v30 that reads
   Q30 = gcm_ctr_raw wtm ctr0, rewrite the stepper's lane tower in
   `read qd sn = <tower>` (wherever it occurs in the assumptions) to
   gcm_ctr_add wtm ctr0, the AES input block for counter wtm.  The fold
   equation is proved on the fly from the tower in the assumption, for a
   fresh w:32 word in place of wtm: both sides are unfolded to lanes
   (gcm_ctr_raw_def, GCM_CTR_ADD_LANES), the symbolic top-lane sum is
   generalized to a fresh variable, and WORD_BLAST proves the rest, so it
   never meets the symbolic addend. *)
let REV32_FOLD_TAC (qd:string) (sn:string) (wtm:term) : tactic =
  fun (asl,gl) ->
    let tower = tryfind (fun (_,th) -> match concl th with
      | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),st)),r)
          when string_of_term c = qd && (try fst(dest_var st)=sn with _ -> false) -> r
      | _ -> fail()) asl in
    (* the fold for a fresh w:32 word, then w := wtm *)
    let tower_gen = subst [`w:32 word`, wtm] tower in
    let fold_thm = prove(mk_eq(tower_gen, `gcm_ctr_add w ctr0`),
      REWRITE_TAC[gcm_ctr_raw_def] THEN
      GEN_REWRITE_TAC RAND_CONV [GCM_CTR_ADD_LANES] THEN
      W(fun (_,gw) ->
         let atom = find_term (fun t -> match t with
           | Comb(Comb(Const("word_add",_),_),Var("w",_)) -> true | _ -> false) gw in
         SPEC_TAC(atom, `aa:32 word`)) THEN
      GEN_TAC THEN CONV_TAC WORD_BLAST) in
    let fold_spec = INST [wtm,`w:32 word`] fold_thm in
    RULE_ASSUM_TAC(REWRITE_RULE[fold_spec]) (asl,gl);;

(* CTR_RAW_INCR_FOLD_TAC qd sn wtm: the increment counterpart of
   REV32_FOLD_TAC.  After an `add v30,v30,v31` step, the assumption
     read qd sn = <single-add tower over gcm_ctr_raw wtm ctr0>
   (top lane word_add (word_subword (gcm_ctr_raw wtm ctr0) (96,32)) (word 1),
   the other lanes + 0) is rewritten by GCM_CTR_RAW_INCR at w := wtm to
     read qd sn = gcm_ctr_raw (word_add wtm (word 1)) ctr0.
   Fold once per add, before the next add nests the increments, so that only
   the single-add left-hand side of GCM_CTR_RAW_INCR ever has to match. *)
let CTR_RAW_INCR_FOLD_TAC (qd:string) (sn:string) (wtm:term) : tactic =
  let incr_spec = INST [wtm,`w:32 word`] GCM_CTR_RAW_INCR in
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),st)),_)
        when string_of_term c = qd && (try fst(dest_var st)=sn with _ -> false) ->
        REWRITE_RULE[incr_spec] th
    | _ -> th);;

(* The next group's raw ciphertext blocks 8(i+1) .. 8(i+1)+7, which the
   body's ldp's load into Q8..Q15, are derived at each load from the
   input-buffer loop constant
     read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes,
   which the body preserves (in_p is only read, and out_p is disjoint from
   it).  From the step-case bound i < (nblk-9) DIV 8, WBN_RAWCT_BOUND gives
     8(i+1)+m < nblk  for m < 8,
   and WBN_RAWCT_READ, by INPUT_BYTES_TO_BYTE128_LANES, the block reads
     read (memory :> bytes128 (in_p + 16*(8(i+1)+m))) s =
     bytes_to_int128 (SUB_LIST (16*(8(i+1)+m),16) ibytes),
   the invariant's values of Q8..Q15 at i+1. *)
let WBN_RAWCT_BOUND = prove
 (`i < (nblk - 9) DIV 8 /\ 9 <= nblk ==> !m. m < 8 ==> 8 * (i+1) + m < nblk`,
  STRIP_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 10a. Loop-body simulation machinery.                                      *)
(*                                                                           *)
(* The loop body 0x4bc..0xa08 (340 instructions) is one software-pipelined   *)
(* 8-block group: 8 AES keystream towers, the GHASH fold of the 8 ciphertext *)
(* blocks of the previous group, the counter advancing 8i+13 -> 8i+21 =      *)
(* 8(i+1)+13, 4 stp stores of 8 plaintext blocks, the ldp loads of the next  *)
(* group and the signed b.lt back-edge.  WBN_MAIN_LOOP_raw simulates it,     *)
(* s0..s340, as follows.                                                     *)
(* - Counter folds: after each rev32 vd,v30, REV32_FOLD_TAC "Qd" "sN"        *)
(*   `word (8*i+c)`; after each add v30,v30,v31, CTR_INCR_NORM_TAC "sN" c,   *)
(*   which folds it and normalizes the index to word (8*i+(c+1)).            *)
(* - Steps 1..13, the counter setup: ARM_STEPS_TAC, GCM_SIMD_SIMPLIFY_TAC.   *)
(* - Steps 14..289, AES and GHASH: ARM_STEPS_FOLD_KEEPDATA_TAC, which keeps  *)
(*   the latest read of each of Q0..Q19.                                     *)
(* - Steps 290..340, the GHASH reduction over the abbreviated accumulators,  *)
(*   the stores and the back-edge: ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC.       *)
(* - The back-edge b.lt at 0xa08: the NF/VF facts of the cmp x0,x5 come from *)
(*   WB_PTRCMP_FLAGS (a = 128*(i+2), d = 128*((nblk-1) DIV 8)) as separate   *)
(*   theorems rewritten into the assumptions (adding them to the goal with   *)
(*   MP_TAC breaks the stp step that follows).  The PC lands at              *)
(*     if 128*(i+2) < 128*((nblk-1) DIV 8) then 0x4bc else 0xa0c,            *)
(*   which WBN_PC_BRIDGE turns into the test i+1 < (nblk-9) DIV 8.           *)
(* ------------------------------------------------------------------------- *)

(* CTR_INCR_NORM_TAC sn c: fold the add v30 at state sn (CTR_RAW_INCR_FOLD_TAC
   on Q30), then normalize the counter index
     word_add (word (8*i+c)) (word 1)  to  word (8*i+(c+1)) *)
let CTR_INCR_NORM_TAC (sn:string) (c:int) : tactic =
  let cur = mk_comb(`word:num->32 word`,
    mk_binop `(+):num->num->num` `8*i` (mk_small_numeral c)) in
  let nrm = WORD_RULE (mk_eq(
    mk_binop `word_add:32 word->32 word->32 word` cur `word 1:32 word`,
    mk_comb(`word:num->32 word`,
      mk_binop `(+):num->num->num` `8*i` (mk_small_numeral (c+1))))) in
  CTR_RAW_INCR_FOLD_TAC "Q30" sn cur THEN RULE_ASSUM_TAC(REWRITE_RULE[nrm]);;

(* DISCARD_STALE_Q19_TAC: keep only the latest `read Q19 sN` fact (the GHASH
   accumulator, whose values at older states are dead); the Q19 analogue of
   DISCARD_STALE_Q18_TAC. *)
let state_num_of_q19_fact th =
  try let c = concl th in if not(is_eq c) then None else
    (match lhs c with
       Comb(Comb(Const("read",_),Const("Q19",_)),Var(sn,_))
         when String.length sn>1 && sn.[0]='s' ->
           Some(int_of_string(String.sub sn 1 (String.length sn-1)))
     | _ -> None) with _ -> None;;

let DISCARD_STALE_Q19_TAC : tactic = fun (asl,w) ->
  let nums = List.filter_map (fun (_,th) -> state_num_of_q19_fact th) asl in
  match nums with [] | [_] -> ALL_TAC (asl,w)
  | _ -> let mx = List.fold_left max 0 nums in
         DISCARD_ASSUMPTIONS_TAC (fun th ->
           (match state_num_of_q19_fact th with Some k -> k<mx | None -> false)) (asl,w);;

(* DISCARD_STALE_QREG_TAC qn: keep only the latest `read qn sN` fact of
   register qn.  DISCARD_STALE_DATA_TAC below applies it to each of Q0..Q19 for
   the KEEPDATA steppers. *)
let state_num_of_qreg qn th =
  try let c = concl th in if not(is_eq c) then None else
    (match lhs c with
       Comb(Comb(Const("read",_),Const(n,_)),Var(sn,_))
         when n=qn && String.length sn>1 && sn.[0]='s' ->
           Some(int_of_string(String.sub sn 1 (String.length sn-1)))
     | _ -> None) with _ -> None;;

let DISCARD_STALE_QREG_TAC qn : tactic = fun (asl,w) ->
  let nums = List.filter_map (fun (_,th) -> state_num_of_qreg qn th) asl in
  match nums with [] | [_] -> ALL_TAC (asl,w)
  | _ -> let mx = List.fold_left max 0 nums in
         DISCARD_ASSUMPTIONS_TAC (fun th ->
           (match state_num_of_qreg qn th with Some k -> k<mx | None -> false)) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* 10c. Loop-body close machinery.                                           *)
(*                                                                           *)
(* The steppers and resolvers of the body simulation.  The KEEPDATA steppers *)
(* keep the latest read of each of Q0..Q19, the keystreams in Q0..Q7         *)
(* included, which the store readbacks need.  The ldp's of the next group    *)
(* are resolved at load by RESOLVE_LDP2_TAC: an ldp leaves                   *)
(*   read Qk sN = read (memory :> bytes128 ADDR) s(N-1),                     *)
(* a memory read at the load-input state s(N-1), so the raw !m lemma has to  *)
(* be matched at s(N-1), not at sN.  RESOLVE_QREG_C matches it at the state  *)
(* of the register read's own memory read, and uses PURE_ONCE_REWRITE: plain *)
(* REWRITE would reduce 8*(i+1)+0 to 8*(i+1) and break the m = 0 ACCEPT.     *)
(* ------------------------------------------------------------------------- *)

(* The KEEPDATA discard: keep every fact that reads one of Q0..Q19
   (DISCARD_STALE_DATA_TAC then keeps only the latest read of each) and every
   fact that mentions no state but the current one; discard every other
   old-state fact. *)
let wbn_datawords_0_19 =
  ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q8";"Q9";
   "Q10";"Q11";"Q12";"Q13";"Q14";"Q15";"Q16";"Q17";"Q18";"Q19"];;

let DISCARD_OLDSTATE_KEEPDATA_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_data t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> List.mem n wbn_datawords_0_19 | _ -> false)
    | Comb(a,b) -> mentions_data a || mentions_data b | Abs(_,t2) -> mentions_data t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_data (concl thm) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else true);;

let DISCARD_STALE_DATA_TAC = MAP_EVERY DISCARD_STALE_QREG_TAC wbn_datawords_0_19;;

(* The KEEPDATA steppers normalize each step with one pass of the
   GCM_SIMD_SIMPLIFY_CORE_TAC rewrites, not with the double pass
   GCM_SIMD_SIMPLIFY_TAC.  The second pass only reaches a REV64 fixpoint that
   one pass can miss on a few steps, and the KEEPDATA windows of the loop body
   and of the prepretail, the only users of these steppers, do not need it.
   (The fronts, ARM_VSTEPS_FOLD_TAC and ARM_STEPS_FOLD_DISCARD_TAC use the
   double pass; the KEEPGH, Q18-latest and KEEPGHALL steppers also use one.)

   The pass is also Q-scoped and memoized, like those of gcm_simd_kgh_tbl and
   gcm_simd_fixpt_tbl: it is applied only to `read Qn s = ...` assumptions, the
   ones its rules are for, and skips an assumption whose conclusion
   gcm_simd_kd_tbl records as already a fixpoint.  The pass is a function of
   the conclusion alone, so skipping a recorded fixpoint changes nothing.
   CLEAR_KEEPDATA_MEMO_TAC empties the table at the start of each of the two
   simulations, so that each proof is self-contained. *)
let gcm_simd_kd_tbl : (term,unit) Hashtbl.t = Hashtbl.create 8192;;

let CLEAR_KEEPDATA_MEMO_TAC : tactic =
  fun (asl,w) -> Hashtbl.clear gcm_simd_kd_tbl; ALL_TAC (asl,w);;

(* The variant without the SIMD normalizer, for the reduction and the store
   windows: normalizing the pmulls by the [sp+64] reduction constant there, or
   the eor3 keystream towers the stores keep, blows the terms up, so these
   steps are taken symbolically. *)
let ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN
              DISCARD_STALE_DATA_TAC THEN DISCARD_OLDSTATE_KEEPDATA_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;

(* RESOLVE_QREG_C qreg scur m: resolve the raw read an ldp leaves,
     read qreg scur = read (memory :> bytes128 ADDR) sload,
   against the raw lemma at sload (the load-input state); PURE_ONCE_REWRITE
   keeps the m = 0 index 8*(i+1)+0 unreduced for the ACCEPT *)
let RESOLVE_QREG_C (qreg:string) (scur:string) (m:int) : tactic =
  fun (asl,w) ->
    let mnum = mk_small_numeral m in
    let th,addr,sload = tryfind (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(n,_)),Var(sn,_))),
             Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),
               Comb(Const("bytes128",_),addr))),Var(sl,_)))
          when n=qreg && sn=scur -> (th,addr,sl)
      | _ -> fail()) asl in
    let raw = tryfind (fun (_,t) -> match concl t with
        Comb(Const("!",_),Abs(Var("m",_),Comb(Comb(Const("==>",_),_),
          Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var(sl,_))),
               Comb(Const("bytes_to_int128",_),_))))) when sl=sload -> t
      | _ -> fail()) asl in
    let canon = vsubst[mnum,`m:num`] `word_add in_p (word (16 * (8*(i+1)+m))):int64` in
    let addr_eq = WORD_RULE (mk_eq(addr,canon)) in
    let raw_inst = MATCH_MP raw (ARITH_RULE(mk_comb(mk_comb(`(<):num->num->bool`,mnum),`8`))) in
    let target = mk_eq((parse_term (Printf.sprintf "read %s %s :int128" qreg scur)),
      vsubst[mnum,`m:num`] `bytes_to_int128 (SUB_LIST (16 * (8*(i+1)+m), 16) ibytes)`) in
    (SUBGOAL_THEN target ASSUME_TAC THENL
      [GEN_REWRITE_TAC LAND_CONV [th] THEN PURE_ONCE_REWRITE_TAC[addr_eq] THEN ACCEPT_TAC raw_inst;
       ALL_TAC]) (asl,w);;

(* the back-edge arithmetic: the b.lt compares 128 * (i + 2) with
   128 * ((nblk - 1) DIV 8), i.e. tests i + 1 < (nblk - 9) DIV 8 *)
let WBN_DIV_SHIFT = prove
 (`9 <= nblk ==> (nblk - 1) DIV 8 = (nblk - 9) DIV 8 + 1`,
  STRIP_TAC THEN
  SUBGOAL_THEN `nblk - 1 = (nblk - 9) + 1 * 8` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIV_ADD_MOD] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC);;

let WBN_PC_BRIDGE = prove
 (`9 <= nblk
   ==> ((128 * (i + 2) < 128 * (nblk - 1) DIV 8) <=> (i + 1 < (nblk - 9) DIV 8))`,
  DISCH_TAC THEN ASM_SIMP_TAC[WBN_DIV_SHIFT] THEN ARITH_TAC);;

(* premises of WB_PTRCMP_FLAGS at the back-edge, X0 = in_p+128*(i+2) (a)
   and X5 = 128*((nblk-1) DIV 8)+in_p (d): val in_p plus either offset is
   below 2^63, by val in_p + 16*nblk < 2^63 *)
let WBN_PTRCMP_PREMS = prove
 (`val (in_p:int64) + 16 * nblk < 2 EXP 63 /\ i < (nblk - 9) DIV 8
   ==> val (in_p:int64) + 128 * (i + 2) < 2 EXP 63 /\
       val (in_p:int64) + 128 * (nblk - 1) DIV 8 < 2 EXP 63`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
  MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ASM_ARITH_TAC);;

(* The caught-up GHASH accumulator: the loop invariant's Q19 at i := k + 1, the
   fold over all 8 * (k + 1) processed blocks.  This is the value of Q19 at the
   seam: the loop exits with the GHASH stream one 8-block group behind, and the
   prepretail folds that group in.  It is a function of the pinned inputs
   (xi, h, ibytes, nblk), not a fresh variable. *)
let wbn_caught_up = `ghash_polyval_acc (byteswap128 (h:int128)) (word_bytereverse (xi:int128))
    (MAP word_bytereverse
    (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) (ibytes:byte list)))
                 (8 * (((nblk:num) - 9) DIV 8 + 1))))`;;

(* The first tail block's index is in range: 8 * k + 8 < nblk for
   k = (nblk - 9) DIV 8 and 9 <= nblk, the index bound that
   WBN_PREPRETAIL_EXT2_UNIFIED passes to WBN_PREPRETAIL_EXT2_TAC. *)
let WBN_Q9_INDEX_LT_9 = prove
 (`!nblk. 9 <= nblk /\ 128 * nblk < 2 EXP 64 ==> 8 * ((nblk - 9) DIV 8) + 8 < nblk`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL[`nblk - 9`;`8`] DIVISION) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = (nblk - 9) DIV 8` THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The tail leg: from the seam to the core exit (WBN_PREP_TO_END).           *)
(*                                                                           *)
(* The tail back-legs WB_TAIL_GEN2_1..8 of the <=8-block chain start at the  *)
(* seam PC pc+3824 and run to the core exit pc+4508, closing the r-block     *)
(* GHASH with GMULT_FULL_CORRECT_BA (r = 1) or GMULT2..8_FULL_CORRECT_BA.    *)
(* They are proved once, before prove_band (which uses them too), where      *)
(* their goal builders wbn_dissect_band, wbn_tail_drop_lhs5,                 *)
(* wbn_weak_q_at5_return and wbn_tail_backleg_goal5_return are defined as    *)
(* well.  Here the seam post wbn_prepretail_post_ext2 feeds them at shifted  *)
(* indices (shift_vals r): precondition weakening, no re-simulation.         *)
(*                                                                           *)
(* The back-legs keep X9 generic (return_value).  The seam has               *)
(* X1 = word (128 * nblk) and X9 = word (16 * nblk), where a tail fixed to r *)
(* blocks would have word (128 * r) and word (16 * r), which differ for      *)
(* nblk >= 17.  The tail (0xef0..0x1198, and the exact-8 drain               *)
(* 0x11b4..0x1330) reads neither register, so the back-leg contract drops X1 *)
(* and keeps X9 as return_value: the shifted tail instantiates it to         *)
(* word (16 * nblk), a fixed band to word (16 * r).                          *)
(* ------------------------------------------------------------------------- *)

(* num_of_bytelist = num_of_wordlist on byte lists (used by
   WBN_INPUT_SLICE_GEN). *)
let NUM_OF_BYTELIST_EQ_WORDLIST = prove
 (`!l:byte list. num_of_bytelist l = num_of_wordlist l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_bytelist; num_of_wordlist; DIMINDEX_8] THEN ARITH_TAC);;

(* the three side conditions of the tail legs, at the whole-buffer length *)
let wbn_prep_to_end_extra_clauses =
  [`nonoverlapping (out_p:int64,16 * nblk) (tag_p:int64,16)`;
   `nonoverlapping (out_p:int64,16 * nblk) (ivec_p:int64,16)`;
   `nonoverlapping (tag_p:int64,16) (ivec_p:int64,16)`];;

(* ------------------------------------------------------------------------- *)
(* The tag fold and the output forall.                                       *)
(*                                                                           *)
(* The seam feed (INNER_TAIL_FEED_TAC with WB_TAIL_GEN2_r) gives the shifted *)
(* band's post:                                                              *)
(*   - PC = pc+4508, the core exit;                                          *)
(*   - the last r output stores, at out_p + 128*(k+1) + 16*i (i < r);        *)
(*   - the tag at tag_p: the caught-up accumulator continued over the r new  *)
(*     blocks.                                                               *)
(* It does not have the first 8*(k+1) output stores, which the seam post     *)
(* carries as its output forall.  The full-nblk contract needs               *)
(*   (a) that forall carried through the r-block tail, whose frame writes    *)
(*       only bytes (out_p+128(k+1),16*r), disjoint from the first           *)
(*       128*(k+1) bytes (ENSURES_ADD_PRESERVED), and                        *)
(*   (b) the tag fold, caught_up ++ [r new blocks] = list_of_seq cph nblk,   *)
(*       by GHASH_ACC_APPEND.                                                *)
(* The lemmas below are the list and tag algebra for (b).                    *)
(* ------------------------------------------------------------------------- *)

(* list_of_seq splits at any point into a prefix + a shifted suffix. *)
let LIST_OF_SEQ_ADD = prove
 (`!m (f:num->A) n. list_of_seq f (m + n) =
        APPEND (list_of_seq f m) (list_of_seq (\i. f (m + i)) n)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; LIST_OF_SEQ; APPEND; ETA_AX];
    REWRITE_TAC[ADD_CLAUSES; LIST_OF_SEQ; APPEND] THEN
    AP_TERM_TAC THEN ASM_REWRITE_TAC[o_DEF]]);;

(* LIST_OF_SEQ_CLAUSES (common/misc.ml) covers n = 0..4 only; the r-block tag
   fold needs the expansion up to n = 8.  Each is proved from the SUC recursion
   (num_CONV down to a count LIST_OF_SEQ_CLAUSES covers, then APPEND). *)
let LIST_OF_SEQ_CLAUSES_5_8 =
  let expand_los n =
    let suc_convs = map (fun k -> num_CONV (mk_small_numeral k)) (rev (5--n)) in
    prove(mk_forall(`f:num->A`,
       mk_eq(list_mk_comb(`list_of_seq:(num->A)->num->(A)list`,[`f:num->A`; mk_small_numeral n]),
             mk_list(map (fun i -> mk_comb(`f:num->A`, mk_small_numeral i)) (0--(n-1)), `:A`))),
      GEN_TAC THEN
      GEN_REWRITE_TAC TOP_DEPTH_CONV suc_convs THEN
      REWRITE_TAC[list_of_seq] THEN
      CONV_TAC(DEPTH_CONV NUM_SUC_CONV) THEN
      REWRITE_TAC[LIST_OF_SEQ_CLAUSES] THEN REWRITE_TAC[APPEND]) in
  end_itlist CONJ (map expand_los [5;6;7;8]);;

(* fold one gcm_ctr_inc into the running gcm_ctr_add offset (for the
   gcm_ctr_inc^i counters of the tail stores in WBN_PREP_TO_END_FULL_r) *)
let GCM_CTR_INC_FOLD = prove
 (`!w x. gcm_ctr_inc (gcm_ctr_add w x) = gcm_ctr_add (word_add w (word 1)) x`,
  REWRITE_TAC[GSYM GCM_CTR_ADD_1; GCM_CTR_ADD_COMPOSE]);;

(* nesting: the shifted band's i-th cph block = the global (8*(k+1)+i)-th. *)
let WBN_SUBLIST_SHIFT = prove
 (`!(ibytes:byte list) k i r. i < r
   ==> SUB_LIST (16 * i,16) (SUB_LIST (128 * (k + 1),16 * r) ibytes) =
       SUB_LIST (16 * (8 * (k + 1) + i),16) ibytes`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUB_LIST_MIN_GENERAL] THEN
  SUBGOAL_THEN `MIN 16 (16 * r - 16 * i) = 16` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `128 * (k + 1) + 16 * i = 16 * (8 * (k + 1) + i)` SUBST1_TAC THENL
   [ARITH_TAC; REFL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* WBN_PREP_TO_END_FULL_r for r = 2..8.                                      *)
(*                                                                           *)
(* They have the skeleton of WBN_PREP_TO_END_FULL_1; the parts that depend   *)
(* on r are OCaml int -> tactic closures, driven by                          *)
(* WBN_PREP_TO_END_FULL_r_TAC.                                               *)
(*                                                                           *)
(* The per-block algebra: for output block j = 8*(q+1)+i (0 <= i < r) the    *)
(* value the seam's forall states equals the r-block band's store.           *)
(* wbn_block_bridge_goal and wbn_block_bridge_tac prove that identity on its *)
(* own, goal form word_xor (word_xor cph tower) klast = store form word_xor  *)
(* cph (aesN_encrypt ...), reconciling                                       *)
(*   - the counter, by GCM_CTR_INC_FOLD:                                     *)
(*       gcm_ctr_inc_iter (8(q+1)+i) = gcm_ctr_add (word (8(q+1)+i))         *)
(*         = gcm_ctr_inc^i (gcm_ctr_add (word (8(q+1))));                    *)
(*   - the input slice, by WBN_SUBLIST_SHIFT:                                *)
(*       SUB_LIST (16*(8(q+1)+i),16) ibytes =                                *)
(*         SUB_LIST (16*i,16) (SUB_LIST (128(q+1),16*r) ibytes);             *)
(*   - the cipher: GSYM AES256_XOR_ENCRYPT_RECONSTRUCT (or its AES-128       *)
(*     counterpart), then WORD_RULE for the XOR reassociation.               *)
(* wbn_block_close_tac then reduces 16*i to a numeral (otherwise the goal's  *)
(* SUB_LIST (16*i,..) and word (16*i) do not match the store's numerals) and *)
(* reconciles the store address (flat for i = 0, nested for i >= 1).         *)
(* wbn_tag_fold_tac folds the explicit r-element tag list to list_of_seq by  *)
(* LIST_OF_SEQ_ADD and GHASH_ACC_APPEND, closing each element by             *)
(* WBN_SUBLIST_SHIFT.                                                        *)
(* ------------------------------------------------------------------------- *)

(* the goal-side and store-side counter for output block i (0<=i<r). *)
let wbn_full_goal_ctr i =
  subst[mk_small_numeral i,`i_:num`]
    `gcm_ctr_add (word (8 * (q + 1) + i_)) ctr0 :int128`;;

let wbn_full_store_ctr i =
  funpow i (fun t -> mk_comb(`gcm_ctr_inc:int128->int128`, t))
    `gcm_ctr_add (word (8 * (q + 1))) ctr0 :int128`;;

(* the goal-side and store-side output addresses for block i. *)
let wbn_full_goal_addr i =
  subst[mk_small_numeral i,`i_:num`]
    `word_add out_p (word (16 * (8 * (q + 1) + i_))):int64`;;

let wbn_full_store_addr i =
  if i = 0 then `word_add out_p (word (128 * (q + 1))):int64`
  else mk_comb(mk_comb(`word_add:int64->int64->int64`,
                       `word_add out_p (word (128 * (q + 1))):int64`),
               mk_comb(`word:num->int64`, mk_small_numeral(16 * i)));;

(* derive a banded leg (the wide >=17 band or the 9..16 band) from the
   union-band FREE_r: MATCH_MP_TAC on the same ensures term, ASM_REWRITE_TAC
   for the shared hypotheses, ASM_ARITH_TAC for the band.
   WBN_PREPRETAIL_EXT2_916 below is derived in the same way. *)
let wbn_prep_to_end_full_derive_tac free_thm =
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC free_thm THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Tag-side bridge lemmas (no simulation, symbolic nblk).                    *)
(*                                                                           *)
(* They turn the tag conjunct of wbn_end_post into the NIST nist_ghash form  *)
(* at a symbolic block count (LIST_OF_SEQ_NIST_INPUT of the <=8-block chain  *)
(* covers only N = 1..8).  WBN_TAG_NIST_BRIDGE is the tag rewrite of the     *)
(* spine postcondition, under the band identifications                       *)
(* byteswap128 h = ghash_twist H and xi = word_reversefields 8 tag0.         *)
(* ------------------------------------------------------------------------- *)

let MAP_LIST_OF_SEQ = prove
 (`!(g:A->B) f n. MAP g (list_of_seq f n) = list_of_seq (g o f) n`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN GEN_TAC THEN
  ASM_REWRITE_TAC[LIST_OF_SEQ; MAP; o_THM] THEN REWRITE_TAC[o_ASSOC]);;

let LIST_OF_SEQ_NIST_INPUT_SYM = prove
 (`!ibytes N.
     list_of_seq (nist_input_block_bytes ibytes) N =
     MAP word_bytereverse
       (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAP_LIST_OF_SEQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; nist_input_block_bytes; BREV_RF8_128]);;

let WBN_TAG_NIST_BRIDGE = prove
 (`!(H:int128) h xi tag0 ibytes nblk.
     byteswap128 h = ghash_twist H /\ xi = word_reversefields 8 tag0
     ==> word_bytereverse
           (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
             (MAP word_bytereverse
               (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) nblk))) =
         word_reversefields 8
           (nist_ghash H tag0 (list_of_seq (nist_input_block_bytes ibytes) nblk))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[NIST_GHASH_IS_POLYVAL; LIST_OF_SEQ_NIST_INPUT_SYM; BREV_RF8_128] THEN
  REWRITE_TAC[GSYM BREV_RF8_128; WORD_BYTEREVERSE_BYTEREVERSE]);;

(* ------------------------------------------------------------------------- *)
(* Output-side bridge lemmas (no simulation, symbolic nblk).                 *)
(*                                                                           *)
(* The symbolic-nblk analogues of GCM_DEC_PT_BYTES_WHOLE_k and               *)
(* BYTE_LIST_AT_WHOLE_CTR of the <=8-block chain: they turn the nblk-uniform *)
(* per-block store forall of wbn_end_post into                               *)
(* byte_list_at (gcm_dec_pt_bytes ..).                                       *)
(* ------------------------------------------------------------------------- *)

(* EL of gcm_dec_blocks_from at a symbolic index (the analogue of
   build_aes_ctr_el). *)
let EL_GCM_DEC_BLOCKS_FROM = prove
 (`!m base i x. i < m
     ==> EL i (gcm_dec_blocks_from base m x) =
         bytes_to_int128 (SUB_LIST (16 * (base + i),16) x)`,
  INDUCT_TAC THEN REWRITE_TAC[LT] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[GCM_DEC_BLOCKS_FROM_STEP; EL; HD; TL] THENL
   [REWRITE_TAC[ADD_CLAUSES];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`base + 1`; `n:num`; `x:byte list`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(base + 1) + n = base + SUC n` SUBST1_TAC THENL
     [ARITH_TAC; REFL_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Counter-model bridge to the NIST SP 800-38D nonce||counter form of the    *)
(* other AES-GCM proofs, for the nonce-named keystream of the exported       *)
(* theorems.                                                                 *)
(*                                                                           *)
(* This proof names counters gcm_ctr_inc_iter j ctr0, iterated from an       *)
(* opaque initial block ctr0.  The other proofs use                          *)
(*   ctr_block nonce ctr = word_join (nonce:96 word) (word ctr:int32)        *)
(* (NIST big-endian: a fixed 96-bit nonce and a 32-bit big-endian counter).  *)
(* These lemmas prove that the two models coincide: gcm_ctr_inc_iter is NIST *)
(* inc32 iterated on the nonce||counter block, conjugated by the byte        *)
(* reversal of the load, unconditionally (the 32-bit wrap is the intended    *)
(* mod 2^32 rollover).  GCM_CTR_INC_ITER_CTR_BLOCK lets the exported         *)
(* theorems name the nonce, through WBN_OUTPUT_POINTWISE_NONCE and           *)
(* GCM_CTR_INC_ITER_NIST_IVEC below.  ctr_block, inc32 on it                 *)
(* (INC32_CTR_BLOCK, ITER_INC32_CTR_BLOCK) and its relation to GCTR are      *)
(* in arm/proofs/utils/aes_gcm_spec.ml (loaded through aes_gcm_common.ml).   *)
(* ------------------------------------------------------------------------- *)

(* The bridge: gcm_ctr_inc_iter j ctr0 is the NIST nonce||counter block
   advanced by j, provided the byte-reversed ctr0 is nonce||c.  By
   GCM_CTR_INC_ITER_INC32 above, gcm_ctr_inc_iter j x is
   word_bytereverse (ITER j inc32 (word_bytereverse x)). *)
let GCM_CTR_INC_ITER_CTR_BLOCK = prove
 (`!j (nonce:96 word) c ctr0.
     word_bytereverse ctr0 = ctr_block nonce c
     ==> gcm_ctr_inc_iter j ctr0 = word_bytereverse (ctr_block nonce (c + j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GCM_CTR_INC_ITER_INC32] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ITER_INC32_CTR_BLOCK]);;

(* The counter write-back: the spines' gcm_ctr_inc_iter n, started from the  *)
(* shared ivec value for counter c, is the shared ivec value for n + c.      *)
let GCM_CTR_INC_ITER_NIST_IVEC = prove
 (`!n (nonce:96 word) c.
     gcm_ctr_inc_iter n (word_reversefields 8 (ctr_block nonce c)) =
     word_reversefields 8 (ctr_block nonce (n + c))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `nonce:96 word`; `c:num`;
                `word_reversefields 8 (ctr_block nonce c)`]
    GCM_CTR_INC_ITER_CTR_BLOCK) THEN
  REWRITE_TAC[BREV_RF8_INV_128] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[BREV_RF8_128; ADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* The exported contracts, in the shared AES-GCM vocabulary.                 *)
(*                                                                           *)
(* In each kernel proof WBN_DEC_VALID_CALL_CORRECT (the AAPCS64 wrapper at   *)
(* len_bits = 128 * nblk) is lifted from the spine                           *)
(* WBN_DEC_SUBROUTINE_BYTELIST by WBN_EXPORT_FROM_SPINE_TAC: the key words,  *)
(* the GHASH key and the counter block are pinned to the FIPS-197 / NIST     *)
(* convention and the input and output are restated per block.  The kernel's *)
(* NOIBT_SUBROUTINE_CORRECT theorem (any len_bits) adds the reject path of   *)
(* the entry guard to WBN_DEC_VALID_CALL_CORRECT.  These are about the       *)
(* trimmed code; the SUBROUTINE_CORRECT theorem about the full code follows  *)
(* from the NOIBT one by ARM_ADD_IBT_RULE.  c is the free counter of data    *)
(* block 0: the kernel increments whatever ivec holds, and c = 2 is the      *)
(* standard NIST SP 800-38D instance.  The machine code writes every one of  *)
(* the 32 vector registers; beyond the ABI frame, the core frame lists       *)
(* Q8-Q15 (WB_CORE_FRAME_EQ below).                                          *)
(* ------------------------------------------------------------------------- *)

(* The frame of the core safety theorem AESn_GCM_DEC_ALT_SAFE.
   MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI already covers Q0-Q7, Q16-Q31 and
   the top halves of Q8-Q15, so beyond it the core theorem lists only Q8-Q15,
   whose bottom halves d8-d15 the prologue saves before the core and the
   epilogue restores after it.  This is the same frame as the internal spines',
   which list all of Q0-Q31: the two are equal, so stating the shorter one
   weakens nothing, and the proofs rewrite it back to the spines' form. *)
let WB_SUBSUMED_ANTISYM = prove
 (`!(R:A->B->bool) S. R subsumed S /\ S subsumed R ==> R = S`,
  REWRITE_TAC[subsumed; FUN_EQ_THM] THEN MESON_TAC[]);;

let WB_CORE_FRAME_EQ = prove
 (`!stackpointer out_p tag_p ivec_p nblk.
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE
      [memory :> bytes (out_p,16 * nblk); memory :> bytes (tag_p,16);
       memory :> bytes (ivec_p,16);
       memory :> bytes (word_add stackpointer (word 64),16)] ,,
      MAYCHANGE
      [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14;
       Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27;
       Q28; Q29; Q30; Q31]) =
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE
      [memory :> bytes (out_p,16 * nblk); memory :> bytes (tag_p,16);
       memory :> bytes (ivec_p,16);
       memory :> bytes (word_add stackpointer (word 64),16)] ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15])`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WB_SUBSUMED_ANTISYM THEN CONJ_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  SUBSUMED_MAYCHANGE_TAC);;

(* ---- quiet stepper: the default one logs a line per state, and these legs
   run several hundred steps each ---- *)
let ARM_QSTEP_TAC th s =
  ARM_STEP_TAC th [] s None (K STRIP_TAC) THEN DISCARD_OLDSTATE_TAC s THEN CLARIFY_TAC;;

let ARM_QSTEPS_TAC th snums = MAP_EVERY (ARM_QSTEP_TAC th) (statenames "s" snums);;

(* ---- general affine word_sub cancellation (no WORD_BLAST) ----
   For a `word_sub P Q` subterm whose only free int64 variable is a single
   register base x (in_p, out_p, ...), the difference P - Q does not depend on
   x: prove `word_sub P Q = word_sub P[x:=0] Q[x:=0]` by WORD_RULE (the
   x-dependence cancels), then reduce the right side to a numeral `word k` by
   WORD_REDUCE_CONV. *)
let affine_cancel_thm t =
  match t with
  | Comb(Comb(Const("word_sub",_),_),_) ->
    let fv = filter (fun v -> type_of v = `:int64` && is_var v) (frees t) in
    (match fv with
     | [x] ->
       let t0 = subst [`word 0:int64`, x] t in
       let step1 = WORD_RULE (mk_eq(t, t0)) in
       (* |- word_sub P Q = word k *)
       CONV_RULE (RAND_CONV WORD_REDUCE_CONV) step1
     | _ -> failwith "affine_cancel_thm: not exactly one int64 var")
  | _ -> failwith "affine_cancel_thm: not word_sub";;

(* Collect every affine word_sub in the goal and the assumptions, cancel it,
   rewrite the assumptions with the results, then reduce the now concrete PC
   if-condition. *)
let WB_TAIL_RESOLVE_TAC : tactic = fun (asl,w) ->
  let is_sub tm = match tm with
    | Comb(Comb(Const("word_sub",_),_),_) ->
        length (filter (fun v -> type_of v = `:int64` && is_var v) (frees tm)) = 1
    | _ -> false in
  let all = itlist (fun (_,th) acc -> concl th :: acc) asl [w] in
  let subs = setify (itlist (fun t acc -> find_terms is_sub t @ acc) all []) in
  let cancel_thms = mapfilter affine_cancel_thm subs in
  (RULE_ASSUM_TAC(REWRITE_RULE cancel_thms) THEN
   (* reflexive compares: ival x - ival x and word_sub x x reduce to 0 *)
   RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; WORD_SUB_REFL; VAL_WORD_0; IVAL_WORD_0]) THEN
   RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
   RULE_ASSUM_TAC(CONV_RULE(TRY_CONV INT_REDUCE_CONV)) THEN
   RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_EQ_CONV))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[NOT_CLAUSES; COND_CLAUSES]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[])) (asl,w);;

(* ---- extract (current state index, PC offset) from the goal's PC assumption:
   the offset is n >= 0 for a concrete pc+n (or a bare word n), -2 for a
   symbolic if-term (which needs the resolver), -3 if there is no PC
   assumption. ---- *)
let pc_info (asl,_) =
  try
    let (_,th) = List.find (fun (_,th) -> match concl th with
        | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),_)),_) -> true
        | _ -> false) asl in
    let lhs,rhs = dest_eq (concl th) in
    let st = rand lhs in
    let sidx = (let nm = fst(dest_var st) in
                int_of_string (String.sub nm 1 (String.length nm - 1))) in
    let off = (match rhs with
      | Comb(Const("word",_),Comb(Comb(Const("+",_),_),n)) -> (try dest_small_numeral n with _ -> -2)
      | Comb(Const("word",_),n) -> (try dest_small_numeral n with _ -> -2)
      | _ -> -2) in
    (sidx, off)
  with _ -> (-1, -3);;

(* ---- the case split shared by the band and residue dispatches: assert
   `x = lo \/ ... \/ x = hi`, proved by side_tac, and leave the cases in order.
   BOUNDS_ARITH_TAC proves such a disjunction from the named bounds alone,
   without the rest of a leg's context. ---- *)
let WB_CASES_TAC x (lo,hi) side_tac =
  let disj = end_itlist (fun a b -> mk_disj(a,b))
     (map (fun k -> mk_eq(x, mk_small_numeral k)) (lo--hi)) in
  SUBGOAL_THEN disj MP_TAC THENL [side_tac; ALL_TAC] THEN STRIP_TAC;;

let BOUNDS_ARITH_TAC bnds =
  MAP_EVERY (MP_TAC o ASSUME) bnds THEN POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

(* ---- reusable safety back-legs, from the compare just before the correctness
   proof's q_at seam.  There X5 is the public residual byte count; the theorem
   executes the compare and the initial ciphertext and H^8 loads itself, so its
   interface carries no condition-code assumptions.  From here the trace
   depends only on the public addresses and the fixed residual block count; all
   SIMD and data values may stay unconstrained.

   Each residual tail is proved once, against the caller's whole-buffer bounds.
   The selected witnesses below are closed choice terms, so all three consumers
   (5..8, 9..16 and >=17) reuse them without an existential witness escaping
   its scope. ---- *)
let WB_SAFETY_BYTES_LEN = prove
 (`!nblk.
      128 * nblk < 2 EXP 64
      ==> val (word (128 * nblk):int64) DIV 8 * 1 = 16 * nblk`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  MP_TAC(SPECL [`8`; `16 * nblk`] DIV_MULT) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* The val-free twin of the above, needed on the >=17 leg only.
   WB_SAFETY_BYTES_LEN matches `val (word (128*nblk)) DIV 8 * 1`, but by the
   time the >=17 residue reaches its events discharge the goal's bound is
   already spelled `(128 * nblk) DIV 8 * 1`: CORE_SAFE_OPEN_TAC asserts
   `val (word (128*nblk)) = 128*nblk` into the assumptions, and
   WB_TAIL_POST_ASM_REWRITE_TAC (which rewrites with every `val`-headed
   assumption) consumes the `val (word ...)` wrapper on the goal side.  The
   assumption side, stripped straight off the reusable tail theorem, keeps the
   val spelling.  So WB_SAFETY_BYTES_LEN cannot fire on the goal, and the two
   sides end up as `(128*nblk) DIV 8 * 1` and `16*nblk`.  This rule closes that
   gap.  It needs no size side condition: with the word wrapper gone it is pure
   natural-number arithmetic, which is also why it is safe to keep
   unconditionally in the rewrite set.  The 9..16 bands never need it (nblk is
   a numeral there, so NUM_REDUCE collapses the bound outright). *)
let WB_SAFETY_BYTES_LEN_NOVAL = prove
 (`!nblk. (128 * nblk) DIV 8 * 1 = 16 * nblk`,
  GEN_TAC THEN
  MP_TAC(SPECL [`8`; `16 * nblk`] DIV_MULT) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* memaccess_inbounds distributes over a loop trace: if every iteration's own
   trace is in bounds, so is the concatenation ENUMERATEL builds.  Needed on
   the >=17 leg only, whose scaffold keeps the loop body symbolic in `i`; the
   legs for nblk <= 16 do not run the loop and produce no ENUMERATEL goal.  The
   stock DISCHARGE_MEMACCESS_INBOUNDS_TAC (common/consttime.ml) splits traces
   with MEMACCESS_INBOUNDS_APPEND (common/safety.ml) but has no ENUMERATEL
   rule, so a quantified loop trace matches none of its cases. *)
let MEMACCESS_INBOUNDS_ENUMERATEL = prove
 (`!n (f:num->((N)address_uarch_event)list) rr ww.
     (!i. i < n ==> memaccess_inbounds (f i) rr ww)
     ==> memaccess_inbounds (ENUMERATEL n f) rr ww`,
  INDUCT_TAC THEN REWRITE_TAC[ENUMERATEL] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[memaccess_inbounds_def; ALL];
    REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LT] THEN
      DISCH_THEN MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let WB_CONTAINED_REFL = prove
 (`!(x:N word) n. contained (x,n) (x,n)`,
  REWRITE_TAC[CONTAINED] THEN MESON_TAC[]);;

let WB_FIRST_NONOVERLAPPING_TAC : tactic = fun (asl,w) ->
  try FIRST_ASSUM ACCEPT_TAC (asl,w)
  with Failure _ ->
    (ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
     FIRST_ASSUM ACCEPT_TAC) (asl,w);;

(* DISCHARGE_SAFETY_PROPERTY_TAC with its closing memaccess_inbounds tactic
   replaced by meminb_tac: the shape of DISCHARGE_SAFE_ROBUST
   (aes_gcm_common.ml). *)
let WB_SAFETY_PROPERTY_TAC (meminb_tac:tactic) : tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W (fun (asl,w) ->
    (if is_conj w then
       CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
     else ALL_TAC) THEN
    meminb_tac);;

(* The accumulated event trace of state st: the right side of its
   `read events st` assumption. *)
let events_of_state asl st =
  rhs(concl(snd(find (fun (_,th) ->
    let c = concl th in
    is_eq c &&
    (try rator(lhs c) = `read events` && rand(lhs c) = st with _ -> false))
    asl)));;

(* These back-legs already finish at the enclosing safety theorem's final PC.
   Consume their ensures theorem directly instead of passing it through
   ARM_BIGSTEP_TAC: the latter needlessly rebuilds the whole state update and
   can fail while absorbing the nested MAYCHANGE relation. *)
let FINAL_TAIL_ENSURES = prove
 (`!step (P:S->bool) Q C Q' C' s.
      P s /\
      ensures step P Q C /\
      C subsumed C' /\
      (!s'. Q s' ==> Q' s')
      ==> eventually step (\s'. Q' s' /\ C' s s') s`,
  REWRITE_TAC[ensures; subsumed] THEN
  MESON_TAC[EVENTUALLY_MONO]);;

(* When the tail starts after a simulated prefix, compose its frame with the
   enclosing frame from the original state instead of rebasing that frame at
   the tail state.

   COMPOSE_FRAME_LEMMA is split out so that MESON only ever sees the frame
   composition.  Handed the whole composed statement instead, MESON diverges:
   the `seq` existential multiplies with `eventually`'s own quantifier. *)
let COMPOSE_FRAME_LEMMA = prove
 (`(C' ,, C) subsumed C' ==> C' s0 s /\ C s s' ==> C' s0 s'`,
  REWRITE_TAC[subsumed; seq] THEN MESON_TAC[]);;

let FINAL_COMPOSED_TAIL_ENSURES = prove
 (`!step (P:S->bool) Q C Q' C' s0 s.
      C' s0 s /\
      P s /\
      ensures step P Q C /\
      (C' ,, C) subsumed C' /\
      (!s'. Q s' ==> Q' s')
      ==> eventually step (\s'. Q' s' /\ C' s0 s') s`,
  REWRITE_TAC[ensures] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME `(P:S->bool) s`))) THEN
  MATCH_MP_TAC(REWRITE_RULE[GSYM RIGHT_FORALL_IMP_THM] EVENTUALLY_MONO) THEN
  BETA_TAC THEN X_GEN_TAC `t:S` THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP COMPOSE_FRAME_LEMMA o
                  check (fun th -> is_binary "subsumed" (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

(* Consume a tail theorem, discharged from the goal, through one of the two
   finishing lemmas above: front closes the lemma's conjuncts that precede the
   tail's own ensures, which is then the tail theorem, followed by its frame
   and, by post_tac, the enclosing postcondition. *)
let CONSUME_WB_TAIL_TAC lemma (front:tactic list) post_tac : tactic =
  DISCH_THEN(fun tailth ->
    let _,args = strip_comb(concl tailth) in
    let tail_pre = el 1 args
    and tail_post = el 2 args
    and tail_frame = el 3 args in
    MATCH_MP_TAC lemma THEN
    MAP_EVERY EXISTS_TAC [tail_pre; tail_post; tail_frame] THEN
    REPEAT CONJ_TAC THENL
     (front @
      [ACCEPT_TAC tailth;
       REWRITE_TAC[ETA_AX; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                   MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS;
                   MODIFIABLE_UPPER_SIMD_REGS] THEN
       SUBSUMED_MAYCHANGE_TAC;
       post_tac]));;

let USE_WB_TAIL_SAFE_TAC =
  CONSUME_WB_TAIL_TAC FINAL_TAIL_ENSURES [BETA_TAC THEN ASM_REWRITE_TAC[]];;

let USE_WB_COMPOSED_TAIL_SAFE_TAC =
  CONSUME_WB_TAIL_TAC FINAL_COMPOSED_TAIL_ENSURES
   [MONOTONE_MAYCHANGE_TAC;
    (* On legs whose tail is entered after a long symbolic front, the front can
       leave the leftover-byte count in X5 as the unreduced difference
       `word_sub (in_p + 16*nblk) (in_p + 128*k)`; the blanket rewrite then
       closes 9 of the 10 precondition conjuncts and leaves that word equation,
       which WORD_RULE finishes.  Where X5 is already reduced nothing is left,
       hence TRY. *)
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN TRY(CONV_TAC WORD_RULE)];;

(* ---- net-safe rewriting for the composed tails.  On the 9..16 and >=17 legs,
   which reach their tail after a long symbolic front, the assumption list
   carries that front's per-state reads plus front_916_setup_tac's asserted
   USHR, AND-mask and DIVISION identities, among which are cyclic equation
   pairs.  A rewrite net (REWRITE_TAC, ASM_SIMP_TAC, any TOP_DEPTH traversal)
   re-descends into its own output and diverges on such a pair, overflowing the
   stack ("looping recursion?"); narrowing the assumption set alone does not
   prevent it.  A single ONCE_DEPTH pass rewrites every redex at most once and
   cannot cycle, so WB_BOUNDED_REWRITE_CONV ths k repeats such passes only
   while the term keeps changing, and at most k times.

   wb_tail_rewrite_asms selects the assumptions a composed tail's goal can use.
   That goal mentions only the freshly generalized final state and the event
   list, so only three kinds of assumption can contribute: variable definitions
   (the stripped `e2 = f_events ...`), reads of a state the goal still
   mentions, and the `val (word ...)` size facts the enclosing spec's buffer
   bounds are phrased over.  The rest are dropped, not discharged. ---- *)
let WB_BOUNDED_REWRITE_CONV ths k tm =
  let conv = GEN_REWRITE_CONV ONCE_DEPTH_CONV ths in
  let rec go k tm =
    if k <= 0 then REFL tm else
    let th = try conv tm with Failure _ -> REFL tm in
    let tm' = rhs(concl th) in
    if tm' = tm then th else TRANS th (go (k-1) tm') in
  go k tm;;

let wb_tail_rewrite_asms (asl,w) =
  let gvars = frees w in
  let usable th =
    let c = concl th in
    is_eq c &&
    (let l = lhs c in
     is_var l ||
     (match strip_comb l with
      | Const("read",_), [_; st] -> mem st gvars
      | Const("val",_), _ -> true
      | _ -> false)) in
  map snd (filter (usable o snd) asl);;

(* Targeted stand-in for the blanket ASM_REWRITE_TAC[] at the head of a
   composed tail's post-tactic, which overflows on the 9..16 and >=17 legs
   (unlike the 5..8 legs, whose tail starts at s0); ASM_SIMP_TAC is no better,
   having the same assumption set and the same net.  The trailing REWRITE_TAC[]
   closes the trivial conjuncts a blanket call would. *)
let WB_TAIL_POST_ASM_REWRITE_TAC : tactic = fun (asl,w) ->
  (CONV_TAC (WB_BOUNDED_REWRITE_CONV (wb_tail_rewrite_asms (asl,w)) 12) THEN
   REWRITE_TAC[]) (asl,w);;

(* After MEMACCESS_INBOUNDS_APPEND splits the trace, the first conjunct is the
   reusable tail theorem's own `memaccess_inbounds` postcondition, which is
   already an assumption, so it needs matching, not search.  A blanket
   ASM_MESON_TAC[] is handed every assumption instead and diverges on the 9..16
   and >=17 legs.  Trying the two assumption-matching tactics first closes that
   case at once and never reaches MESON.  The fallback is the unrestricted
   ASM_MESON_TAC[]: on the 5..8 legs this conjunct needs facts beyond the
   inbounds assumptions.

   Plain matching is still not enough on the 9..16 and >=17 legs, because the
   two sides spell the same buffer bound differently.  mk_tail_safe_goal states
   the tail's postcondition over `val (word (128 * nblk):int64) DIV 8 * 1`, and
   prove_tail_safe SUBST_ALL_TACs that to `16 * nblk` only inside its own
   proof, so the exported theorem keeps the `val` spelling.  The enclosing band
   closers then run `RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV)` and
   `CONV_TAC NUM_REDUCE_CONV` over a leg where nblk is already a numeral, which
   collapses one side to a literal (`144` at band 9) while the other keeps the
   `val (word ...) DIV 8 * 1` form.  The 5..8 legs never diverge this way
   because they specialize the tail at s0 with no intervening reduction.  So
   normalize both sides to the same spelling and try the match again;
   equality-shaped goals and the legs the plain matches close are untouched,
   because the plain matches are tried first.

   The decisive normalizer is APPEND_NIL.  Both sides carry the tail's selector
   `(@f_events. ...) in_p key_p ... stackpointer`, the goal's copy inside a
   `memaccess_inbounds` argument, the assumption's as the `e2 = ...`
   definition.  But RESHAPE_LOOP_TAC leaves the goal's copy with
   `APPEND (APPEND [...] []) []` wrappers around the range lists inside the
   epsilon's body, where the assumption's copy has the bare lists.  Two epsilon
   terms whose bodies differ at all are different terms, so `e2` never rewrites
   and the conjunct cannot match however the bounds are spelled.  APPEND_NIL
   collapses the wrappers and the two selectors become alpha-equal.

   WB_SAFETY_BYTES_LEN and the `val` size facts also reconcile the buffer
   bounds, spelled `val (word 1152) DIV 8 * 1` in the assumption against the
   literal `144` in the goal.  WB_SAFETY_BYTES_LEN is the rule prove_tail_safe
   itself uses for this bound; it matters on the >=17 leg, where nblk stays
   symbolic and the `val` facts alone would leave `(128 * nblk) DIV 8 * 1`
   needing symbolic arithmetic that neither NUM_REDUCE nor MESON closes. *)
let WB_TAIL_EVENTS_DISCHARGE_TAC : tactic = fun (asl,w) ->
  let bytelen =
    mapfilter (fun (_,th) -> MATCH_MP WB_SAFETY_BYTES_LEN th) asl in
  let valfacts = map snd (filter (fun (_,th) ->
      let c = concl th in
      is_eq c &&
      (match strip_comb(lhs c) with
       | Const("val",_),_ -> true
       (* the stripped `e2 = f_events ...` definition.  Without it the
          assumption keeps the bare variable `e2` where the goal has the
          selector it stands for, so the two can never converge, however the
          rest is normalized. *)
       | _ -> is_var(lhs c))) asl) in
  (* WB_SAFETY_BYTES_LEN_NOVAL is unconditional, so it is prepended rather than
     derived from an assumption: on the >=17 leg the goal's bound has already
     lost its `val (word ...)` wrapper, so WB_SAFETY_BYTES_LEN cannot reach it
     (see that lemma's comment). *)
  let rules = WB_SAFETY_BYTES_LEN_NOVAL :: bytelen @ valfacts in
  (* APPEND_NIL gets a full TOP_DEPTH traversal: the wrappers are nested two
     deep (`APPEND (APPEND l []) []`) and a single ONCE_DEPTH pass strips only
     the outer one.  This cannot cycle, because the right side of APPEND_NIL is
     a strict subterm.  The assumption-derived rules get the bounded passes of
     WB_BOUNDED_REWRITE_CONV instead: TOP_DEPTH would diverge on the cyclic
     pairs described there, and a single ONCE_DEPTH pass does not reach the
     bounds, which sit inside the epsilon's body below the first redex.

     The APPEND_NIL pass runs both before and after the rule expansion.  The
     goal's wrappers are there from the start, but on the assumption side the
     trace is still the bare variable `e2`, and its wrappers only appear once
     the `e2 = <selector>` definition has been rewritten in.  With the leading
     pass alone the two sides would end as epsilon terms whose bodies differ by
     `APPEND (APPEND [...] []) []`, and the goal would fall through to the
     diverging ASM_MESON_TAC[].  On the 5..8 and 9..16 legs nblk is a numeral,
     their bounds have already converged, and the trailing pass changes
     nothing. *)
  let append_nil_pass = TRY_CONV(GEN_REWRITE_CONV TOP_DEPTH_CONV [APPEND_NIL]) in
  let nconv =
    append_nil_pass THENC
    (if rules = [] then ALL_CONV else WB_BOUNDED_REWRITE_CONV rules 12) THENC
    append_nil_pass THENC
    TRY_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV) in
  let match_with f =
    FIRST_ASSUM (fun th -> ACCEPT_TAC(f th)) ORELSE
    FIRST_ASSUM (fun th -> MATCH_ACCEPT_TAC(f th)) in
  (match_with I ORELSE
   match_with (CONV_RULE nconv) ORELSE
   (CONV_TAC nconv THEN (match_with I ORELSE match_with (CONV_RULE nconv))) ORELSE
   ASM_MESON_TAC[]) (asl,w);;

(* Local, net-safe shadow of the stock DISCHARGE_MEMACCESS_INBOUNDS_TAC
   (common/consttime.ml), for the second conjunct below.

   The stock tactic overflows the stack ("looping recursion?") on the 9..16 and
   >=17 legs.  Its one blanket call is the ASM_REWRITE_TAC[] inside
   DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC, whose job is only to expand the
   stripped `e2 = f_events ...` definition so that the undischarged assumption
   and the goal take the same shape.  It is the failure mode described at
   WB_BOUNDED_REWRITE_CONV, and the remedy is the same: bound the traversal
   rather than narrow the fact set (the overflow needs the cycle to be
   reachable from the goal).

   On the shapes the stock tactic does close (identical-term match, range
   widening, concrete goal, and APPEND-split with and without `e2` defined) the
   shadow agrees with it exactly, so the 5..8 legs take the same path.

   The code is the stock tactic apart from that one call, a recursion cap on
   main_tac, which turns a non-shrinking trace into a Failure the enclosing
   ORELSE can act on instead of an exhausted OCaml stack, and the two dispatch
   cases described below.

   The bounded traversal is made of the same single ONCE_DEPTH passes as
   WB_BOUNDED_REWRITE_CONV, repeated because the shapes needing normalization
   sit below the first redex, inside the tail selector's epsilon body.  But
   here the repetition stops when a term repeats, not only when it stops
   changing: an oscillating equation pair flips the term on every pass, so a
   stabilization test alone never fires and the conjunct is left unprovable. *)
let WB_BOUNDED_ASM_REWRITE_TAC (extra:thm list) : tactic = fun (asl,w) ->
  let rules = extra @ wb_tail_rewrite_asms (asl,w) in
  let conv = GEN_REWRITE_CONV ONCE_DEPTH_CONV rules in
  let rec go seen k tm =
    if k <= 0 then REFL tm else
    let th = try conv tm with Failure _ -> REFL tm in
    let tm' = rhs(concl th) in
    if tm' = tm || exists (fun t -> t = tm') seen then REFL tm
    else TRANS th (go (tm::seen) (k-1) tm') in
  (CONV_TAC (go [] 12) THEN REWRITE_TAC extra) (asl,w);;

let WB_DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC:tactic =
  let try_discharge (meminb_th:thm):tactic =
    UNDISCH_TAC (concl meminb_th) THEN
    WB_BOUNDED_ASM_REWRITE_TAC [] THEN
    REWRITE_TAC[APPEND;APPEND_NIL] THEN
    ((MATCH_MP_TAC MEMACCESS_INBOUNDS_MEM THEN
      REWRITE_TAC[ALL;MEM] THEN NO_TAC) ORELSE
     (MATCH_MP_TAC MEMACCESS_INBOUNDS_CONTAINED THEN
      DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC)) in
  W (fun (asl,w) ->
    let meminbounds = map snd (filter (fun (_,th) ->
          let cth = concl th in
          is_comb cth &&
          name_of (fst (strip_comb cth)) = "memaccess_inbounds") asl) in
    if meminbounds = [] then
      failwith "No memaccess_inbounds assumption" else
    end_itlist (fun tac1 tac2 -> tac1 ORELSE tac2)
      (map try_discharge meminbounds));;

let WB_DISCHARGE_MEMACCESS_INBOUNDS_TAC =
  let append_nil_th =
      MESON[APPEND]
        `memaccess_inbounds (APPEND [] b) = memaccess_inbounds b /\
         memaccess_inbounds (APPEND (APPEND [] []) b) = memaccess_inbounds b` in
  let rec main_tac d (asl,w) =
    if d <= 0 then failwith "WB_DISCHARGE_MEMACCESS_INBOUNDS_TAC: depth" else
    ((WB_DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC) ORELSE

    (DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC) ORELSE

    (REWRITE_TAC[CONJUNCT2 APPEND] THEN
      CONV_TAC ((RATOR_CONV o RATOR_CONV o RAND_CONV) CONS_TO_APPEND_CONV) THEN
      GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
      CONJ_TAC THENL [
        DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC;
        REWRITE_TAC[append_nil_th] THEN main_tac (d-1) THEN NO_TAC
      ]) ORELSE

    (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
      CONJ_TAC THENL [
        main_tac (d-1) THEN NO_TAC;
        DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC;
      ]) ORELSE

    (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
      CONJ_TAC THENL [
        WB_DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC;
        main_tac (d-1);
      ] THEN NO_TAC)) (asl,w)
  in
  (* Two dispatch cases main_tac does not have, both reached only by the >=17
     leg and no-ops on every shape the 5..8 and 9..16 legs present.

     (1) REPEAT CONJ_TAC.  main_tac dispatches on `memaccess_inbounds` heads
     and on MEMACCESS_INBOUNDS_APPEND, so a top-level `/\` matches nothing at
     all and the whole tactic reports "could not identify the pattern".  The
     >=17 leg gets one because its scaffold entry is
     `APPEND residue (APPEND (ENUMERATEL ..) front)`:
     DISCHARGE_WB_COMPOSED_TAIL_TAC's REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND]
     then distributes all the way down and hands this call a five-way
     conjunction.  The bands 9..16 enter the scaffold at a bare f_ev_k with no
     APPEND, so their goal stays a single memaccess_inbounds term and REPEAT
     CONJ_TAC is a no-op there.

     (2) The ENUMERATEL rule.  Of those five conjuncts four are concrete traces
     that main_tac already closes; the fifth is the symbolic loop trace, and it
     needs the quantified-i step before the per-iteration body, which main_tac
     then closes by its ordinary assumption route, since the body's stores are
     already covered by the tail theorem's own inbounds assumption. *)
  let close_one =
    main_tac 8 ORELSE
    (MATCH_MP_TAC MEMACCESS_INBOUNDS_ENUMERATEL THEN
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN main_tac 8) ORELSE
    FAIL_TAC
      "WB_DISCHARGE_MEMACCESS_INBOUNDS_TAC could not identify the pattern" in
  REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL] THEN
  REPEAT CONJ_TAC THEN close_one;;

let DISCHARGE_WB_COMPOSED_TAIL_TAC =
  WB_SAFETY_PROPERTY_TAC
   (REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
    CONJ_TAC THENL
     [WB_TAIL_EVENTS_DISCHARGE_TAC;
      WB_DISCHARGE_MEMACCESS_INBOUNDS_TAC]);;

(* ---- the event-trace scaffold of the core, one branch per leg.  On the >=17
   leg the trace is already in ENSURES_EVENTS_WHILE_UP2 shape,
     e2 = APPEND <residue ladder>
                 (APPEND (ENUMERATEL ((nblk-9) DIV 8) f_ev_loop) f_ev_front),
   so the residue ladder lands in the rule's discarded e_back.  The ladder has
   its own metavariable for each of the eight values of (nblk-9) MOD 8: HOL
   metavariables are shared across the goal stack, so a single shared one would
   be fixed by whichever residue closed first. ---- *)

let core_scaffold =
 `\(in_p:int64) (key_p:int64) (htable_p:int64) (out_p:int64) (tag_p:int64)
   (ivec_p:int64) (nblk:num) (pc:num) (stackpointer:int64).
     if nblk = 1 then f_ev_1 in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer
     else if nblk = 2 then f_ev_2 in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer
     else if nblk = 3 then f_ev_3 in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer
     else if nblk = 4 then f_ev_4 in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer
     else if nblk <= 8 then
       APPEND
         ((if nblk = 5 then f_ev_5
           else if nblk = 6 then f_ev_6
           else if nblk = 7 then f_ev_7
           else f_ev_8) in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer)
         (f_ev_58_front in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer)
     else if nblk = 9 then f_ev_9 in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer
     else if nblk = 10 then f_ev_10 in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer
     else if nblk = 11 then f_ev_11 in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer
     else if nblk = 12 then f_ev_12 in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer
     else if nblk = 13 then f_ev_13 in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer
     else if nblk = 14 then f_ev_14 in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer
     else if nblk = 15 then f_ev_15 in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer
     else if nblk = 16 then f_ev_16 in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer
     else
       APPEND
         ((if (nblk - 9) MOD 8 = 0 then f_ev_t0
           else if (nblk - 9) MOD 8 = 1 then f_ev_t1
           else if (nblk - 9) MOD 8 = 2 then f_ev_t2
           else if (nblk - 9) MOD 8 = 3 then f_ev_t3
           else if (nblk - 9) MOD 8 = 4 then f_ev_t4
           else if (nblk - 9) MOD 8 = 5 then f_ev_t5
           else if (nblk - 9) MOD 8 = 6 then f_ev_t6
           else f_ev_t7) in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer)
         (APPEND
           (ENUMERATEL ((nblk - 9) DIV 8)
             (\i. f_ev_loop in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer i))
           (f_ev_front in_p key_p htable_p out_p tag_p ivec_p nblk pc stackpointer))
     :(uarch_event)list`;;

(* ---- >=17 entry prep: establish the bounds and collapse the 16-way ladder to
   its else-branch.  The rewrite discharges each `~(nblk = k)` from the
   `17 <= nblk` already present and leaves no hypotheses behind; sixteen
   asserted `~(nblk = k)` hypotheses would instead be walked at every
   simulation step and again by DISCHARGE_SAFETY_PROPERTY_TAC over the whole
   trace. ---- *)
let GE17_LADDER_KILL_TAC : tactic = fun (asl,w) ->
  let neq = map (fun k ->
    EQF_INTRO (UNDISCH (ARITH_RULE
      (mk_imp(`17 <= nblk`, mk_neg(mk_eq(`nblk:num`, mk_small_numeral k))))))) (1--16) in
  let nle8 = EQF_INTRO
    (UNDISCH (ARITH_RULE `17 <= nblk ==> ~(nblk <= 8)`)) in
  (GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV)
      (COND_CLAUSES::nle8::neq) THEN
   REWRITE_TAC (nle8::neq)) (asl,w);;

let GE17_PREP_TAC =
  SUBGOAL_THEN `17 <= nblk /\ 9 <= nblk` STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `~(nblk <= 16)`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  GE17_LADDER_KILL_TAC;;

(* ---- reshape the collapsed trace for SEQUENCE:
     APPEND ladder (APPEND loop front)
       -> APPEND (APPEND ladder (APPEND loop [])) front,
   so that SEQUENCE at the loop head peels `e_front_tail = front` and
   `e_back = APPEND ladder (APPEND loop [])`.  ONCE_REWRITE_TAC is used because
   GEN_REWRITE_TAC with a RAND o ONCE_DEPTH path does not reach the intended
   APPEND occurrence. ---- *)
let RESHAPE_LOOP_TAC : tactic = fun (asl,w) ->
  let e2var = `e2:(uarch_event)list` in
  let e2eq = find_term (fun t -> is_eq t && lhs t = e2var
                 && (match rhs t with Comb(Comb(Const("APPEND",_),_),_) -> true | _ -> false)) w in
  let rhs_e2 = rhs e2eq in
  let a,bb,c = (match rhs_e2 with
     | Comb(Comb(Const("APPEND",_),a),Comb(Comb(Const("APPEND",_),bb),c)) -> a,bb,c
     | _ -> failwith "RESHAPE_LOOP_TAC: unexpected e2 shape") in
  let nil = `[]:(uarch_event)list` in
  let ap x y = mk_binop `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list` x y in
  let reshaped = ap (ap a (ap bb nil)) c in
  let reshape_thm = prove(mk_eq(rhs_e2, reshaped), REWRITE_TAC[APPEND_NIL; APPEND_ASSOC]) in
  ONCE_REWRITE_TAC[reshape_thm] (asl,w);;

(* Collapse the first four concrete leaves of core_scaffold and expose the
   APPEND shared by the bands 5..8 without first making nblk concrete. *)
let LE8_58_LADDER_OPEN_TAC : tactic = fun (asl,w) ->
  let neq = map (fun k ->
    EQF_INTRO (UNDISCH (ARITH_RULE
      (mk_imp(`5 <= nblk`, mk_neg(mk_eq(`nblk:num`, mk_small_numeral k))))))) (1--4) in
  (GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV)
      (COND_CLAUSES::(ASSUME `nblk <= 8`)::neq) THEN
   REWRITE_TAC neq) (asl,w);;

(* G0: the count is nonzero *)
let GE17_COUNT_TAC =
  MP_TAC(ASSUME `17 <= nblk`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN ARITH_TAC;;

(* G1, entry (i = 0): the precondition is the postcondition after normalizing
   0+1, 128*1, ENUMERATEL 0, APPEND [] and *1 *)
let GE17_ENTRY_TAC =
  ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ENUMERATEL; APPEND; ADD_CLAUSES; MULT_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_exists (concl th))) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES];;

let x0norm_i = WORD_RULE
  `word_add (word_add in_p (word (128 * (i + 1)))) (word 128):int64 = word_add in_p (word (128 * (i + 2)))`;;

let pcbridge_i = MP WBN_PC_BRIDGE (ASSUME `9 <= nblk`);;

(* ---- G3, the exit and tail leg, pc+2572 to pc+4508: the straight-line
   prepretail to pc+3812, then the 8-way dispatch on the leftover block count
   (nblk-9) MOD 8. ---- *)

(* the leftover-byte count in X5 at the tail compare, under 17 <= nblk and the
   pointer bound *)
let TAIL_LEFTOVER_BYTES = prove
  (`17 <= nblk /\ val (in_p:int64) + 16 * nblk < 2 EXP 63
     ==> word_sub (word_add in_p (word (16 * nblk)))
                  (word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1))))
         = word (16 * ((nblk - 9) MOD 8 + 1)):int64`,
   STRIP_TAC THEN
   SUBGOAL_THEN `16 * nblk = 128 * ((nblk - 9) DIV 8 + 1) + 16 * ((nblk - 9) MOD 8 + 1)` ASSUME_TAC THENL
    [MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
     MP_TAC(ASSUME `17 <= nblk`) THEN ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE);;

(* ---- the core safety opening.  Unlike a `\s s'. true` frame, this one
   unfolds MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI up front so that
   ENSURES_FINAL_STATE_TAC can discharge the real frame at every leaf; the
   wrapper needs the real frame, because it simulates the epilogue after the
   core big-step and so needs aligned_bytes_loaded preserved across it.
   Mirrors BIGNUM_INV_P25519_SAFE. ---- *)
let CORE_SAFE_OPEN_TAC =
  CONCRETIZE_F_EVENTS_TAC core_scaffold THEN REPEAT META_EXISTS_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REPEAT STRIP_TAC THEN
  VAL_INT64_TAC `16 * nblk` THEN VAL_INT64_TAC `128 * nblk`;;

(* ---- the ABI wrapper.  The stock ARM_ADD_RETURN_STACK_TAC is not used: the
   exported spec quantifies over the C argument len_bits, while the core below
   takes word (128 * nblk) with 1 <= nblk, and the prologue contains the entry
   guard, whose zero and non-multiple-of-128 branches return before the core.
   So the crossing is hand-rolled (ARBITRARY_WRAPPER_SAFE_TAC below). ---- *)

let WB_GUARD_FALLTHROUGH_TAC =
  SUBGOAL_THEN `val (word (128 * nblk):int64) = 128 * nblk` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(128 * nblk = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word_and (word (128 * nblk):int64) (word 127)) = 0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(127:num) = 2 EXP 7 - 1` SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(2:num) EXP 7 = 128` SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[MOD_MULT]; ALL_TAC];;
