(* ========================================================================= *)
(* Shared GCM AES-GCM proof helpers (extracted from 1-block claude_4.7).     *)
(*                                                                           *)
(* This file provides ONLY the helper definitions, lemmas, and tactics that  *)
(* the per-N-block claude_4.7 proofs share.  It does NOT include any         *)
(* machine-code definition or main theorem — those belong in the per-proof  *)
(* file.                                                                     *)
(*                                                                           *)
(* Loading this file is fast (~30 seconds), unlike loading the full 1-block *)
(* proof which takes ~12 minutes due to ARM simulation.                     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/aes.ml";;
needs "arm/proofs/utils/aes.ml";;
needs "arm/proofs/utils/aes256_gcm_block_enc_spec.ml";;
needs "common/ghash_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* WORD_SIMPLE_SUBWORD_CONV compatibility shim.                               *)
(*                                                                           *)
(* HOL commit b9a430b (Dec 2025, in the current checkpoint base) reordered     *)
(* WORD_SIMPLE_SUBWORD_CONV to try the trivial size-match rewrite FIRST and    *)
(* `failwith` in its catch-all, instead of trying the structural word_join /   *)
(* word_insert / word_subword / word_zx cases first and falling back to        *)
(* WORD_SUBWORD_TRIVIAL.  The new conversion no longer collapses the nested    *)
(* word_subword (word_join ...) ... byte-shuffle networks that every GCM GHASH *)
(* closer produces when it expands final_xi, so all the per-band closers (which *)
(* call WORD_SIMPLE_SUBWORD_CONV by name) stop closing.                        *)
(*                                                                           *)
(* Rather than port every closer, we re-bind WORD_SIMPLE_SUBWORD_CONV to the   *)
(* verbatim pre-b9a430b definition here, restoring the term normal form the    *)
(* whole proof was written against.  This is loaded after the ARM model, which *)
(* drives its own simplification through the late-bound `extra_word_CONV` ref  *)
(* (NOT this name), so the symbolic simulator is unaffected.  All supporting   *)
(* theorems exist unchanged in the current base.                              *)
(* ------------------------------------------------------------------------- *)

let WORD_SIMPLE_SUBWORD_COMPAT_CONV =
  let dimarith_conv = DEPTH_CONV(!word_SIZE_CONV ORELSEC NUM_RED_CONV) in
  let dimarith_rule th =
    MP th (EQT_ELIM(dimarith_conv(lhand(concl th))))
  and post_rule =
     CONV_RULE(RAND_CONV(RAND_CONV(BINOP_CONV dimarith_conv)))
  and triv_rule =
     GEN_REWRITE_RULE (RAND_CONV o TRY_CONV) [WORD_DUPLICATE_REFL] in
  let [rules_join; rules_insert; rules_zx; rules_subword; rules_duplicate;
       [rule_duplicate]; [rule_trivial]] =
  map (map (PART_MATCH (lhand o rand)))
   [[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER];
    [WORD_SUBWORD_INSERT_OUTER; WORD_SUBWORD_INSERT_INNER];
    [WORD_SUBWORD_ZX_TRIVIAL; WORD_SUBWORD_ZX];
    [WORD_SUBWORD_SUBWORD]; [WORD_SUBWORD_DUPLICATE];
    [WORD_SUBWORD_DUPLICATE_DUPLICATE];
    [WORD_SUBWORD_TRIVIAL]] in
  fun tm ->
    match tm with
      Comb(Comb(Const("word_subword",_),itm),
           Comb(Comb(Const(",",_),Comb(Const("NUMERAL",_),_)),
                Comb(Const("NUMERAL",_),_))) ->
     (match itm with
        Comb(Comb(Const("word_join",_),_),_) ->
           post_rule(tryfind (fun f -> dimarith_rule(f tm)) rules_join)
      | Comb(Comb(Comb(Const("word_insert",_),_),_),_) ->
           post_rule(tryfind (fun f -> dimarith_rule(f tm)) rules_insert)
      | Comb(Comb(Const("word_subword",_),_),_) ->
           post_rule(tryfind (fun f -> dimarith_rule(f tm)) rules_subword)
      | Comb(Const("word_zx",_),_) ->
           tryfind (fun f -> dimarith_rule(f tm)) rules_zx
      | Comb(Const("word_duplicate",_),_) ->
         (try triv_rule(dimarith_rule(rule_duplicate tm))
          with Failure _ ->
           post_rule(tryfind (fun f -> dimarith_rule(f tm)) rules_duplicate))
      | _ -> dimarith_rule(rule_trivial tm))
    | _ -> failwith "WORD_SIMPLE_SUBWORD_COMPAT_CONV";;

(* Globally restore the pre-b9a430b behaviour for the rest of this proof. *)
let WORD_SIMPLE_SUBWORD_CONV = WORD_SIMPLE_SUBWORD_COMPAT_CONV;;

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

(* ---- Pmul argument-order normalizer -------------------------------------- *)

let PMUL_NORM_CONV tm =
  match tm with
  | Comb(Comb(Const("word_pmul",_), a), b) ->
    if term_order a b then SPECL [a;b] WORD_PMUL_SYM
    else failwith "already normalized"
  | _ -> failwith "not word_pmul";;

(* ---- Assembly-shaped 1-block spec --------------------------------------- *)

let ghash_1block_karatsuba = new_definition
 `ghash_1block_karatsuba (input:int128) (h:int128) (hk:int128) : int128 =
  let a_lo:64 word = word_subword input (0,64) in
  let a_hi:64 word = word_subword input (64,64) in
  let h_lo:64 word = word_subword h (0,64) in
  let h_hi:64 word = word_subword h (64,64) in
  let hk_lo:64 word = word_subword hk (0,64) in
  let pl:int128 = word_pmul a_lo h_hi in
  let ph:int128 = word_pmul a_hi h_lo in
  let pm:int128 = word_pmul (word_xor a_lo a_hi) hk_lo in
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

(* ---- 1-block bridge ------------------------------------------------------ *)

let BYTESWAP128_SUBWORD_LO = prove(
  `!(h:int128). word_subword (byteswap128 h) (0,64):(64)word = word_subword h (64,64)`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let BYTESWAP128_SUBWORD_HI = prove(
  `!(h:int128). word_subword (byteswap128 h) (64,64):(64)word = word_subword h (0,64)`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_XOR_COMM = prove(
  `!(a:(N)word) (b:(N)word) n.
    word_subword (word_xor a (word_xor b c)) n:(M)word =
    word_subword (word_xor a (word_xor c b)) n`,
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT = prove(
  `!(input:int128) (h:int128) (hk:int128).
    word_subword hk (0,64):(64)word = karatsuba_mid h
    ==> ghash_1block_karatsuba input (byteswap128 h) hk =
        word_reversefields 8 (polyval_dot input h)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ghash_1block_karatsuba; LET_DEF; LET_END_DEF;
              BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI;
              REWRITE_RULE[LET_DEF; LET_END_DEF] POLYVAL_DOT_KARATSUBA] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[karatsuba_mid] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR_COMM] THEN
  REWRITE_TAC[WORD_XOR_ASSOC]);;

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

(* WORD_JOIN_SUBWORD_HALVES moved to gcm_aesgcm_standalone_blocks_helper.ml (unused by AES256_GCM_ENCRYPT_CORRECT). *)

(* June-2026 HOL base: the new WORD_SIMPLE_SUBWORD_CONV no longer collapses the
   straddling extraction word_subword (word_join a a) (64,128) (it crosses the
   128-bit join boundary), leaving it wrapped around the REV64 byte shuffle so
   the lane lemmas cannot match.  This lemma rewrites it to the explicit
   half-swap so the byte-level subword extraction can proceed. *)
let WORD_JOIN_SELF_MID = prove(
  `!a:(128)word.
     word_subword (word_join a a:(256)word) (64,128):(128)word =
     word_join (word_subword a (0,64):(64)word) (word_subword a (64,64):(64)word):(128)word`,
  CONV_TAC WORD_BLAST);;

let SIMD_SIMPLIFY_RULES = [REV64_LOWER_LANE; REV64_UPPER_LANE; REV64_128];;

let SIMD_SIMPLIFY_ASSUM_TAC =
  RULE_ASSUM_TAC(fun th ->
    try REWRITE_RULE SIMD_SIMPLIFY_RULES th with _ -> th);;

(* ---- Mask / word simplification lemmas ----------------------------------- *)

let MASK_IS_ONES = prove(
  `!(x:(128)word).
    word_insert (word_insert x (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word =
    (word_not(word 0):(128)word)`, CONV_TAC WORD_BLAST);;
let WORD_AND_MASK = prove(
  `!(x:(128)word) (y:(128)word).
    word_and x (word_insert (word_insert y (0,64) (word 18446744073709551615:(128)word):(128)word)
      (64,64) (word 18446744073709551615:(128)word):(128)word) = x`,
  REWRITE_TAC[MASK_IS_ONES; WORD_AND_NOT0]);;
let WORD_AND_MASK_SYM = prove(
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

(* ---- Per-step cleanup (called after every ARM_STEPS_TAC step) ------------ *)
let GCM_ENC_SIMPLIFY_TAC =
  SIMD_SIMPLIFY_ASSUM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SWAP_HALVES_INVOLUTION;
    WORD_ZX_ALLONES_64_128; WORD_AND_MASK; WORD_AND_MASK_SYM; BIF_MASK;
    WORD_AND_MASK_64; WORD_AND_MASK_SYM_64]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    with _ -> th);;

(* ---- GHASH closure lemmas ------------------------------------------------ *)

let WORD_XOR_0_LEFT = WORD_BITWISE_RULE
  `word_xor (word 0) x = (x:(N)word)`;;

let WORD_INSERT_AS_JOIN_1 = prove(
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

let WORD_INSERT_AS_JOIN_2 = prove(
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

let KAR_SUBWORD_LEMMA = prove(
  `!(xi_rev:(128)word).
    word_subword
      (word_xor xi_rev
        (word_subword (word_join xi_rev xi_rev:(256)word) (64,128)))
      (0,64):(64)word =
    word_xor (word_subword xi_rev (0,64):(64)word)
             (word_subword xi_rev (64,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

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

(* ---- Half-swap lemmas (used by the 3-block only-Q19 fast reduce) ---------- *)
(* When the GHASH accumulator register (Q19) is abbreviated opaque across the
   epilogue ext (the 3-block fast reduce), the final_xi value and the ciphertext
   atoms enter the GHASH closer in half-swapped `word_join` form. These three
   WORD_BLAST identities re-normalize them to the c?lo/c?hi shape the closer
   expects. Centralized here (was inline in the 3-block file). *)

(* Half-swap of `word_join x x` (256-bit) taking the middle 128 bits. *)
(* HALFSWAP_JOIN_SELF moved to gcm_aesgcm_standalone_blocks_helper.ml (unused by AES256_GCM_ENCRYPT_CORRECT). *)

(* reversefields of a half-swapped join = lo/hi-swapped subword of reversefields. *)
let HALFSWAP_REV8_LEMMA = prove
 (`!(x:(128)word).
     (word_subword (word_reversefields 8
        (word_join (word_subword x (0,64):(64)word) (word_subword x (64,64):(64)word):(128)word):(128)word) (0,64):(64)word =
      word_subword (word_reversefields 8 x:(128)word) (64,64):(64)word) /\
     (word_subword (word_reversefields 8
        (word_join (word_subword x (0,64):(64)word) (word_subword x (64,64):(64)word):(128)word):(128)word) (64,64):(64)word =
      word_subword (word_reversefields 8 x:(128)word) (0,64):(64)word)`,
  GEN_TAC THEN CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* A half-swapped join of a word's subwords reconstructs the word. *)
let JOIN_SUBWORD_IDENT = prove
 (`!(x:(128)word).
     word_join (word_subword x (64,64):(64)word) (word_subword x (0,64):(64)word):(128)word = x`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ---- N-block GHASH_POLYVAL_ACC specializations (lengths 2..7) ------------- *)
(* All of GHASH_POLYVAL_ACC_2..7 live here, derived from GHASH_POLYVAL_ACC_2's *)
(* ring-algebra proof and from GHASH_POLYVAL_ACC_BATCHED (both in              *)
(* common/ghash_spec.ml, loaded before this file via `needs`). The per-N      *)
(* proof files reference these rather than redefining them.                   *)

(* ========================================================================= *)
(* 2-block Horner unrolling: ghash_polyval_acc h a [b;c] = prop3(...)        *)
(* Processing 2 GHASH blocks iteratively equals a batched computation:       *)
(*   XOR of 256-bit polynomial multiplications followed by Prop 3 reduction  *)
(* This matches the Loop_mod2x_v8 loop in ghashv8-armx.S                    *)
(* ========================================================================= *)

let GHASH_POLYVAL_ACC_2 = prove
 (`!(h:int128) (a:int128) (b:int128) (c:int128).
    ghash_polyval_acc h a [b; c] =
    polyval_reduce_prop3
      (word_xor (word_pmul (word_xor a b) (polyval_dot h h) : 256 word)
                (word_pmul c h : 256 word))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ghash_polyval_acc] THEN
  MATCH_MP_TAC(ISPEC `128` MOD_POLYVAL_CANCEL_VARPOW) THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
    `ring_add bool_poly
      (ring_mul bool_poly (poly_of_word (polyval_dot (word_xor (a:int128) (b:int128)) (h:int128))) (poly_of_word h))
      (ring_mul bool_poly (poly_of_word (c:int128)) (poly_of_word h))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
    EXISTS_TAC
      `ring_mul bool_poly
        (ring_add bool_poly (poly_of_word (polyval_dot (word_xor (a:int128) (b:int128)) (h:int128))) (poly_of_word (c:int128)))
        (poly_of_word h)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`word_xor (polyval_dot (word_xor (a:int128) (b:int128)) (h:int128)) (c:int128)`; `h:int128`] POLYVAL_DOT_CORRECT) THEN REWRITE_TAC[POLY_OF_WORD_XOR];
      MATCH_MP_TAC MOD_POLYVAL_REFL_GEN THEN
      SIMP_TAC[RING_MUL; RING_ADD; BOOL_POLY_OF_WORD] THEN
      MATCH_MP_TAC(GSYM RING_ADD_RDISTRIB) THEN REWRITE_TAC[BOOL_POLY_OF_WORD]];
    ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
    MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
    EXISTS_TAC
      `ring_add bool_poly
        (ring_mul bool_poly (ring_add bool_poly (poly_of_word (a:int128)) (poly_of_word (b:int128))) (poly_of_word (polyval_dot (h:int128) h)))
        (ring_mul bool_poly (poly_of_word (c:int128)) (poly_of_word h))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`word_xor (word_pmul (word_xor (a:int128) (b:int128)) (polyval_dot (h:int128) h) : 256 word) (word_pmul (c:int128) h : 256 word)`] POLYVAL_REDUCE_PROP3_CORRECT) THEN REWRITE_TAC[POLY_OF_WORD_XOR; POLY_OF_WORD_PMUL_2N];
      MP_TAC(ISPECL
        [`ring_mul bool_poly (ring_add bool_poly (poly_of_word (a:int128)) (poly_of_word (b:int128))) (poly_of_word (polyval_dot (h:int128) h))`;
         `ring_mul bool_poly (poly_of_word (polyval_dot (word_xor (a:int128) (b:int128)) (h:int128))) (poly_of_word h)`;
         `ring_mul bool_poly (poly_of_word (c:int128)) (poly_of_word (h:int128))`;
         `ring_mul bool_poly (poly_of_word (c:int128)) (poly_of_word (h:int128))`] MOD_POLYVAL_ADD) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [REWRITE_TAC[INNER_CONG];
          REWRITE_TAC[MOD_POLYVAL_REFL; RING_MUL; BOOL_POLY_OF_WORD]];
        REWRITE_TAC[]] THEN
      SIMP_TAC[RING_MUL; BOOL_POLY_OF_WORD]]]);;

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
(* GHASH_POLYVAL_ACC_4: 4-block Horner unrolling specialization.            *)
(* Derived directly from GHASH_POLYVAL_ACC_BATCHED for list [p;q;r;s].      *)
(* Unfolds h_power 0..3 to the polyval_dot chain (h, h^2, h^3, h^4).         *)
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

let GHASH_POLYVAL_ACC_7 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128) (u:int128) (z:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t; u; z] =
    polyval_reduce_prop3
      (word_xor (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) : 256 word)
      (word_xor (word_pmul q (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) : 256 word)
      (word_xor (word_pmul r (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
      (word_xor (word_pmul s (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
      (word_xor (word_pmul t (polyval_dot (polyval_dot h h) h) : 256 word)
      (word_xor (word_pmul u (polyval_dot h h) : 256 word)
                (word_pmul z h : 256 word)))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t; u; z]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;

(* ---- Tactics for closing the GHASH subgoal -------------------------------- *)

(* ABBREV_ALL_PMUL_TAC moved to gcm_aesgcm_standalone_blocks_helper.ml (unused by AES256_GCM_ENCRYPT_CORRECT). *)

(* PMUL_ARG_SORT_CONV moved to gcm_aesgcm_standalone_blocks_helper.ml (unused by AES256_GCM_ENCRYPT_CORRECT). *)

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

