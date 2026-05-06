(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)
 
(* =========================================================================  *)
(* NIST SP 800-38D GHASH multiplication                                       *)
(*                                                                            *)
(* Implements Algorithm 1 (Section 6.3) and Algorithm 2 (Section 6.4)         *)
(* exactly as defined in NIST Special Publication 800-38D, November 2007.     *)
(*                                                                            *)
(* The NIST bit convention (polynomial-semantics interpretation): a 128-bit   *)
(* block encodes a polynomial whose highest-degree coefficient (x^127) is    *)
(* NIST bit 0, and whose constant term is NIST bit 127.  In HOL Light's      *)
(* 128-bit word view, this maps:                                             *)
(*   NIST bit i  <-->  HOL Light bit (127 - i)                                *)
(*                                                                            *)
(* Converting from NIST bit numbering to the natural polynomial               *)
(* representation (HOL bit k = coefficient of x^k) is a single full 128-bit   *)
(* reversal: word_reversefields 1 (= bit_reflect128).                         *)
(* =========================================================================  *)

needs "common/ghash_spec.ml";;
needs "arm/proofs/utils/gcm_gmult_v8_spec.ml";;

(* ---- NIST bit-level operations on 128-bit blocks ----------------------- *)

(* NIST bit x_i of block X: under the polynomial-semantics interpretation,
   NIST bit 0 represents the coefficient of x^127 (highest degree) and NIST
   bit 127 represents the constant term. This maps NIST bit i to HOL bit
   (127 - i) — a full 128-bit reversal of bit indices. *)
let nist_bit = new_definition
  `nist_bit (x:int128) (i:num) = bit (127 - i) x`;;

(* NIST LSB_1(V): the rightmost bit = NIST bit 127 = HOL bit 0. *)
let nist_lsb = new_definition
  `nist_lsb (v:int128) = bit 0 v`;;

(* NIST right shift V >> 1: shift the bit string right by one position.
   x_0 x_1 ... x_127  -->  0 x_0 x_1 ... x_126

   Under the new convention (NIST bit i = HOL bit (127 - i)):
   "shift NIST bits right by one" corresponds to "shift HOL bits right by
   one" (NIST position i+1 becomes NIST position i, i.e. HOL bit (127-i-1)
   moves to HOL bit (127-i) — that's `word_ushr` by 1 at the bit level). *)
let nist_shr1 = new_definition
  `nist_shr1 (v:int128) : int128 = word_ushr v 1`;;

(* ---- Algorithm 1: X • Y (Section 6.3) --------------------------------- *)

(* R = 11100001 || 0^120.  Under the new convention where NIST bit i
   corresponds to HOL bit (127 - i), R has NIST bits 0,1,2,7 set, which
   translates to HOL bits 127, 126, 125, 120 set.
   Value: 2^127 + 2^126 + 2^125 + 2^120. *)
let ghash_R = new_definition
  `ghash_R : int128 =
   word (2 EXP 127 + 2 EXP 126 + 2 EXP 125 + 2 EXP 120)`;;

(* The loop body of Algorithm 1.  We count down the remaining steps:
   ghash_mul_loop Z V X 0 = Z   (done, return Z_128)
   ghash_mul_loop Z V X (SUC n) =
     process bit x_i where i = 128 - SUC n, then recurse with n.

   This iterates i = 0, 1, ..., 127 as n counts down from 128 to 0. *)
let ghash_mul_loop = define
  `ghash_mul_loop (z:int128) (v:int128) (x:int128) 0 = z /\
   ghash_mul_loop z v x (SUC n) =
     let i = 128 - SUC n in
     let z' = if nist_bit x i then word_xor z v else z in
     let v' = if nist_lsb v
              then word_xor (nist_shr1 v) ghash_R
              else nist_shr1 v in
     ghash_mul_loop z' v' x n`;;

(* Algorithm 1: X • Y
   Steps:
   1. Let x_0 x_1 ... x_127 denote the bits of X.
   2. Let Z_0 = 0^128 and V_0 = Y.
   3. For i = 0 to 127, compute Z_{i+1} and V_{i+1}.
   4. Return Z_128. *)
let nist_ghash_mul = new_definition
  `nist_ghash_mul (x:int128) (y:int128) : int128 =
   ghash_mul_loop (word 0) y x 128`;;

(* ---- Algorithm 2: GHASH_H(X) (Section 6.4) ----------------------------- *)

(* GHASH_H(X) where X = X_1 || X_2 || ... || X_m:
     Y_0 = 0^128
     For i = 1,...,m: Y_i = (Y_{i-1} XOR X_i) • H
     Return Y_m *)
let nist_ghash_spec = define
  `nist_ghash_spec (h:int128) (acc:int128) [] = acc /\
   nist_ghash_spec h acc (CONS x xs) =
     nist_ghash_spec h (nist_ghash_mul (word_xor acc x) h) xs`;;

(* ========================================================================= *)
(* Bridge A: NIST Algorithm 1 = polynomial multiplication mod P(x)           *)
(*                                                                           *)
(* The NIST shift-and-XOR loop computes the same result as:                  *)
(*   bit_reflect128(ghash_reduce(word_pmul (bit_reflect128 X) (bit_reflect128 Y))) *)
(* where bit_reflect128 = word_reversefields 1 is the full 128-bit           *)
(* bit-reversal that converts between NIST bit ordering and the natural      *)
(* polynomial bit order used by poly_of_word / word_pmul.                    *)
(*                                                                           *)
(* Key insight: NIST "right shift" (V >> 1) = multiplication by the          *)
(* polynomial variable x in GF(2)[x]. In natural bit order (after the full   *)
(* bit-reversal), this is word_shl by 1 (shift towards MSB = higher          *)
(* polynomial degree). The conditional XOR with R implements reduction       *)
(* mod P(x) when the x^127 coefficient overflows into x^128.                 *)
(* ========================================================================= *)

(* Full 128-bit bit reversal: maps NIST bit i to HOL bit i directly.
   This single reversal absorbs the NIST-to-polynomial convention change. *)
let bit_reflect128 = new_definition
  `bit_reflect128 (x:int128) : int128 = word_reversefields 1 x`;;

(* NIST bit i of x = natural bit i of bit_reflect128(x).
   Trivial under the new definitions: both sides are bit (127 - i) x. *)
let NIST_BIT_AS_NATURAL = prove(
  `!x:int128. !i. i < 128 ==>
    (nist_bit x i <=> bit i (bit_reflect128 x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[nist_bit; bit_reflect128; BIT_WORD_REVERSEFIELDS;
              DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DIV_1; MOD_1; MULT_CLAUSES; ADD_0]);;

(* NIST LSB_1(V) = bit 127 of bit_reflect128(V). *)
let NIST_LSB_AS_NATURAL = prove(
  `!v:int128. nist_lsb v <=> bit 127 (bit_reflect128 v)`,
  GEN_TAC THEN
  REWRITE_TAC[nist_lsb; bit_reflect128; BIT_WORD_REVERSEFIELDS; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* R in natural bit order = word 0x87 = x^7 + x^2 + x + 1 = P(x) - x^128.
   Under the new convention where NIST bit i = HOL bit (127-i), ghash_R has
   bits 127,126,125,120 set (NIST bits 0,1,2,7); bit_reflect128 flips to
   bits 0,1,2,7 (= 0x87). *)
let REFLECT_GHASH_R = prove(
  `bit_reflect128 ghash_R = (word 0x87 : int128)`,
  REWRITE_TAC[bit_reflect128; ghash_R] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;

(* ---- NIST_SHR1_BIT: nist_shr1 shifts NIST bits right by 1 -------------- *)

(* This is the core lemma for Bridge A. It says that nist_shr1 does
   exactly what the NIST spec says: bit 0 becomes 0, and bit k becomes
   the old bit k-1. *)
let NIST_SHR1_BIT = prove(
  `!v:int128. !k. k < 128 ==>
    (nist_bit (nist_shr1 v) k <=> if k = 0 then F else nist_bit v (k - 1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[nist_bit; nist_shr1; BIT_WORD_USHR; DIMINDEX_128] THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THENL
   [SIMP_TAC[BIT_TRIVIAL; DIMINDEX_128; ARITH_RULE `128 <= 127 - 0 + 1`];
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

(* ========================================================================= *)
(* Equivalence A: NIST loop ↔ polynomial multiplication in natural bit order *)
(* ========================================================================= *)

(* bit_reflect128 distributes over XOR *)
let REFLECT128_XOR = prove(
  `!a b:int128. bit_reflect128(word_xor a b) =
                word_xor (bit_reflect128 a) (bit_reflect128 b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bit_reflect128] THEN
  CONV_TAC WORD_BLAST);;

(* NIST shr1 in natural order = word_shl by 1 (multiply by x) *)
let NIST_SHR1_AS_SHL = prove(
  `!v:int128. bit_reflect128(nist_shr1 v) =
              word_shl (bit_reflect128 v) 1`,
  GEN_TAC THEN REWRITE_TAC[bit_reflect128; nist_shr1] THEN
  CONV_TAC WORD_BLAST);;

(* V-step: the NIST V-update (shift right + conditional XOR with R) in
   natural polynomial order equals multiply-by-x with reduction mod P(x).
   If bit 127 is set (overflow), XOR with 0x87 = x^7+x^2+x+1 reduces. *)
let NIST_V_UPDATE_AS_POLY_SHL = prove(
  `!v:int128.
    bit_reflect128
      (if nist_lsb v then word_xor (nist_shr1 v) ghash_R else nist_shr1 v) =
    (if bit 127 (bit_reflect128 v)
     then word_xor (word_shl (bit_reflect128 v) 1) (word 0x87)
     else word_shl (bit_reflect128 v) 1)`,
  GEN_TAC THEN REWRITE_TAC[NIST_LSB_AS_NATURAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[REFLECT128_XOR; NIST_SHR1_AS_SHL; REFLECT_GHASH_R];
    REWRITE_TAC[NIST_SHR1_AS_SHL]]);;

(* Z-step: the NIST Z-update (conditional XOR of accumulator Z with V
   when bit x_i is set) commutes with bit_reflect128. In natural polynomial
   order, nist_bit becomes bit, and word_xor is preserved by the reversal. *)
let NIST_Z_UPDATE_AS_POLY_XOR = prove(
  `!z v x:int128. !i. i < 128 ==>
    bit_reflect128
      (if nist_bit x i then word_xor z v else z) =
    (if bit i (bit_reflect128 x)
     then word_xor (bit_reflect128 z) (bit_reflect128 v)
     else bit_reflect128 z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:int128`; `i:num`] NIST_BIT_AS_NATURAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[REFLECT128_XOR]);;

(* ---- Polynomial loop (natural bit order version of Algorithm 1) --------- *)

(* The same loop as ghash_mul_loop but in natural polynomial bit order:
   V-update = word_shl + conditional XOR with 0x87
   Z-update = conditional XOR based on natural bit *)
let poly_mul_loop = define
  `poly_mul_loop (z:int128) (v:int128) (x:int128) 0 = z /\
   poly_mul_loop z v x (SUC n) =
     let i = 128 - SUC n in
     let z' = if bit i x then word_xor z v else z in
     let v' = if bit 127 v
              then word_xor (word_shl v 1) (word 0x87)
              else word_shl v 1 in
     poly_mul_loop z' v' x n`;;

(* ---- NIST_LOOP_AS_POLY_LOOP: bit_reflect128 commutes with the loop ------ *)

(* The NIST loop after bit_reflect128 equals the polynomial loop.
   Proved by induction using NIST_V_UPDATE_AS_POLY_SHL and NIST_Z_UPDATE_AS_POLY_XOR. *)
let NIST_LOOP_AS_POLY_LOOP = prove(
  `!n z v x:int128.
    bit_reflect128(ghash_mul_loop z v x n) =
    poly_mul_loop (bit_reflect128 z) (bit_reflect128 v)
                  (bit_reflect128 x) n`,
  INDUCT_TAC THENL
   [REWRITE_TAC[ghash_mul_loop; poly_mul_loop];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[ghash_mul_loop; poly_mul_loop; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    SUBGOAL_THEN `128 - SUC n < 128` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun ih -> GEN_REWRITE_TAC LAND_CONV [ih]) THEN
    MP_TAC(SPECL [`z:int128`; `v:int128`; `x:int128`; `128 - SUC n`] NIST_Z_UPDATE_AS_POLY_XOR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPEC `v:int128` NIST_V_UPDATE_AS_POLY_SHL) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

(* bit_reflect128(0) = 0 *)
let REFLECT128_ZERO = prove(
  `bit_reflect128 (word 0 : int128) = word 0`,
  REWRITE_TAC[bit_reflect128] THEN CONV_TAC WORD_REDUCE_CONV);;

(* Bridge A, Stage 1: the NIST Algorithm 1 multiply, after bit_reflect128,
   equals the natural-order polynomial loop. This separates the NIST bit-
   ordering concern from the polynomial algebra — everything after this
   point works in natural bit order. *)
let NIST_GHASH_MUL_BYTREV_EQ_POLY_LOOP = prove(
  `!x y:int128.
    bit_reflect128(nist_ghash_mul x y) =
    poly_mul_loop (word 0) (bit_reflect128 y) (bit_reflect128 x) 128`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nist_ghash_mul; NIST_LOOP_AS_POLY_LOOP; REFLECT128_ZERO]);;

(* ---- Uniqueness of 128-bit representatives mod P(x) --------------------- *)

let BOOL_POLY_RING_MUL_EQ_POLY_MUL = prove(
  `ring_mul bool_poly = poly_mul bool_ring`,
  REWRITE_TAC[bool_poly; POLY_RING]);;

let BOOL_POLY_RING_ZERO_EQ_POLY_ZERO = prove(
  `ring_0 bool_poly = poly_0 bool_ring`,
  REWRITE_TAC[bool_poly; POLY_RING]);;

(* P(x) is nonzero (degree 128 > 0). *)
let GHASH_POLY_NEQ_ZERO = prove(
  `~(ghash_poly = ring_0 bool_poly)`,
  REWRITE_TAC[bool_poly; POLY_RING] THEN
  DISCH_THEN(MP_TAC o AP_TERM `poly_deg bool_ring:((1->num)->bool)->num`) THEN
  REWRITE_TAC[POLY_DEG_GHASH_POLY; bool_poly; POLY_RING; POLY_DEG_0] THEN
  ARITH_TAC);;

(* If P(x) divides a polynomial of degree < 128, that polynomial must be zero. *)
let GHASH_POLY_DIVIDES_IMPLIES_ZERO_IF_LOW_DEG = prove(
  `!p:(1->num)->bool. p IN ring_carrier bool_poly /\
       ring_divides bool_poly ghash_poly p /\
       poly_deg bool_ring p < 128
       ==> p = ring_0 bool_poly`,
  GEN_TAC THEN ASM_CASES_TAC `p:(1->num)->bool = ring_0 bool_poly` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `poly_deg bool_ring (p:(1->num)->bool) >= 128` MP_TAC THENL
   [ALL_TAC; ASM_ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_divides]) THEN
  ASM_REWRITE_TAC[GHASH_BOOL_POLY] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(1->num)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(q:(1->num)->bool = ring_0 bool_poly)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_MUL_RZERO; GHASH_BOOL_POLY]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[GE; BOOL_POLY_RING_MUL_EQ_POLY_MUL] THEN
  SUBGOAL_THEN
    `poly_deg bool_ring (poly_mul bool_ring ghash_poly (q:(1->num)->bool)) =
     poly_deg bool_ring ghash_poly + poly_deg bool_ring q`
    (fun th -> REWRITE_TAC[th; POLY_DEG_GHASH_POLY] THEN ARITH_TAC) THEN
  MATCH_MP_TAC POLY_DEG_MUL THEN
  REWRITE_TAC[INTEGRAL_DOMAIN_BOOL_RING; RING_POLYNOMIAL_GHASH_POLY] THEN
  SUBGOAL_THEN `ring_polynomial bool_ring (q:(1->num)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `(q:(1->num)->bool) IN ring_carrier bool_poly` THEN
    REWRITE_TAC[bool_poly; POLY_RING; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM BOOL_POLY_RING_ZERO_EQ_POLY_ZERO] THEN
  ASM_MESON_TAC[GHASH_POLY_NEQ_ZERO; BOOL_POLY_RING_ZERO_EQ_POLY_ZERO]);;

(* CONG_MOD_GHASH_IMP_WORD_EQ: congruent 128-bit words mod P(x) are equal.
   The linchpin theorem — unique representative in degree < 128. *)
let CONG_MOD_GHASH_IMP_WORD_EQ = prove(
  `!(x:128 word) (y:128 word).
    (poly_of_word x == poly_of_word y) (mod_ghash) ==> x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cong] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM WORD_XOR_EQ_0] THEN
  MATCH_MP_TAC(INST_TYPE [`:128`,`:N`] POLY_OF_WORD_INJ) THEN
  REWRITE_TAC[POLY_OF_WORD_0] THEN
  MATCH_MP_TAC GHASH_POLY_DIVIDES_IMPLIES_ZERO_IF_LOW_DEG THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[mod_ghash; BOOL_POLY_OF_WORD]) THEN
    STRIP_TAC THEN
    REWRITE_TAC[POLY_OF_WORD_XOR; GSYM BOOL_POLY_SUB] THEN
    FIRST_X_ASSUM(MP_TAC o
      REWRITE_RULE[REWRITE_RULE[GHASH_BOOL_POLY]
        (SPEC `ghash_poly:(1->num)->bool`
          (REWRITE_RULE[GHASH_BOOL_POLY]
            (ISPEC `bool_poly` IN_IDEAL_GENERATED_SING_EQ)))]) THEN
    REWRITE_TAC[];
    MATCH_MP_TAC(ARITH_RULE `x <= 127 ==> x < 128`) THEN
    REWRITE_TAC[POLY_DEG_POLY_OF_WORD] THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC]);;

(* ========================================================================= *)
(* Key equivalence: gcm_gmult_spec = polyval_dot via byteswap128             *)
(*                                                                           *)
(* GCM_GMULT_SPEC_EQ_POLYVAL_DOT:                                            *)
(*   !xi h. let H = byteswap128 h in                                         *)
(*     gcm_gmult_spec xi h (word_zx(karatsuba_mid H)) =                      *)
(*     word_reversefields 8 (polyval_dot (word_reversefields 8 xi) H)        *)
(*                                                                           *)
(* This connects the ARM implementation spec to the algebraic                *)
(* polyval_dot, which has all the mod Q(x) congruence proofs.                *)
(*                                                                           *)
(* Proof strategy:                                                           *)
(* 1. Expand both sides with PMUL_KARATSUBA + KARATSUBA_LIMBS                *)
(* 2. Abbreviate the 3 Karatsuba pmull results (xl, xh, xm)                  *)
(* 3. Use KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS: relate Karatsuba middle term   *)
(*     to Prop3 limbs                                                        *)
(* 4. Use BARRETT_REDUCTION_EQ_PROP3_REDUCTION: spec's 2-phase reduction =   *)
(*     Prop3's reduction                                                     *)
(*    (proved by WORD_BLAST on 256 Boolean variables = 4 x 64-bit limbs)     *)
(* ========================================================================= *)

(* --- Helper: Karatsuba 256-bit product limb extractions --- *)

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

(* --- Helper: xm' halves = Karatsuba ABCD limbs B and C --- *)

(* The assembly's EXT+EOR Karatsuba recombination produces the same 64-bit
   limbs (B, C) that Gueron's Proposition 3 expects as input. This bridges
   the assembly's instruction-level pattern to the POLYVAL_REDUCE_PROP3_CORRECT. *)
let KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS = prove(
  `!(xl:int128) (xh:int128) (xm:int128).
    let mid = word_xor (word_xor xm xl) xh in
    let xm' = word_xor (word_xor xl xh)
              (word_xor (word_subword (word_join xh xl : 256 word) (64,128) : int128) xm) in
    word_subword xm' (0,64) : 64 word =
      word_xor (word_subword xl (64,64)) (word_subword mid (0,64)) /\
    word_subword xm' (64,64) : 64 word =
      word_xor (word_subword xh (0,64)) (word_subword mid (64,64))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC WORD_BLAST);;

(* --- Helper: spec's reduction = Prop3's reduction (on 4 x 64-bit limbs) --- *)

(* The assembly's two-phase Montgomery reduction (shifts by 63,62,57 + EXT+EOR)
   produces the same result as Proposition 3's reduction on the same four
   64-bit limbs. Bridges the assembly's reduction to nebeid's POLYVAL_REDUCE_PROP3_CORRECT. *)
let BARRETT_REDUCTION_EQ_PROP3_REDUCTION = prove(
  `!(a:64 word) (b:64 word) (c:64 word) (d:64 word).
    let wa:int128 = word_xor
      (word_xor (word_shl (word_zx a : int128) 63)
                (word_shl (word_zx a : int128) 62))
      (word_shl (word_zx a : int128) 57) in
    let phase1:int128 = word_xor wa (word_join a b : int128) in
    let t3:int128 = word_subword (word_join phase1 phase1 : 256 word) (64,128) in
    let red2:int128 = word_xor
      (word_xor (word_shl (word_zx (word_subword phase1 (0,64) : 64 word) : int128) 63)
                (word_shl (word_zx (word_subword phase1 (0,64) : 64 word) : int128) 62))
      (word_shl (word_zx (word_subword phase1 (0,64) : 64 word) : int128) 57) in
    word_xor (word_xor (word_join d c : int128) t3) red2 =
    (let v:64 word = word_xor b (word_subword wa (0,64)) in
     let u:64 word = word_xor (word_xor c a) (word_subword wa (64,64)) in
     let wv:int128 = word_xor
       (word_xor (word_shl (word_zx v : int128) 63)
                 (word_shl (word_zx v : int128) 62))
       (word_shl (word_zx v : int128) 57) in
     word_join (word_xor (word_xor d v) (word_subword wv (64,64)))
              (word_xor u (word_subword wv (0,64))) : int128)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC WORD_BLAST);;

(* --- Main theorem: gcm_gmult_spec = polyval_dot via byteswap128 --- *)

let GCM_GMULT_SPEC_EQ_POLYVAL_DOT = prove(
  `!xi h:int128.
    let H = byteswap128 h in
    gcm_gmult_spec xi h (word_zx(karatsuba_mid H) : int128) =
    word_reversefields 8 (polyval_dot (word_reversefields 8 xi) H)`,
  X_GEN_TAC `xi:int128` THEN X_GEN_TAC `h:int128` THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; gcm_gmult_spec; polyval_dot;
              polyval_reduce_prop3; byteswap128; karatsuba_mid;
              REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[KARATSUBA_LIMBS] THEN
  REWRITE_TAC[PMUL_W_64_128] THEN
  MATCH_MP_TAC(MESON[] `x = y ==> word_reversefields 8 x = word_reversefields 8 y`) THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS] THEN
  ABBREV_TAC `xl:int128 = word_pmul (word_subword (h:int128) (64,64) : 64 word)
    (word_subword (word_reversefields 8 (xi:int128)) (0,64) : 64 word)` THEN
  ABBREV_TAC `xh:int128 = word_pmul (word_subword (h:int128) (0,64) : 64 word)
    (word_subword (word_reversefields 8 (xi:int128)) (64,64) : 64 word)` THEN
  ABBREV_TAC `xm:int128 = word_pmul
    (word_xor (word_subword (h:int128) (64,64) : 64 word) (word_subword h (0,64) : 64 word))
    (word_xor (word_subword (word_reversefields 8 (xi:int128)) (0,64) : 64 word)
              (word_subword (word_reversefields 8 xi) (64,64) : 64 word))` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_PMUL_SYM]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS] THEN
  ONCE_REWRITE_TAC[WORD_PMUL_SYM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] BARRETT_REDUCTION_EQ_PROP3_REDUCTION] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV));;

(* ========================================================================= *)
(* POLY_SHL_XOR_CONG_MOD_GHASH: V-step preserves congruence mod P(x)         *)
(*                                                                           *)
(* The V-update in poly_mul_loop (shift + conditional XOR with 0x87) is      *)
(* congruent to multiplication by the polynomial variable x mod P(x).        *)
(* This is the core inductive step for connecting the NIST loop to           *)
(* polynomial multiplication.                                                *)
(* ========================================================================= *)

(* ---- Helper lemmas for POLY_SHL_XOR_CONG_MOD_GHASH ---- *)

(* poly_var bool_ring one is in ring_carrier bool_poly *)
let POLY_VAR_IN_BOOL_POLY = prove(
  `poly_var bool_ring one IN ring_carrier bool_poly`,
  REWRITE_TAC[bool_poly; POLY_VAR; IN_UNIV]);;

(* x * poly_of_word is in the carrier *)
let RING_MUL_POLY_VAR = prove(
  `!v:N word. ring_mul bool_poly (poly_var bool_ring one) (poly_of_word v)
              IN ring_carrier bool_poly`,
  GEN_TAC THEN MATCH_MP_TAC RING_MUL THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VAR_IN_BOOL_POLY]);;

(* word_clz v >= 1 when bit 127 v is false (for int128) *)
let WORD_CLZ_GE_1 = prove(
  `!v:int128. ~bit 127 v ==> 1 <= word_clz v`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  REWRITE_TAC[WORD_CLZ_EQ_0; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* Degree bound: poly_deg(u * poly_of_word v) < 128 when ~bit 127 v *)
let POLY_DEG_MUL_V_U_BOUND = prove(
  `!v:int128. ~bit 127 v ==>
    poly_deg bool_ring
      (ring_mul bool_poly (poly_of_word v) (poly_var bool_ring one)) < 128`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[BOOL_POLY_MUL] THEN
  MATCH_MP_TAC LET_TRANS THEN
  EXISTS_TAC `poly_deg bool_ring (poly_of_word (v:int128)) +
              poly_deg bool_ring (poly_var bool_ring one:(1->num)->bool)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC POLY_DEG_MUL_LE THEN
    REWRITE_TAC[RING_POLYNOMIAL_OF_WORD; RING_POLYNOMIAL_VAR];
    REWRITE_TAC[POLY_DEG_POLY_OF_WORD; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[POLY_DEG_VAR] THEN
    SUBGOAL_THEN `~(ring_1 bool_ring <=> ring_0 bool_ring)` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[GSYM bool_ring; BOOL_RING]; ALL_TAC] THEN
    MP_TAC(ISPEC `v:int128` WORD_CLZ_GE_1) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* word_shl v 1 = word_of_poly(poly_of_word v * x) at any word size *)
let WORD_SHL_1_AS_OF_POLY = prove(
  `!v:int128. word_shl v 1 =
    word_of_poly(ring_mul bool_poly (poly_of_word v) (poly_var bool_ring one)) : int128`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM POLY_OF_WORD_2; GSYM WORD_PMUL_POLY] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 WORD_PMUL_POW2)] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* FALSE case: when ~bit 127 v, poly_of_word(shl v 1) = x * poly_of_word(v) *)
let POLY_SHL1_EQ_MUL_VAR_WHEN_NO_OVERFLOW = prove(
  `!v:int128. ~bit 127 v ==>
    poly_of_word(word_shl v 1) =
    ring_mul bool_poly (poly_var bool_ring one) (poly_of_word v)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_SHL_1_AS_OF_POLY] THEN
  SUBGOAL_THEN
    `(poly_of_word:int128->(1->num)->bool)
     (word_of_poly(ring_mul bool_poly (poly_of_word (v:int128)) (poly_var bool_ring one))) =
     ring_mul bool_poly (poly_of_word v) (poly_var bool_ring one)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:128`,`:N`] POLY_OF_WORD_OF_POLY) THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_MUL THEN
      REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VAR_IN_BOOL_POLY];
      REWRITE_TAC[DIMINDEX_128] THEN ASM_SIMP_TAC[POLY_DEG_MUL_V_U_BOUND]];
    MP_TAC(ISPECL [`bool_poly`; `poly_of_word (v:int128)`;
                    `poly_var bool_ring one:(1->num)->bool`] RING_MUL_SYM) THEN
    REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VAR_IN_BOOL_POLY] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* ODD(1 DIV 2^n) iff n = 0 *)
let ODD_1_DIV_2EXP = prove(
  `!n. ODD(1 DIV 2 EXP n) <=> (n = 0)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `1 DIV 2 EXP n = 0` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_LT THEN
      TRANS_TAC LTE_TRANS `2 EXP 1` THEN CONJ_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV;
        REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
      REWRITE_TAC[ODD]]]);;

(* 256-bit XOR overflow identity:
   word_zx(word_shl v 1 : int128) XOR word_shl(word_zx v : 256) 1
   = word with just bit 128 set when bit 127 v, else 0 *)
let WORD_ZX_SHL_XOR_OVERFLOW = prove(
  `!v:int128.
    word_xor (word_zx(word_shl v 1 : int128) : 256 word)
             (word_shl (word_zx v : 256 word) 1) =
    (if bit 127 v then word_shl (word 1 : 256 word) 128 else word 0 : 256 word)`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_256] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_XOR; BIT_WORD_ZX; BIT_WORD_SHL; BIT_WORD;
              BIT_WORD_0; DIMINDEX_128; DIMINDEX_256] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < 128` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `i - 1 < 256` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[BIT_WORD_SHL; BIT_WORD; BIT_WORD_0; DIMINDEX_256; ODD_1_DIV_2EXP] THEN
    ASM_ARITH_TAC;
    SUBGOAL_THEN `1 <= i /\ i - 1 < 256` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `i = 128` THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      COND_CASES_TAC THEN
      REWRITE_TAC[BIT_WORD_SHL; BIT_WORD; BIT_WORD_0; DIMINDEX_256; ODD_1_DIV_2EXP] THEN
      CONV_TAC NUM_REDUCE_CONV;
      SUBGOAL_THEN `~(i - 1 < 128)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `128 <= i - 1` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[BIT_TRIVIAL; DIMINDEX_128] THEN
      COND_CASES_TAC THEN
      REWRITE_TAC[BIT_WORD_SHL; BIT_WORD; BIT_WORD_0; DIMINDEX_256; ODD_1_DIV_2EXP] THEN
      ASM_ARITH_TAC]]);;

(* poly_of_word(word_shl (word 1 : 256) 128) = x^128 *)
let POLY_OF_WORD_X128 = prove(
  `poly_of_word(word_shl (word 1 : 256 word) 128 : 256 word) =
   ring_pow bool_poly (poly_var bool_ring one) 128`,
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(SPEC `128` (INST_TYPE [`:256`, `:N`] POLY_VAR_POW_OF_WORD)) THEN
  REWRITE_TAC[DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* poly_of_word at 128 and 256 bits agree for zero-extended words *)
let POLY_OF_WORD_ZX_128_256 = prove(
  `!w:int128. poly_of_word(word_zx w : 256 word) = poly_of_word w`,
  GEN_TAC THEN
  MP_TAC(SPEC `w:int128` (INST_TYPE [`:128`,`:M`; `:256`,`:N`] POLY_OF_WORD_ZX)) THEN
  REWRITE_TAC[DIMINDEX_128; DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV);;

(* poly_of_word(word 2 : 256 word) = x (the polynomial variable) *)
let POLY_OF_WORD2_256_EQ_POLY_VAR = prove(
  `poly_of_word(word 2 : 256 word) = poly_var bool_ring one`,
  MP_TAC(SPEC `1` (INST_TYPE [`:256`, `:N`] POLY_VAR_POW_OF_WORD)) THEN
  REWRITE_TAC[DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(SUBST1_TAC o GSYM) THEN
  SIMP_TAC[RING_POW_1; POLY_VAR_IN_BOOL_POLY]);;

(* poly_of_word(word_shl(word_zx v : 256) 1) = x * poly_of_word(v) *)
let POLY_SHL1_ZX256_EQ_MUL_VAR = prove(
  `!v:int128. poly_of_word(word_shl (word_zx v : 256 word) 1 : 256 word) =
              ring_mul bool_poly (poly_var bool_ring one) (poly_of_word v)`,
  GEN_TAC THEN
  SUBGOAL_THEN `word_shl (word_zx (v:int128) : 256 word) 1 =
    (word_of_poly(ring_mul bool_poly (poly_of_word(word_zx v : 256 word))
                                     (poly_of_word(word 2 : 256 word))) : 256 word)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_PMUL_POLY; GSYM(CONJUNCT2 WORD_PMUL_POW2)] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(poly_of_word:256 word->(1->num)->bool)
    (word_of_poly(ring_mul bool_poly (poly_of_word(word_zx (v:int128) : 256 word))
                                     (poly_of_word(word 2 : 256 word)))) =
    ring_mul bool_poly (poly_of_word(word_zx v : 256 word)) (poly_of_word(word 2 : 256 word))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:256`,`:N`] POLY_OF_WORD_OF_POLY) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_MUL THEN REWRITE_TAC[BOOL_POLY_OF_WORD];
      REWRITE_TAC[DIMINDEX_256; BOOL_POLY_MUL; POLY_OF_WORD_ZX_128_256] THEN
      MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `poly_deg bool_ring (poly_of_word(v:int128)) +
                  poly_deg bool_ring (poly_of_word(word 2:256 word))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC POLY_DEG_MUL_LE THEN REWRITE_TAC[RING_POLYNOMIAL_OF_WORD];
        REWRITE_TAC[POLY_DEG_POLY_OF_WORD; DIMINDEX_128; DIMINDEX_256] THEN
        CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
        ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[POLY_OF_WORD_ZX_128_256; POLY_OF_WORD2_256_EQ_POLY_VAR] THEN
  MP_TAC(ISPECL [`bool_poly`; `poly_of_word(v:int128)`;
                  `poly_var bool_ring one:(1->num)->bool`] RING_MUL_SYM) THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VAR_IN_BOOL_POLY] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ghash_poly = x^128 + poly_of_word(word 0x87 : 256 word) *)
let GHASH_POLY_EQ_X128_PLUS_LOW = prove(
  `ghash_poly = ring_add bool_poly
    (ring_pow bool_poly (poly_var bool_ring one) 128)
    (poly_of_word(word 0x87 : 256 word))`,
  MP_TAC(INST_TYPE [`:256`, `:N`] GHASH_POLY_OF_WORD) THEN
  REWRITE_TAC[DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(word 340282366920938463463374607431768211591 : 256 word) =
    word_xor (word_shl (word 1 : 256 word) 128) (word 0x87 : 256 word)` SUBST1_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[POLY_OF_WORD_XOR; POLY_OF_WORD_X128]);;

(* ring_add(ring_add A B) C = ring_add(ring_add A C) B *)
let BOOL_POLY_ADD_SWAP_MIDDLE = prove(
  `!r (A:A) B C. A IN ring_carrier r /\ B IN ring_carrier r /\ C IN ring_carrier r ==>
    ring_add r (ring_add r A B) C = ring_add r (ring_add r A C) B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `A:A`; `B:A`; `C:A`] RING_ADD_ASSOC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o GSYM) THEN
  MP_TAC(ISPECL [`r:A ring`; `B:A`; `C:A`] RING_ADD_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `A:A`; `C:A`; `B:A`] RING_ADD_ASSOC) THEN
  ASM_REWRITE_TAC[]);;

(* ---- POLY_SHL_XOR_CONG_MOD_GHASH: the V-step is congruent to multiplication by x ---- *)

(* The V-step of the polynomial loop:
     if bit 127 v then word_xor (word_shl v 1) (word 0x87) else word_shl v 1
   satisfies: poly_of_word(V_step(v)) ≡ x * poly_of_word(v) (mod P(x)).

   Proof strategy:
   - FALSE case (~bit 127 v): word_shl v 1 = word_of_poly(x * poly_of_word v)
     and the degree < 128, so the round-trip preserves the polynomial.
   - TRUE case (bit 127 v): work at 256 bits via WORD_ZX_SHL_XOR_OVERFLOW.
     The overflow bit gives x^128, and x^128 + poly(0x87) = ghash_poly. *)
let POLY_SHL_XOR_CONG_MOD_GHASH = prove(
  `!v:int128.
    (poly_of_word
      (if bit 127 v then word_xor (word_shl v 1) (word 0x87)
       else word_shl v 1) ==
     ring_mul bool_poly (poly_var bool_ring one) (poly_of_word v))
    (mod_ghash)`,
  GEN_TAC THEN ASM_CASES_TAC `bit 127 (v:int128)` THEN ASM_REWRITE_TAC[] THENL
   [(* TRUE case: quotient witness = ring_1 *)
    REWRITE_TAC[cong; mod_ghash; BOOL_POLY_OF_WORD] THEN
    SIMP_TAC[IDEAL_GENERATED_SING; GHASH_BOOL_POLY; IN_ELIM_THM] THEN
    REWRITE_TAC[ring_divides; GHASH_BOOL_POLY] THEN
    SIMP_TAC[RING_SUB; BOOL_POLY_OF_WORD; RING_MUL_POLY_VAR] THEN
    EXISTS_TAC `ring_1 bool_poly` THEN
    CONJ_TAC THENL [REWRITE_TAC[RING_1; GHASH_BOOL_POLY]; ALL_TAC] THEN
    REWRITE_TAC[BOOL_POLY_SUB] THEN
    SIMP_TAC[RING_MUL_RID; GHASH_BOOL_POLY] THEN
    REWRITE_TAC[POLY_OF_WORD_XOR] THEN
    (* Derive truncation identity: poly(shl v 1) + x*poly(v) = x^128 *)
    MP_TAC(ISPEC `v:int128` WORD_ZX_SHL_XOR_OVERFLOW) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `poly_of_word:(256 word)->(1->num)->bool`) THEN
    REWRITE_TAC[POLY_OF_WORD_XOR; POLY_OF_WORD_X128;
                POLY_OF_WORD_ZX_128_256; POLY_SHL1_ZX256_EQ_MUL_VAR] THEN
    DISCH_TAC THEN
    (* Convert poly(word 135:int128) to 256-bit type for GHASH_POLY_EQ_X128_PLUS_LOW *)
    SUBGOAL_THEN `poly_of_word(word 135:int128) = poly_of_word(word 135:256 word)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MP_TAC(SPEC `word 135:int128` (INST_TYPE [`:128`,`:M`; `:256`,`:N`] POLY_OF_WORD_ZX)) THEN
      REWRITE_TAC[DIMINDEX_128; DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN(SUBST1_TAC o GSYM) THEN AP_TERM_TAC THEN CONV_TAC WORD_REDUCE_CONV;
      ALL_TAC] THEN
    (* Unfold ghash_poly = x^128 + poly(word 135:256) *)
    GEN_REWRITE_TAC (RAND_CONV) [GHASH_POLY_EQ_X128_PLUS_LOW] THEN
    (* Ring AC: (A+B)+C = (A+C)+B *)
    MP_TAC(ISPECL [`bool_poly`;
      `poly_of_word(word_shl (v:int128) 1)`;
      `poly_of_word(word 135 : 256 word)`;
      `ring_mul bool_poly (poly_var bool_ring one) (poly_of_word (v:int128))`] BOOL_POLY_ADD_SWAP_MIDDLE) THEN
    REWRITE_TAC[BOOL_POLY_OF_WORD; RING_MUL_POLY_VAR] THEN
    DISCH_THEN SUBST1_TAC THEN
    (* Now: (A+C)+B = x^128+B, use A+C = x^128 *)
    AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM ACCEPT_TAC;
    (* FALSE case: poly(shl v 1) = u*poly(v), congruence is reflexive *)
    ASM_SIMP_TAC[POLY_SHL1_EQ_MUL_VAR_WHEN_NO_OVERFLOW; MOD_GHASH_REFL; RING_MUL_POLY_VAR]]);;

(* ========================================================================= *)
(* Equivalence A completion: NIST loop = polynomial multiplication mod P(x)  *)
(*                                                                           *)
(* poly_mul_loop 0 y x 128 = ghash_reduce(word_pmul x y)                     *)
(* brp(nist_ghash_mul x y) = ghash_reduce(word_pmul (brp x) (brp y))         *)
(* ========================================================================= *)

(* ---- Partial polynomial: Horner evaluation of x's bits ---- *)

(* partial_poly x n = the polynomial formed by processing n bits of x
   using the Horner scheme. After 128 steps, this equals poly_of_word(x). *)
let partial_poly = define
  `partial_poly (x:int128) 0 = ring_0 bool_poly /\
   partial_poly x (SUC n) =
     ring_add bool_poly
       (if bit (128 - SUC n) x then ring_1 bool_poly else ring_0 bool_poly)
       (ring_mul bool_poly (poly_var bool_ring one) (partial_poly x n))`;;

let PARTIAL_POLY_IN_CARRIER = prove(
  `!x:int128. !n. partial_poly x n IN ring_carrier bool_poly`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[partial_poly; RING_0; GHASH_BOOL_POLY];
    REWRITE_TAC[partial_poly] THEN
    MATCH_MP_TAC RING_ADD THEN CONJ_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[RING_1; RING_0; GHASH_BOOL_POLY];
      MATCH_MP_TAC RING_MUL THEN
      ASM_REWRITE_TAC[POLY_VAR_IN_BOOL_POLY]]]);;

(* ---- Horner evaluation: partial_poly x 128 = poly_of_word x ---- *)

(* word_horner: the word-level version of partial_poly *)
let word_horner = define
  `word_horner (x:int128) 0 = (word 0 : int128) /\
   word_horner x (SUC n) =
     word_xor (if bit (128 - SUC n) x then word 1 else word 0 : int128)
              (word_shl (word_horner x n) 1)`;;

(* Bit-level characterization of word_horner *)
let WORD_HORNER_BIT = prove(
  `!x:int128 n. n <= 128 ==>
    (!k. k < 128 ==> (bit k (word_horner x n) <=> k < n /\ bit (128 - n + k) x))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[word_horner; BIT_WORD_0; LT];
    DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `n <= 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[word_horner; BIT_WORD_XOR; BIT_WORD_SHL; DIMINDEX_128] THEN
    ASM_CASES_TAC `bit (128 - SUC n) (x:int128)` THEN ASM_REWRITE_TAC[BIT_WORD; BIT_WORD_0; ODD_1_DIV_2EXP; DIMINDEX_128] THENL
     [ASM_CASES_TAC `k = 0` THENL
       [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN `128 - SUC n + 0 = 128 - SUC n` SUBST1_TAC THENL
         [ARITH_TAC; ASM_REWRITE_TAC[] THEN ARITH_TAC];
        SUBGOAL_THEN `1 <= k /\ k - 1 < 128` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `k - 1`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `128 - n + (k - 1) = 128 - SUC n + k` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(k - 1 < n <=> k < SUC n)` SUBST1_TAC THENL
         [ASM_ARITH_TAC; REFL_TAC]];
      ASM_CASES_TAC `k = 0` THENL
       [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN `128 - SUC n + 0 = 128 - SUC n` SUBST1_TAC THENL
         [ARITH_TAC; ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `1 <= k /\ k - 1 < 128` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `k - 1`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `128 - n + (k - 1) = 128 - SUC n + k` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(k - 1 < n <=> k < SUC n)` SUBST1_TAC THENL
         [ASM_ARITH_TAC; REFL_TAC]]]]);;

(* word_horner x 128 = x *)
let WORD_HORNER_128 = prove(
  `!x:int128. word_horner x 128 = x`,
  GEN_TAC THEN ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN REWRITE_TAC[DIMINDEX_128] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:int128`; `128`] WORD_HORNER_BIT) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[ADD_CLAUSES]);;

(* bit 127 of word_horner x n is F for n <= 127 (no overflow during Horner build) *)
let WORD_HORNER_BIT127_F = prove(
  `!x:int128. !n. n <= 127 ==> ~bit 127 (word_horner x n)`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:int128`; `n:num`] WORD_HORNER_BIT) THEN
  SUBGOAL_THEN `n <= 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `127`) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC);;

(* partial_poly x n = poly_of_word(word_horner x n) for n <= 128 *)
let PARTIAL_POLY_AS_WORD_HORNER = prove(
  `!x:int128. !n. n <= 128 ==> partial_poly x n = poly_of_word(word_horner x n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[partial_poly; word_horner; POLY_OF_WORD_0];
    DISCH_TAC THEN
    SUBGOAL_THEN `n <= 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REWRITE_TAC[partial_poly; word_horner] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLY_OF_WORD_XOR] THEN
    SUBGOAL_THEN `poly_of_word(if bit (128 - SUC n) (x:int128) then word 1 else word 0 : int128) =
                  (if bit (128 - SUC n) x then ring_1 bool_poly else ring_0 bool_poly)`
      SUBST1_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[POLY_OF_WORD_1; POLY_OF_WORD_0]; ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC POLY_SHL1_EQ_MUL_VAR_WHEN_NO_OVERFLOW THEN
    MATCH_MP_TAC WORD_HORNER_BIT127_F THEN ASM_ARITH_TAC]);;

(* PARTIAL_POLY_128: the Horner evaluation of x's bits equals poly_of_word(x) *)
let PARTIAL_POLY_128 = prove(
  `!x:int128. partial_poly x 128 = poly_of_word x`,
  GEN_TAC THEN
  MP_TAC(SPECL [`x:int128`; `128`] PARTIAL_POLY_AS_WORD_HORNER) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[WORD_HORNER_128]);;

(* ---- Bridge A, Stage 2: poly_mul_loop = ghash_reduce(word_pmul) ---------- *)
(*                                                                            *)
(* Both compute poly(x) * poly(y) mod P(x), but differently:                  *)
(*   - poly_mul_loop: 128-step Horner loop with online reduction              *)
(*   - ghash_reduce(word_pmul): full 256-bit multiply then reduce             *)
(* We prove they're equal via mod-P uniqueness (CONG_MOD_GHASH_IMP_WORD_EQ):  *)
(* both are 128-bit words congruent to the same product mod P, so equal.      *)
(*                                                                            *)
(* The ring algebra helpers below support the inductive step of the loop      *)
(* invariant: poly(loop_result) ≡ poly(z) + partial_poly(x,n) * poly(v)       *)
(* (mod P) at each iteration.                                                 *)

(* Distributes (1 + x*pp) * pv into pv + (x*pp)*pv.
   Used in the Horner step: multiplying by the next partial polynomial. *)
let BOOL_POLY_ADD_ONE_RDISTRIB = prove(
  `!pp pv:(1->num)->bool. pp IN ring_carrier bool_poly /\ pv IN ring_carrier bool_poly ==>
    ring_mul bool_poly
      (ring_add bool_poly (ring_1 bool_poly) (ring_mul bool_poly (poly_var bool_ring one) pp))
      pv =
    ring_add bool_poly pv (ring_mul bool_poly (ring_mul bool_poly (poly_var bool_ring one) pp) pv)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`bool_poly`; `ring_1 bool_poly:(1->num)->bool`;
    `ring_mul bool_poly (poly_var bool_ring one) (pp:(1->num)->bool)`;
    `pv:(1->num)->bool`] RING_ADD_RDISTRIB) THEN
  ASM_SIMP_TAC[RING_1; RING_MUL; GHASH_BOOL_POLY; POLY_VAR_IN_BOOL_POLY] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[RING_MUL_LID; GHASH_BOOL_POLY]);;

(* Moves x from one factor to the other: (x*pp)*pv = pp*(x*pv).
   Used to align the induction hypothesis with the Horner recurrence. *)
let BOOL_POLY_MUL_ASSOC_COMM = prove(
  `!pp pv:(1->num)->bool. pp IN ring_carrier bool_poly /\ pv IN ring_carrier bool_poly ==>
    ring_mul bool_poly (ring_mul bool_poly (poly_var bool_ring one) pp) pv =
    ring_mul bool_poly pp (ring_mul bool_poly (poly_var bool_ring one) pv)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ring_mul bool_poly (poly_var bool_ring one) (pp:(1->num)->bool) =
                ring_mul bool_poly pp (poly_var bool_ring one)` SUBST1_TAC THENL
   [MATCH_MP_TAC(ISPEC `bool_poly` RING_MUL_SYM) THEN
    ASM_REWRITE_TAC[POLY_VAR_IN_BOOL_POLY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`bool_poly`; `pp:(1->num)->bool`;
    `poly_var bool_ring one:(1->num)->bool`; `pv:(1->num)->bool`] RING_MUL_ASSOC) THEN
  ASM_SIMP_TAC[POLY_VAR_IN_BOOL_POLY] THEN MESON_TAC[]);;

(* Addition associativity: a + (b + c) = (a + b) + c.
   Needed to regroup terms when combining the Z-update with the V-update. *)
let BOOL_POLY_ADD_ASSOC_3 = prove(
  `!a b c:(1->num)->bool. a IN ring_carrier bool_poly /\ b IN ring_carrier bool_poly /\
    c IN ring_carrier bool_poly ==>
    ring_add bool_poly a (ring_add bool_poly b c) =
    ring_add bool_poly (ring_add bool_poly a b) c`,
  MESON_TAC[RING_ADD_ASSOC]);;

(* One step of the loop invariant: after processing bit i, the loop result
   is congruent to poly(z) + partial_poly(x,n+1) * poly(v) (mod P). *)
let POLY_LOOP_STEP_CONG_MOD_GHASH = prove(
  `!n (z:int128) (v:int128) (x:int128) (pp:(1->num)->bool).
    pp IN ring_carrier bool_poly ==>
    (ring_add bool_poly
      (poly_of_word (if bit (128 - SUC n) x then word_xor z v else z))
      (ring_mul bool_poly pp
        (poly_of_word (if bit 127 v then word_xor (word_shl v 1) (word 135) else word_shl v 1))) ==
     ring_add bool_poly (poly_of_word z)
       (ring_mul bool_poly
         (ring_add bool_poly
           (if bit (128 - SUC n) x then ring_1 bool_poly else ring_0 bool_poly)
           (ring_mul bool_poly (poly_var bool_ring one) pp))
         (poly_of_word v)))
    (mod_ghash)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `bit (128 - SUC n) (x:int128)` THEN ASM_REWRITE_TAC[] THENL
   [(* TRUE case *)
    REWRITE_TAC[POLY_OF_WORD_XOR] THEN
    ASM_SIMP_TAC[BOOL_POLY_ADD_ONE_RDISTRIB; BOOL_POLY_OF_WORD] THEN
    ASM_SIMP_TAC[BOOL_POLY_MUL_ASSOC_COMM; BOOL_POLY_OF_WORD] THEN
    SUBGOAL_THEN `ring_add bool_poly (poly_of_word (z:int128))
      (ring_add bool_poly (poly_of_word (v:int128))
        (ring_mul bool_poly pp (ring_mul bool_poly (poly_var bool_ring one) (poly_of_word v)))) =
    ring_add bool_poly (ring_add bool_poly (poly_of_word z) (poly_of_word v))
      (ring_mul bool_poly pp (ring_mul bool_poly (poly_var bool_ring one) (poly_of_word v)))`
      SUBST1_TAC THENL
     [MATCH_MP_TAC BOOL_POLY_ADD_ASSOC_3 THEN
      ASM_SIMP_TAC[BOOL_POLY_OF_WORD; RING_MUL; POLY_VAR_IN_BOOL_POLY]; ALL_TAC] THEN
    MATCH_MP_TAC MOD_GHASH_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[MOD_GHASH_REFL] THEN MATCH_MP_TAC RING_ADD THEN
      REWRITE_TAC[BOOL_POLY_OF_WORD]; ALL_TAC] THEN
    MATCH_MP_TAC MOD_GHASH_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[MOD_GHASH_REFL] THEN ASM_REWRITE_TAC[];
      MATCH_ACCEPT_TAC POLY_SHL_XOR_CONG_MOD_GHASH];
    (* FALSE case *)
    ASM_SIMP_TAC[RING_ADD_LZERO; GHASH_BOOL_POLY; RING_MUL; POLY_VAR_IN_BOOL_POLY;
                  BOOL_POLY_OF_WORD] THEN
    ASM_SIMP_TAC[BOOL_POLY_MUL_ASSOC_COMM; BOOL_POLY_OF_WORD] THEN
    MATCH_MP_TAC MOD_GHASH_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[MOD_GHASH_REFL; BOOL_POLY_OF_WORD]; ALL_TAC] THEN
    MATCH_MP_TAC MOD_GHASH_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[MOD_GHASH_REFL] THEN ASM_REWRITE_TAC[];
      MATCH_ACCEPT_TAC POLY_SHL_XOR_CONG_MOD_GHASH]]);;

(* Full loop invariant by induction on n:
   poly(poly_mul_loop z v x n) ≡ poly(z) + partial_poly(x,n) * poly(v) (mod P).
   At n=128 with z=0, this gives: poly(loop_result) ≡ poly(x) * poly(v) (mod P). *)

let POLY_LOOP_HORNER_CONG_MOD_GHASH = prove(
  `!n (z:int128) (v:int128) (x:int128). n <= 128 ==>
    (poly_of_word(poly_mul_loop z v x n) ==
     ring_add bool_poly (poly_of_word z)
       (ring_mul bool_poly (partial_poly x n) (poly_of_word v)))
    (mod_ghash)`,
  INDUCT_TAC THENL
   [(* Base case *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[poly_mul_loop; partial_poly] THEN
    SIMP_TAC[RING_MUL_LZERO; GHASH_BOOL_POLY; BOOL_POLY_OF_WORD] THEN
    SIMP_TAC[RING_ADD_RZERO; GHASH_BOOL_POLY; BOOL_POLY_OF_WORD] THEN
    REWRITE_TAC[MOD_GHASH_REFL; BOOL_POLY_OF_WORD];
    (* Inductive step: use IH + POLY_LOOP_STEP_CONG_MOD_GHASH + MOD_GHASH_TRANS *)
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[poly_mul_loop; partial_poly; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    SUBGOAL_THEN `n <= 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [
      `(if bit (128 - SUC n) (x:int128) then word_xor z v else z) : int128`;
      `(if bit 127 (v:int128) then word_xor (word_shl v 1) (word 135) else word_shl v 1) : int128`;
      `x:int128`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:num`; `z:int128`; `v:int128`; `x:int128`; `partial_poly (x:int128) n`]
      POLY_LOOP_STEP_CONG_MOD_GHASH) THEN
    REWRITE_TAC[PARTIAL_POLY_IN_CARRIER] THEN DISCH_TAC THEN
    ASM_MESON_TAC[MOD_GHASH_TRANS]]);;

(* Instantiate the loop invariant at n=128, z=0: the Horner loop result
   is congruent to poly(x) * poly(y) (mod P). *)
let POLY_LOOP_FULL_CONG_MOD_GHASH = prove(
  `!x y:int128.
    (poly_of_word(poly_mul_loop (word 0) y x 128) ==
     ring_mul bool_poly (poly_of_word x) (poly_of_word y))
    (mod_ghash)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`128`; `word 0:int128`; `y:int128`; `x:int128`] POLY_LOOP_HORNER_CONG_MOD_GHASH) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[PARTIAL_POLY_128; POLY_OF_WORD_0] THEN
  SIMP_TAC[RING_ADD_LZERO; GHASH_BOOL_POLY; RING_MUL; BOOL_POLY_OF_WORD]);;

(* ---- poly_mul_loop = ghash_reduce(word_pmul) ---- *)

(* Both sides are congruent to poly(x)*poly(y) mod P, and both are 128-bit words,
   so they are equal by CONG_MOD_GHASH_IMP_WORD_EQ. *)
let POLY_LOOP_EQ_GHASH_REDUCE = prove(
  `!x y:int128. poly_mul_loop (word 0) y x 128 =
                ghash_reduce(word_pmul x y : 256 word)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONG_MOD_GHASH_IMP_WORD_EQ THEN
  MP_TAC(SPECL [`x:int128`; `y:int128`] POLY_LOOP_FULL_CONG_MOD_GHASH) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
    `(ring_mul bool_poly (poly_of_word (x:int128)) (poly_of_word (y:int128)) ==
      poly_of_word(ghash_reduce(word_pmul x y : 256 word))) (mod_ghash)`
    MP_TAC THENL
   [MP_TAC(ISPEC `word_pmul (x:int128) (y:int128) : 256 word` POLY_EQUIV_GHASH_REDUCE) THEN
    REWRITE_TAC[POLY_OF_WORD_PMUL_2N] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM MOD_GHASH_SYM] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(fun h0 -> DISCH_THEN(fun h1 ->
      ACCEPT_TAC(MATCH_MP MOD_GHASH_TRANS (CONJ h0 h1))))]);;

(* ========================================================================= *)
(* BRIDGE A: NIST Algorithm 1 = ghash_reduce(word_pmul(refl x, refl y))      *)
(*                                                                           *)
(* This is the top-level Bridge A theorem connecting the NIST specification  *)
(* to polynomial multiplication mod P(x) in the natural bit order.           *)
(* ========================================================================= *)

(* bit_reflect128(nist_ghash_mul x y) =
   poly_mul_loop 0 (bit_reflect128 y) (bit_reflect128 x) 128 *)
let NIST_GHASH_MUL_EQ_POLY_LOOP = prove(
  `!x y:int128.
    bit_reflect128(nist_ghash_mul x y) =
    poly_mul_loop (word 0) (bit_reflect128 y) (bit_reflect128 x) 128`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nist_ghash_mul; NIST_LOOP_AS_POLY_LOOP; REFLECT128_ZERO]);;

(* BRIDGE A: The main theorem.
   Combines NIST_GHASH_MUL_EQ_POLY_LOOP with POLY_LOOP_EQ_GHASH_REDUCE. *)
let NIST_GHASH_EQ_GHASH_REDUCE = prove(
  `!x y:int128.
    bit_reflect128(nist_ghash_mul x y) =
    ghash_reduce(word_pmul (bit_reflect128 x) (bit_reflect128 y) : 256 word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[NIST_GHASH_MUL_EQ_POLY_LOOP; POLY_LOOP_EQ_GHASH_REDUCE]);;

(* ========================================================================= *)
(* P(x) <-> Q(x) BRIDGE: poly_revn 254 maps ideal{P} to ideal{Q}           *)
(*                                                                           *)
(* This establishes that bit-reversing a mod-P result gives a mod-Q result,  *)
(* connecting ghash_reduce (mod P) to polyval_dot (mod Q).                   *)
(* ========================================================================= *)

(* ---- Helper lemmas for bool_poly coefficient manipulation ---- *)

(* The zero element of bool_ring is false. *)
let BOOL_RING_ZERO_IS_FALSE = prove(
  `ring_0 bool_ring <=> false`,
  REWRITE_TAC[BOOL_RING]);;

(* The zero polynomial has all coefficients false. *)
let BOOL_POLY_ZERO_ALL_COEFFS_FALSE = prove(
  `!m. ~(ring_0 bool_poly m)`,
  GEN_TAC THEN REWRITE_TAC[BOOL_POLY_ZERO; poly_0; poly_const; COND_ID; BOOL_RING_ZERO_IS_FALSE]);;

(* ring_add in bool_poly is pointwise XOR *)
let BOOL_POLY_ADD_POINTWISE = prove(
  `!(p:(1->num)->bool) (q:(1->num)->bool) (m:1->num).
    ring_add bool_poly p q m <=> ~(p m <=> q m)`,
  REWRITE_TAC[bool_poly; POLY_RING; poly_add] THEN
  REWRITE_TAC[BOOL_RING]);;

(* x^n has a single nonzero coefficient at degree n: (x^n)(m) <=> m = n. *)
let BOOL_POLY_POW_COEFF = prove(
  `!(n:num). n < 256 ==>
    (!(m:1->num). (ring_pow bool_poly (poly_var bool_ring one) n : (1->num)->bool) m <=> m one = n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(ring_pow bool_poly (poly_var bool_ring one) n : (1->num)->bool) =
                poly_of_word(word(2 EXP n) : 256 word)`
    SUBST1_TAC THENL
   [MP_TAC(SPEC `n:num` (REWRITE_RULE[DIMINDEX_256] (INST_TYPE [`:256`,`:N`] POLY_VAR_POW_OF_WORD))) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[poly_of_word; BIT_WORD; DIMINDEX_256] THEN
  ASM_CASES_TAC `(m:1->num) one = n` THENL
   [ASM_REWRITE_TAC[] THEN
    SIMP_TAC[DIV_REFL; EXP_EQ_0; ARITH] THEN REWRITE_TAC[ODD];
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(m:1->num) one < 256` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(m:1->num) one < n` THENL
     [SUBGOAL_THEN `(m:1->num) one <= n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[DIV_EXP; ARITH_RULE `~(2 = 0)`] THEN
      REWRITE_TAC[ODD_EXP] THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `2 EXP n DIV 2 EXP (m:1->num) one = 0` SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_LT THEN REWRITE_TAC[LT_EXP] THEN ASM_ARITH_TAC;
        REWRITE_TAC[ODD]]]]);;

(* P(x) has nonzero coefficients exactly at degrees {128,7,2,1,0}. *)
let GHASH_POLY_COEFF_AT_0_1_2_7_128 = prove(
  `!m. ghash_poly m <=> (m:1->num) one IN {128,7,2,1,0}`,
  GEN_TAC THEN REWRITE_TAC[ghash_poly; IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[RING_SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[POLY_VARPOW_BOOL_POLY; BOOL_POLY_ADD_POINTWISE; BOOL_POLY_ZERO_ALL_COEFFS_FALSE] THEN
  SIMP_TAC[RING_ADD_RZERO; POLY_VARPOW_BOOL_POLY; BOOL_POLY_ADD_POINTWISE] THEN
  SUBGOAL_THEN `!n. n < 256 ==> (ring_pow bool_poly (poly_var bool_ring one) n m <=> (m:1->num) one = n)`
    (fun th ->
      REWRITE_TAC[MATCH_MP th (ARITH_RULE `128 < 256`);
                  MATCH_MP th (ARITH_RULE `7 < 256`);
                  MATCH_MP th (ARITH_RULE `2 < 256`);
                  MATCH_MP th (ARITH_RULE `1 < 256`);
                  MATCH_MP th (ARITH_RULE `0 < 256`)]) THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(SPEC `n:num` BOOL_POLY_POW_COEFF) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  MAP_EVERY ASM_CASES_TAC [`(m:1->num) one = 128`; `(m:1->num) one = 7`;
    `(m:1->num) one = 2`; `(m:1->num) one = 1`; `(m:1->num) one = 0`] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* Decompose P(x) = x^128 + poly(0x87), separating the leading term. *)
let GHASH_POLY_EQ_X128_PLUS_POLY87 = prove(
  `ghash_poly = ring_add bool_poly
    (ring_pow bool_poly (poly_var bool_ring one) 128)
    (poly_of_word (word 135:int128))`,
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC[GHASH_POLY_COEFF_AT_0_1_2_7_128; BOOL_POLY_ADD_POINTWISE; poly_of_word;
              IN_INSERT; NOT_IN_EMPTY] THEN
  MP_TAC(SPEC `128` BOOL_POLY_POW_COEFF) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[BIT_WORD; DIMINDEX_128] THEN
  ASM_CASES_TAC `(x:1->num) one = 128` THEN ASM_REWRITE_TAC[ARITH] THEN
  ASM_CASES_TAC `(x:1->num) one < 128` THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY (fun k ->
      ASM_CASES_TAC (mk_eq(`(x:1->num) one`, mk_small_numeral k)) THENL
       [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC])
      [0;1;2;7] THEN
    SUBGOAL_THEN `~ODD(135 DIV 2 EXP ((x:1->num) one))` (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY (fun k ->
        ASM_CASES_TAC (mk_eq(`(x:1->num) one`, mk_small_numeral k)) THENL
         [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC])
        [3;4;5;6] THEN
      REWRITE_TAC[NOT_ODD] THEN
      SUBGOAL_THEN `135 DIV 2 EXP ((x:1->num) one) = 0` (fun th -> REWRITE_TAC[th; EVEN]) THEN
      MATCH_MP_TAC DIV_LT THEN
      TRANS_TAC LTE_TRANS `2 EXP 8` THEN
      CONJ_TAC THENL [ARITH_TAC; REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
      ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* The machine word 2 (= bit 1 set) represents the polynomial x.
   Connects the concrete word to HOL Light's abstract poly_var. *)
let POLY_OF_WORD2_EQ_POLY_VAR = prove(
  `poly_of_word(word 2 : int128) = poly_var bool_ring one`,
  REWRITE_TAC[FUN_EQ_THM; poly_of_word; poly_var; monomial_var; BOOL_RING] THEN
  X_GEN_TAC `m:1->num` THEN
  SUBGOAL_THEN `(!(x:1). m x = (if x = one then 1 else 0)) <=> (m one = 1)`
    SUBST1_TAC THENL
   [EQ_TAC THENL
     [DISCH_THEN(MP_TAC o SPEC `one:1`) THEN REWRITE_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC one_INDUCT THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[BIT_WORD; DIMINDEX_128] THEN
    COND_CASES_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[] THEN
    ASM_CASES_TAC `(m:1->num) one = 0` THENL
     [ASM_REWRITE_TAC[ARITH] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    ASM_CASES_TAC `(m:1->num) one < 128` THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[NOT_ODD] THEN
      SUBGOAL_THEN `2 DIV 2 EXP ((m:1->num) one) = 0` SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP 2` THEN
        CONJ_TAC THENL [ARITH_TAC; REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
        REWRITE_TAC[EVEN]];
      ASM_REWRITE_TAC[]]]);;

(* ---- poly_revn identities for the P<->Q bridge ---- *)

(* poly_revn d p: reverse the coefficients of polynomial p up to degree d.
   Coefficient n of (poly_revn d p) = coefficient (d-n) of p, for n <= d. *)
let poly_revn = new_definition
  `poly_revn (d:num) (p:(1->num)->bool) =
   (\m. if m one <= d then p (\i. d - m i) else F)`;;

(* poly_revn 126 of a 128-bit word = poly of (ushr(bitrev w) 1) *)
let POLY_REVN126_EQ_USHR_BITREV = prove(
  `!w:int128. poly_revn 126 (poly_of_word w) =
              poly_of_word(word_ushr (word_reversefields 1 w) 1 : int128)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC[poly_revn; poly_of_word] THEN
  REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_REVERSEFIELDS; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1; MOD_1; MULT_CLAUSES; ADD_CLAUSES] THEN
  ASM_CASES_TAC `(x:1->num) one <= 126` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `(x:1->num) one + 1 < 128` THENL
     [ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SPEC_TAC(`(x:1->num) one`, `n:num`) THEN ARITH_TAC;
      ASM_ARITH_TAC];
    ASM_CASES_TAC `(x:1->num) one + 1 < 128` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

(* x * poly_revn 126(poly w) = poly(bitrev w) when MSB is 0 *)
let POLY_VAR_MUL_REVN126_EQ_BITREV = prove(
  `!w:int128. ~bit 127 w ==>
    ring_mul bool_poly (poly_var bool_ring one)
      (poly_of_word(word_ushr (word_reversefields 1 w) 1 : int128)) =
    poly_of_word(word_reversefields 1 w : int128)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM POLY_OF_WORD2_EQ_POLY_VAR; GSYM POLY_OF_WORD_PMUL_2N] THEN
  REWRITE_TAC[FUN_EQ_THM; poly_of_word] THEN GEN_TAC THEN
  ABBREV_TAC `n = (x:1->num) one` THEN
  REWRITE_TAC[BIT_WORD_PMUL; DIMINDEX_256; DIMINDEX_128] THEN
  ASM_CASES_TAC `n < 256` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `!i. bit i (word 2:int128) <=> (i = 1)` (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[BIT_WORD; DIMINDEX_128] THEN
      ASM_CASES_TAC `i = 1` THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      ASM_CASES_TAC `i = 0` THENL [ASM_REWRITE_TAC[ARITH] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      ASM_CASES_TAC `i < 128` THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[NOT_ODD] THEN
        SUBGOAL_THEN `2 DIV 2 EXP i = 0` (fun th -> REWRITE_TAC[th; EVEN]) THEN
        MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP 2` THEN
        CONJ_TAC THENL [ARITH_TAC; REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
        ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    SUBGOAL_THEN `!i. bitval(i = 1) * bitval(bit (n - i) (word_ushr(word_reversefields 1 (w:int128)) 1:int128)) =
                      if i = 1 then bitval(bit (n - 1) (word_ushr(word_reversefields 1 w) 1:int128)) else 0`
      (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NSUM_DELTA; IN_NUMSEG] THEN
    ASM_CASES_TAC `1 <= n` THENL
     [ASM_REWRITE_TAC[ARITH_RULE `0 <= 1`; ODD_BITVAL] THEN
      REWRITE_TAC[BIT_WORD_USHR; DIMINDEX_128] THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> n - 1 + 1 = n`] THEN
      ASM_CASES_TAC `n < 128` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[BIT_TRIVIAL; DIMINDEX_128] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[ARITH_RULE `~(1 <= n) ==> n = 0`] THEN
      REWRITE_TAC[ODD; BIT_WORD_REVERSEFIELDS; DIMINDEX_128] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1; MOD_1; MULT_CLAUSES; ADD_CLAUSES] THEN ASM_MESON_TAC[]];
    MATCH_MP_TAC(MESON[BIT_TRIVIAL] `dimindex(:128) <= n ==> ~bit n (w:int128)`) THEN
    REWRITE_TAC[DIMINDEX_128] THEN ASM_ARITH_TAC]);;

(* poly_revn 254 of word shifted left by 128 = poly_revn 126 *)
let POLY_REVN254_OF_SHL128_EQ_REVN126 = prove(
  `!w:int128. poly_revn 254 (poly_of_word(word_shl (word_zx w : 256 word) 128)) =
              poly_revn 126 (poly_of_word w)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:1->num` THEN
  REWRITE_TAC[poly_revn; poly_of_word] THEN
  ASM_CASES_TAC `(m:1->num) one <= 126` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(m:1->num) one <= 254` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[BIT_WORD_SHL; BIT_WORD_ZX; DIMINDEX_256; DIMINDEX_128] THEN
    ASM_SIMP_TAC[ARITH_RULE `n <= 126 ==> 128 <= 254 - n`] THEN
    ASM_SIMP_TAC[ARITH_RULE `n <= 126 ==> 254 - n - 128 < 128`] THEN
    ASM_SIMP_TAC[ARITH_RULE `n <= 126 ==> 254 - n - 128 = 126 - n`] THEN
    SUBGOAL_THEN `254 - (m:1->num) one < 256 /\ 126 - m one < 256` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ASM_CASES_TAC `(m:1->num) one <= 254` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[BIT_WORD_SHL; DIMINDEX_256] THEN
    ASM_CASES_TAC `128 <= 254 - (m:1->num) one` THENL
     [REWRITE_TAC[BIT_WORD_ZX; DIMINDEX_256; DIMINDEX_128] THEN
      SUBGOAL_THEN `~(254 - (m:1->num) one - 128 < 128)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* GHASH-POLYVAL reflection equivalence                                      *)
(*                                                                           *)
(* Proves that bit-reversing a GHASH reduction (mod P(x)) gives the same     *)
(* result as POLYVAL reduction (mod Q(x)) with bit-reversed inputs.          *)
(* The key mathematical insight: poly_revn 254 maps ideal{P} to ideal{Q}.    *)
(* ========================================================================= *)

(* ---- Lemmas for the reflection equivalence                               *)

(* poly_revn distributes over ring_add *)
let POLY_REVN_ADD = prove(
  `!d p q. poly_revn d (ring_add bool_poly p q) =
           ring_add bool_poly (poly_revn d p) (poly_revn d q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; poly_revn; BOOL_POLY_ADD_POINTWISE] THEN
  GEN_TAC THEN ASM_CASES_TAC `(x:1->num) one <= d` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BOOL_POLY_ADD_POINTWISE]);;

(* Bits at position >= 128 are always false for 128-bit words. *)
let BIT_TRVL_128 = prove(
  `!i (w:int128). 128 <= i ==> ~bit i w`,
  SIMP_TAC[BIT_TRIVIAL; DIMINDEX_128]);;

(* poly_revn 254 of poly_of_word at 128 bits *)
let POLY_REVN_254_WORD128 = prove(
  `!w:int128. poly_revn 254 (poly_of_word w) =
              poly_of_word(word_shl (word_zx (word_reversefields 1 w) : 256 word) 127)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; poly_revn; poly_of_word] THEN GEN_TAC THEN
  ASM_CASES_TAC `(x:1->num) one <= 254` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[BIT_WORD_SHL; BIT_WORD_ZX; BIT_WORD_REVERSEFIELDS;
                DIMINDEX_256; DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_1; MOD_1; MULT_CLAUSES; ADD_CLAUSES] THEN
    SUBGOAL_THEN `(\i':1. 254 - x i') one = 254 - (x:1->num) one` SUBST1_TAC THENL
     [CONV_TAC(LAND_CONV BETA_CONV) THEN REFL_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `127 <= (x:1->num) one` THENL
     [ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[ARITH_RULE `127 <= n /\ n <= 254 ==> n - 127 < 128 /\ n - 127 < 256`] THEN
      SUBGOAL_THEN `(x:1->num) one < 256` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `128 <= 254 - (x:1->num) one` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`254 - (x:1->num) one`; `w:int128`] BIT_TRVL_128) THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[BIT_WORD_SHL; BIT_WORD_ZX; BIT_WORD_REVERSEFIELDS; DIMINDEX_256; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1; MOD_1; MULT_CLAUSES; ADD_CLAUSES] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    TRY(MP_TAC(SPECL [`(x:1->num) one - 127`; `word_reversefields 1 (w:int128):int128`] BIT_TRVL_128) THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC) THEN
    ASM_ARITH_TAC]);;

(* bit i (w:int128) implies i < 128 *)
let BIT_LESST_128 = prove(
  `!i (w:int128). bit i w ==> i < 128`,
  MESON_TAC[BIT_GUARD; DIMINDEX_128]);;

(* CARD equality for carry-less product bit reversal via bijection j <-> 127-j *)
let CARD_PMUL_BITREV = prove(
  `!(a:int128) (b:int128) k. k <= 254 ==>
    CARD {i | i <= 254 - k /\ bit i a /\ bit (254 - k - i) b} =
    CARD {j | j <= k /\ bit j (word_reversefields 1 a) /\ bit (k - j) (word_reversefields 1 b)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN
  EXISTS_TAC `\j:num. 127 - j` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j <= k}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LE; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `j < 128` ASSUME_TAC THENL [ASM_MESON_TAC[BIT_LESST_128]; ALL_TAC] THEN
    SUBGOAL_THEN `k - j < 128` ASSUME_TAC THENL [ASM_MESON_TAC[BIT_LESST_128]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `bit j (word_reversefields 1 (a:int128))` THEN
    UNDISCH_TAC `bit (k - j) (word_reversefields 1 (b:int128))` THEN
    REWRITE_TAC[BIT_REVERSEFIELDS_1; DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1; MOD_1; MULT_CLAUSES; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `127 - (127 - j) = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `254 - k - (127 - j) = 127 - (k - j)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `i < 128` ASSUME_TAC THENL [ASM_MESON_TAC[BIT_LESST_128]; ALL_TAC] THEN
    SUBGOAL_THEN `254 - k - i < 128` ASSUME_TAC THENL [ASM_MESON_TAC[BIT_LESST_128]; ALL_TAC] THEN
    SUBGOAL_THEN `k + i < 255` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXISTS_UNIQUE] THEN
    EXISTS_TAC `127 - i` THEN CONJ_TAC THENL
     [CONJ_TAC THENL
       [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `bit i (a:int128)` THEN
          REWRITE_TAC[BIT_REVERSEFIELDS_1; DIMINDEX_128] THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1; MOD_1; MULT_CLAUSES; ADD_CLAUSES] THEN
          ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> 127 - i < 128`] THEN
          SUBGOAL_THEN `127 - (127 - i) = i` SUBST1_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
          UNDISCH_TAC `bit (254 - k - i) (b:int128)` THEN
          REWRITE_TAC[BIT_REVERSEFIELDS_1; DIMINDEX_128] THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1; MOD_1; MULT_CLAUSES; ADD_CLAUSES] THEN
          ASM_SIMP_TAC[ARITH_RULE `k + i < 255 /\ i < 128 ==> k - (127 - i) < 128`] THEN
          SUBGOAL_THEN `127 - (k - (127 - i)) = 254 - k - i` SUBST1_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
        ASM_ARITH_TAC];
      GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `y < 128` ASSUME_TAC THENL [ASM_MESON_TAC[BIT_LESST_128]; ALL_TAC] THEN
      ASM_ARITH_TAC]]);;

(* Bit-reversing both inputs of word_pmul reverses the product's coefficients. *)
let POLY_REVN_254_PMUL = prove(
  `!(a:int128) (b:int128).
    poly_revn 254 (poly_of_word(word_pmul a b : 256 word)) =
    poly_of_word(word_pmul (word_reversefields 1 a) (word_reversefields 1 b) : 256 word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; poly_revn; poly_of_word] THEN
  GEN_TAC THEN ASM_CASES_TAC `(x:1->num) one <= 254` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[BIT_WORD_PMUL_ALT; DIMINDEX_256] THEN
    SUBGOAL_THEN `(x:1->num) one < 256 /\ 254 - x one < 256` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CARD_PMUL_BITREV THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[BIT_WORD_PMUL_ALT; DIMINDEX_256] THEN
    ASM_CASES_TAC `(x:1->num) one < 256` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[ODD; CARD_CLAUSES] `s = {} ==> ~ODD(CARD s)`) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `x' < 128` ASSUME_TAC THENL [ASM_MESON_TAC[BIT_LESST_128]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:1->num) one - x' < 128` ASSUME_TAC THENL [ASM_MESON_TAC[BIT_LESST_128]; ALL_TAC] THEN
    ASM_ARITH_TAC]);;

(* Decompose Q(x) = 1 + x * poly(bitrev 0x87), used for the ideal mapping. *)
let Q_AS_ONE_PLUS_U_REV_LOW = prove(
  `polyval_poly = ring_add bool_poly (ring_1 bool_poly)
    (ring_mul bool_poly (poly_var bool_ring one)
      (poly_of_word(word_reversefields 1 (word 135:int128))))`,
  SUBGOAL_THEN `128 < dimindex(:256)` ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_256] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP POLYVAL_POLY_OF_WORD (ASSUME `128 < dimindex(:256)`)) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM(INST_TYPE[`:256`,`:N`] POLY_OF_WORD_1)] THEN
  REWRITE_TAC[GSYM POLY_OF_WORD2_EQ_POLY_VAR] THEN
  REWRITE_TAC[GSYM POLY_OF_WORD_PMUL_2N] THEN
  ONCE_REWRITE_TAC[WORD_PMUL_SYM] THEN REWRITE_TAC[PMUL_2_AS_SHL] THEN
  REWRITE_TAC[GSYM POLY_OF_WORD_XOR] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_REDUCE_CONV);;

(* GHASH_REDUCE1_HI: formula for the high bits after one reduction pass *)
let GHASH_REDUCE1_HI = prove(
  `!(hi:int128) (lo:int128).
    word_ushr (ghash_reduce1 (word_join hi lo : 256 word)) 128 =
    word_zx(word_xor (word_ushr hi 121)
      (word_xor (word_ushr hi 126) (word_ushr hi 127))) : 256 word`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ghash_reduce1] THEN
  SUBGOAL_THEN `word_ushr (word_join (hi:int128) (lo:int128) : 256 word) 128 = word_zx hi : 256 word`
    SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN `word_subword (word_join (hi:int128) (lo:int128) : 256 word) (0,128) = word_zx lo : 256 word`
    SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr (word_xor (word_zx (lo:int128) : 256 word) (word_pmul (word_zx hi : 256 word) (word 135 : 256 word))) 128 = word_ushr (word_pmul (word_zx (hi:int128) : 256 word) (word 135 : 256 word)) 128`
    SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_zx (hi:int128) : 256 word) (word 135 : 256 word) =
    word_xor (word_xor (word_shl (word_zx hi : 256 word) 7) (word_shl (word_zx hi : 256 word) 2))
             (word_xor (word_shl (word_zx hi : 256 word) 1) (word_zx hi : 256 word))`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `word 135 : 256 word = word_xor (word_xor (word(2 EXP 7)) (word(2 EXP 2))) (word_xor (word(2 EXP 1)) (word(2 EXP 0))) : 256 word`
      SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[WORD_PMUL_XOR; CONJUNCT2 WORD_PMUL_POW2] THEN
    SIMP_TAC[WORD_SHL_ZERO]; ALL_TAC] THEN
  CONV_TAC WORD_BLAST);;

(* ---- Helper lemmas for type 1 and bit-level word operations ------------- *)

(* Functions from the unit type 1 are equal iff they agree at one. *)
let ONE_FUN_EQ = prove(
  `!(f:1->A) (g:1->A). f = g <=> f one = g one`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    MATCH_MP_TAC one_INDUCT THEN ASM_REWRITE_TAC[]]);;

(* Right-shifting a 256-bit word by 128 = zero-extending the upper 128 bits. *)
let WORD_USHR_128_AS_ZX_SUBWORD = prove(
  `!x:256 word. word_ushr x 128 = word_zx(word_subword x (128,128) : int128) : 256 word`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* A 256-bit word = join of its upper and lower 128-bit halves. *)
let WORD_JOIN_SUBWORDS_256 = prove(
  `!x:256 word. x = word_join(word_subword x (128,128):int128)(word_subword x (0,128):int128)`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_JOIN; BIT_WORD_SUBWORD;
                            DIMINDEX_256; DIMINDEX_128; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN GEN_TAC THEN DISCH_TAC THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[ARITH_RULE `~(i < 128) /\ i < 256 ==> i - 128 < 128 /\ 128 + (i - 128) = i`]]);;

(* ---- poly(w) * x^128 = poly(shl(zx w) 128) ----------------------------- *)

(* 128 <= 256: needed for word_zx lemmas between int128 and 256-bit words. *)
let dimindex_le_128_256 = prove(`dimindex(:128) <= dimindex(:256)`,
  REWRITE_TAC[DIMINDEX_128; DIMINDEX_256] THEN ARITH_TAC);;

(* poly(w) * x^128 = poly(shl(zx w : 256) 128): polynomial multiply by
   x^128 corresponds to shifting the 128-bit word into the upper half. *)
let MUL_U128_WORD = prove(
  `!w:int128. ring_mul bool_poly (poly_of_word w)
              (ring_pow bool_poly (poly_var bool_ring one) 128) =
              poly_of_word(word_shl (word_zx w : 256 word) 128)`,
  GEN_TAC THEN REWRITE_TAC[GSYM POLY_OF_WORD_ZX_128_256] THEN
  SUBGOAL_THEN `ring_pow bool_poly (poly_var bool_ring one) 128 =
                poly_of_word(word(2 EXP 128) : 256 word)` SUBST1_TAC THENL
   [MP_TAC(SPEC `128` (INST_TYPE [`:256`, `:N`] POLY_VAR_POW_OF_WORD)) THEN
    REWRITE_TAC[DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[GSYM POLY_OF_WORD_PMUL_2N] THEN
  REWRITE_TAC[FUN_EQ_THM; poly_of_word] THEN X_GEN_TAC `m:1->num` THEN
  REWRITE_TAC[BIT_WORD_PMUL_ALT; BIT_WORD_SHL; BIT_WORD_ZX;
              DIMINDEX_512; DIMINDEX_256; DIMINDEX_128] THEN
  SUBGOAL_THEN `!k. bit k (word(2 EXP 128) : 256 word) <=> (k = 128)`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[BIT_WORD; DIMINDEX_256] THEN
    EQ_TAC THEN STRIP_TAC THENL
     [UNDISCH_TAC `ODD(2 EXP 128 DIV 2 EXP k)` THEN
      ASM_CASES_TAC `k = 128` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `k < 128` THENL
       [ASM_SIMP_TAC[DIV_EXP; ARITH_RULE `~(2=0)`; ARITH_RULE `k<128 ==> k<=128`] THEN
        REWRITE_TAC[ODD_EXP] THEN ASM_ARITH_TAC;
        SUBGOAL_THEN `2 EXP 128 DIV 2 EXP k = 0` (fun th -> REWRITE_TAC[th; ODD]) THEN
        MATCH_MP_TAC DIV_LT THEN REWRITE_TAC[LT_EXP] THEN ASM_ARITH_TAC];
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
  ABBREV_TAC `n = (m:1->num) one` THEN
  SUBGOAL_THEN `!j. 128 <= j ==> ~bit j (w:int128)` ASSUME_TAC THENL
   [SIMP_TAC[BIT_TRIVIAL; DIMINDEX_128]; ALL_TAC] THEN
  ASM_CASES_TAC `128 <= n` THENL
   [ASM_CASES_TAC `n < 256` THENL
     [ASM_CASES_TAC `bit (n - 128) (w:int128)` THENL
       [SUBGOAL_THEN `{i | i <= n /\ (i < 256 /\ bit i (w:int128)) /\ n - i = 128} = {n - 128}`
          SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN GEN_TAC THEN
          EQ_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
          REWRITE_TAC[CARD_SING] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
        SUBGOAL_THEN `{i | i <= n /\ (i < 256 /\ bit i (w:int128)) /\ n - i = 128} = {}`
          SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN GEN_TAC THEN
          STRIP_TAC THEN SUBGOAL_THEN `x = n - 128` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]];
          REWRITE_TAC[CARD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]];
      SUBGOAL_THEN `~bit (n - 128) (w:int128)` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `{i | i <= n /\ (i < 256 /\ bit i (w:int128)) /\ n - i = 128} = {}`
        SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN GEN_TAC THEN
        STRIP_TAC THEN SUBGOAL_THEN `x = n - 128` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]];
        REWRITE_TAC[CARD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]];
    SUBGOAL_THEN `{i | i <= n /\ (i < 256 /\ bit i (w:int128)) /\ n - i = 128} = {}`
      SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN GEN_TAC THEN STRIP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[CARD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]]);;

(* ---- Key lemma: poly_revn 254(k * P) = poly_revn 126(k) * Q ----------- *)

(* The ideal mapping lemma: poly_revn 254(k * P) = poly_revn 126(k) * Q.
   Reversing coefficients maps multiples of P to multiples of Q. *)
let POLY_REVN_MUL_GHASH = prove(
  `!w:int128. ~bit 127 w ==>
    poly_revn 254 (ring_mul bool_poly (poly_of_word w) ghash_poly) =
    ring_mul bool_poly (poly_revn 126 (poly_of_word w)) polyval_poly`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GHASH_POLY_EQ_X128_PLUS_POLY87] THEN
  SIMP_TAC[RING_ADD_LDISTRIB; BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY] THEN
  REWRITE_TAC[MUL_U128_WORD] THEN
  REWRITE_TAC[GSYM POLY_OF_WORD_PMUL_2N] THEN
  REWRITE_TAC[POLY_REVN_ADD; POLY_REVN254_OF_SHL128_EQ_REVN126; POLY_REVN_254_PMUL;
              POLY_OF_WORD_PMUL_2N] THEN
  REWRITE_TAC[Q_AS_ONE_PLUS_U_REV_LOW; POLY_REVN126_EQ_USHR_BITREV] THEN
  ABBREV_TAC `r = poly_of_word(word_ushr(word_reversefields 1 (w:int128)) 1:int128)` THEN
  ABBREV_TAC `c = poly_of_word(word_reversefields 1 (word 135:int128):int128)` THEN
  ABBREV_TAC `b = poly_of_word(word_reversefields 1 (w:int128):int128)` THEN
  SUBGOAL_THEN `r IN ring_carrier bool_poly /\ c IN ring_carrier bool_poly /\ b IN ring_carrier bool_poly /\ (poly_var bool_ring one) IN ring_carrier bool_poly`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r"; "c"; "b"] THEN REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VAR_IN_BOOL_POLY]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_mul bool_poly (poly_var bool_ring one) r = b` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r"; "b"] THEN MATCH_MP_TAC POLY_VAR_MUL_REVN126_EQ_BITREV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_mul bool_poly r (ring_add bool_poly (ring_1 bool_poly) (ring_mul bool_poly (poly_var bool_ring one) c)) =
                ring_add bool_poly r (ring_mul bool_poly b c)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[RING_ADD_LDISTRIB; RING_1; RING_MUL; RING_MUL_RID] THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `ring_mul bool_poly r (ring_mul bool_poly (poly_var bool_ring one) c) =
                  ring_mul bool_poly (ring_mul bool_poly r (poly_var bool_ring one)) c`
      SUBST1_TAC THENL [ASM_MESON_TAC[RING_MUL_ASSOC]; ALL_TAC] THEN
    SUBGOAL_THEN `ring_mul bool_poly r (poly_var bool_ring one) =
                  ring_mul bool_poly (poly_var bool_ring one) r`
      SUBST1_TAC THENL [ASM_MESON_TAC[RING_MUL_SYM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    REFL_TAC]);;

(* ---- Explicit quotient from Barrett reduction --------------------------- *)

(* bit 255 of word_pmul(a:128)(b:128):256 is always 0 (degree <= 254) *)
let BIT255_PMUL_128 = prove(
  `!(a:int128) (b:int128). ~bit 255 (word_pmul a b : 256 word)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BIT_WORD_PMUL_ALT; DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `{i | i <= 255 /\ bit i (a:int128) /\ bit (255 - i) (b:int128)} = {}`
    (fun th -> REWRITE_TAC[th; CARD_CLAUSES; ODD]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  ASM_CASES_TAC `x < 128` THENL
   [SUBGOAL_THEN `128 <= 255 - x` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`255 - x`; `b:int128`] BIT_TRVL_128) THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `128 <= x` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`x:num`; `a:int128`] BIT_TRVL_128) THEN ASM_REWRITE_TAC[]]);;

(* bit 255 of ghash_reduce1(word_pmul a b) is always 0 *)
let BIT255_REDUCE1_PMUL = prove(
  `!(a:int128) (b:int128). ~bit 255 (ghash_reduce1(word_pmul a b : 256 word) : 256 word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ghash_reduce1; BIT_WORD_XOR] THEN
  SUBGOAL_THEN `~bit 255 (word_subword(word_pmul (a:int128) (b:int128):256 word)(0,128):256 word)`
    ASSUME_TAC THENL
   [REWRITE_TAC[BIT_WORD_SUBWORD; DIMINDEX_256; DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `~bit 255 (word_pmul(word_ushr(word_pmul (a:int128) (b:int128):256 word) 128:256 word)(word 135:256 word):256 word)`
    ASSUME_TAC THENL
   [REWRITE_TAC[BIT_WORD_PMUL_ALT; BIT_WORD_USHR; BIT_WORD; DIMINDEX_256] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC(MESON[ODD; CARD_CLAUSES] `s = {} ==> ~ODD(CARD s)`) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
    UNDISCH_TAC `ODD(135 DIV 2 EXP (255 - x))` THEN
    SUBGOAL_THEN `135 DIV 2 EXP (255 - x) = 0` (fun th -> REWRITE_TAC[th; ODD]) THEN
    MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP 8` THEN
    CONJ_TAC THENL [ARITH_TAC; REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* The quotient word has degree <= 126 *)
let QUOTIENT_BIT127 = prove(
  `!(a:int128) (b:int128).
    ~bit 127 (word_xor
      (word_subword(word_pmul a b : 256 word)(128,128) : int128)
      (word_subword(ghash_reduce1(word_pmul a b : 256 word) : 256 word)(128,128) : int128))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_WORD_XOR; BIT_WORD_SUBWORD; DIMINDEX_128; DIMINDEX_256] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`a:int128`; `b:int128`] BIT255_PMUL_128) THEN
  MP_TAC(SPECL [`a:int128`; `b:int128`] BIT255_REDUCE1_PMUL) THEN
  REWRITE_TAC[] THEN MESON_TAC[]);;

(* After two reduction passes, upper 128 bits are zero *)
let USHR121_SMALL = prove(
  `!(hi:int128). word_ushr (word_xor(word_ushr hi 121)(word_xor(word_ushr hi 126)(word_ushr hi 127)):int128) 121 = word 0`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;
let USHR126_SMALL = prove(
  `!(hi:int128). word_ushr (word_xor(word_ushr hi 121)(word_xor(word_ushr hi 126)(word_ushr hi 127)):int128) 126 = word 0`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;
let USHR127_SMALL = prove(
  `!(hi:int128). word_ushr (word_xor(word_ushr hi 121)(word_xor(word_ushr hi 126)(word_ushr hi 127)):int128) 127 = word 0`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* After two passes of ghash_reduce1, the upper 128 bits are zero. *)
let R2_HIGH_ZERO = prove(
  `!(a:int128) (b:int128).
    word_ushr(ghash_reduce1(ghash_reduce1(word_pmul a b : 256 word)):256 word) 128 = word 0 : 256 word`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `T2 = word_pmul (a:int128) (b:int128) : 256 word` THEN
  ABBREV_TAC `r1 = ghash_reduce1 (T2:256 word) : 256 word` THEN
  ABBREV_TAC `hi1 = word_subword (T2:256 word) (128,128) : int128` THEN
  SUBGOAL_THEN `word_ushr (r1:256 word) 128 = word_zx(word_xor(word_ushr (hi1:int128) 121)(word_xor(word_ushr hi1 126)(word_ushr hi1 127))) : 256 word`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r1"; "hi1"] THEN
    GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV o RAND_CONV) [WORD_JOIN_SUBWORDS_256] THEN
    REWRITE_TAC[GHASH_REDUCE1_HI]; ALL_TAC] THEN
  SUBGOAL_THEN `r1:256 word = word_join(word_subword r1 (128,128):int128)(word_subword r1 (0,128):int128)` (LABEL_TAC "r1_join") THENL
   [REWRITE_TAC[WORD_JOIN_SUBWORDS_256]; ALL_TAC] THEN
  ABBREV_TAC `hi2 = word_subword (r1:256 word) (128,128) : int128` THEN
  ABBREV_TAC `lo2 = word_subword (r1:256 word) (0,128) : int128` THEN
  SUBGOAL_THEN `r1:256 word = word_join (hi2:int128) (lo2:int128)` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["hi2"; "lo2"] THEN REWRITE_TAC[GSYM WORD_JOIN_SUBWORDS_256]; ALL_TAC] THEN
  REWRITE_TAC[GHASH_REDUCE1_HI] THEN
  SUBGOAL_THEN `hi2:int128 = word_xor(word_ushr (hi1:int128) 121)(word_xor(word_ushr hi1 126)(word_ushr hi1 127))`
    SUBST1_TAC THENL
   [EXPAND_TAC "hi2" THEN
    ONCE_REWRITE_TAC[GSYM(MATCH_MP WORD_ZX_ZX dimindex_le_128_256)] THEN
    ONCE_REWRITE_TAC[GSYM WORD_USHR_128_AS_ZX_SUBWORD] THEN
    ASM_REWRITE_TAC[GHASH_REDUCE1_HI; MATCH_MP WORD_ZX_ZX dimindex_le_128_256]; ALL_TAC] THEN
  REWRITE_TAC[USHR121_SMALL; USHR126_SMALL; USHR127_SMALL] THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* poly(ghash_reduce(pmul a b)) = poly(reduce1(reduce1(pmul a b))) *)
let POLY_GHASH_REDUCE_EQ_R2 = prove(
  `!(a:int128) (b:int128).
    poly_of_word (ghash_reduce (word_pmul a b)) =
    poly_of_word (ghash_reduce1 (ghash_reduce1 (word_pmul a b : 256 word)) : 256 word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ghash_reduce] THEN
  REWRITE_TAC[FUN_EQ_THM; poly_of_word; BIT_WORD_ZX; DIMINDEX_128; DIMINDEX_256] THEN
  GEN_TAC THEN ASM_CASES_TAC `(x:1->num) one < 128` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bit ((x:1->num) one) (ghash_reduce1(ghash_reduce1(word_pmul (a:int128) (b:int128):256 word)):256 word) <=>
                bit (x one - 128) (word_ushr(ghash_reduce1(ghash_reduce1(word_pmul a b:256 word)):256 word) 128 : 256 word)`
    SUBST1_TAC THENL
   [REWRITE_TAC[BIT_WORD_USHR; DIMINDEX_256] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(i < 128) ==> i - 128 + 128 = i`] THEN
    ASM_CASES_TAC `(x:1->num) one < 256` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[BIT_TRIVIAL; DIMINDEX_256] THEN ASM_ARITH_TAC;
    REWRITE_TAC[R2_HIGH_ZERO; BIT_WORD_0]]);;

(* ---- Reduce1 explicit quotient + two-pass combination ------------------- *)

(* Helper: word_pmul bit access is the same regardless of word 135 type (128 vs 256) *)
let PMUL_135_BIT_NORMALIZE = prove(
  `!x:256 word. !k. bit k (word_pmul (word_subword x (128,128) : int128) (word 135 : 256 word) : 256 word) <=>
                    bit k (word_pmul (word_subword x (128,128) : int128) (word 135 : int128) : 256 word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_WORD_PMUL_ALT; DIMINDEX_256; DIMINDEX_128] THEN
  ASM_CASES_TAC `k < 256` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; BIT_WORD; DIMINDEX_256; DIMINDEX_128] THEN
  GEN_TAC THEN ASM_CASES_TAC `(k - x'):num < 128` THENL
   [ASM_SIMP_TAC[ARITH_RULE `n < 128 ==> n < 256`];
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `(k - x'):num < 256` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `135 DIV 2 EXP (k - x') = 0` (fun th -> REWRITE_TAC[th; ODD]) THEN
    MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP 8` THEN
    CONJ_TAC THENL [ARITH_TAC; REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC]]);;

(* One pass of ghash_reduce1: poly(x) + poly(reduce1(x)) = poly(upper_128_bits) * P.
   The quotient is the upper 128 bits of the input. *)
let REDUCE1_QUOTIENT = prove(
  `!x:256 word.
    ring_add bool_poly (poly_of_word x) (poly_of_word(ghash_reduce1 x)) =
    ring_mul bool_poly (poly_of_word(word_subword x (128,128) : int128)) ghash_poly`,
  GEN_TAC THEN
  REWRITE_TAC[ghash_reduce1; POLY_OF_WORD_XOR; GHASH_POLY_EQ_X128_PLUS_POLY87] THEN
  SIMP_TAC[RING_ADD_LDISTRIB; BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY] THEN
  REWRITE_TAC[MUL_U128_WORD; GSYM POLY_OF_WORD_PMUL_2N; WORD_USHR_128_AS_ZX_SUBWORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV(GEN_REWRITE_CONV I [MATCH_MP WORD_ZX_WORD_SIMPLE dimindex_le_128_256])) THEN
  REWRITE_TAC[WORD_PMUL_ZX] THEN
  REWRITE_TAC[FUN_EQ_THM; BOOL_POLY_ADD_POINTWISE; poly_of_word; BIT_WORD_SUBWORD;
              BIT_WORD_SHL; BIT_WORD_ZX; DIMINDEX_256; DIMINDEX_128; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `128 + n = n + 128`] THEN REWRITE_TAC[ADD_SUB] THEN
  ASM_CASES_TAC `128 <= (x':1->num) one` THENL
   [ASM_SIMP_TAC[ARITH_RULE `128 <= n ==> ~(n < 128) /\ n - 128 + 128 = n`] THEN
    ASM_CASES_TAC `(x':1->num) one < 256` THENL
     [SUBGOAL_THEN `(x':1->num) one - 128 < 128 /\ (x':1->num) one - 128 < 256`
        STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[PMUL_135_BIT_NORMALIZE]];
      SUBGOAL_THEN `~bit ((x':1->num) one) (x:256 word)` (fun th -> REWRITE_TAC[th]) THENL
       [MP_TAC(ISPECL [`x:256 word`; `(x':1->num) one`] BIT_TRIVIAL) THEN
        REWRITE_TAC[DIMINDEX_256] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[PMUL_135_BIT_NORMALIZE]];
    SUBGOAL_THEN `(x':1->num) one < 128` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[TAUT `!a p. ~(a <=> ~(a <=> p)) <=> p`; PMUL_135_BIT_NORMALIZE]]);;

(* Two-pass quotient: poly(T) + poly(ghash_reduce T) = poly(w) * P *)
let REDUCE_SUM_EQ_QUOTIENT_MUL = prove(
  `!(a:int128) (b:int128).
    ring_add bool_poly (poly_of_word(word_pmul a b : 256 word))
                       (poly_of_word(ghash_reduce(word_pmul a b) : int128)) =
    ring_mul bool_poly
      (poly_of_word(word_xor (word_subword(word_pmul a b : 256 word)(128,128) : int128)
                              (word_subword(ghash_reduce1(word_pmul a b : 256 word) : 256 word)(128,128) : int128)))
      ghash_poly`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INST_TYPE [`:128`,`:M`; `:128`,`:N`] POLY_GHASH_REDUCE_EQ_R2] THEN
  ABBREV_TAC `T2 = word_pmul (a:int128) (b:int128) : 256 word` THEN
  ABBREV_TAC `r1 = ghash_reduce1(T2:256 word) : 256 word` THEN
  MP_TAC(SPEC `T2:256 word` REDUCE1_QUOTIENT) THEN
  MP_TAC(SPEC `r1:256 word` REDUCE1_QUOTIENT) THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `ring_add bool_poly (poly_of_word (T2:256 word)) (poly_of_word(ghash_reduce1 (r1:256 word) : 256 word)) =
     ring_add bool_poly
       (ring_mul bool_poly (poly_of_word(word_subword T2 (128,128):int128)) ghash_poly)
       (ring_mul bool_poly (poly_of_word(word_subword r1 (128,128):int128)) ghash_poly)`
    MP_TAC THENL
   [SUBGOAL_THEN
      `ring_add bool_poly (poly_of_word (T2:256 word)) (poly_of_word(ghash_reduce1 (r1:256 word))) =
       ring_add bool_poly
         (ring_add bool_poly (poly_of_word T2) (poly_of_word r1))
         (ring_add bool_poly (poly_of_word r1) (poly_of_word(ghash_reduce1 r1)))`
      SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; BOOL_POLY_ADD_POINTWISE] THEN GEN_TAC THEN CONV_TAC TAUT;
      ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[GSYM POLY_OF_WORD_XOR; GSYM RING_ADD_RDISTRIB; GHASH_BOOL_POLY;
              BOOL_POLY_OF_WORD] THEN
  EXPAND_TAC "r1" THEN REWRITE_TAC[] THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[POLY_OF_WORD_XOR];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[POLY_OF_WORD_XOR; GSYM RING_ADD_RDISTRIB; GHASH_BOOL_POLY; BOOL_POLY_OF_WORD] THEN
    SIMP_TAC[RING_ADD_RDISTRIB; GHASH_BOOL_POLY; BOOL_POLY_OF_WORD]]);;

(* ---- poly_revn 254 maps ideal{P} to ideal{Q} for our specific d -------- *)

(* Helper for word_pmul type normalization at 2^127 *)
let PMUL_2EXP127_BIT_NORMALIZE = prove(
  `!w:int128. !k. bit k (word_pmul (word_zx w : 256 word) (word(2 EXP 127) : 256 word) : 512 word) <=>
                  bit k (word_shl (word_zx w : 256 word) 127 : 256 word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_WORD_PMUL_ALT; BIT_WORD_SHL; BIT_WORD_ZX;
              DIMINDEX_512; DIMINDEX_256; DIMINDEX_128] THEN
  SUBGOAL_THEN `!j. bit j (word(2 EXP 127) : 256 word) <=> (j = 127)` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[BIT_WORD; DIMINDEX_256] THEN EQ_TAC THEN STRIP_TAC THENL
     [UNDISCH_TAC `ODD(2 EXP 127 DIV 2 EXP j)` THEN ASM_CASES_TAC `j = 127` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `j < 127` THENL
       [ASM_SIMP_TAC[DIV_EXP; ARITH_RULE `~(2=0)`; ARITH_RULE `j<127 ==> j<=127`] THEN REWRITE_TAC[ODD_EXP] THEN ASM_ARITH_TAC;
        SUBGOAL_THEN `2 EXP 127 DIV 2 EXP j = 0` (fun th -> REWRITE_TAC[th; ODD]) THEN MATCH_MP_TAC DIV_LT THEN REWRITE_TAC[LT_EXP] THEN ASM_ARITH_TAC];
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
  ASM_CASES_TAC `k < 512` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `127 <= k` THENL
     [ASM_CASES_TAC `k < 256` THENL
       [SUBGOAL_THEN `k - 127 < 256` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `{i | i <= k /\ (i < 256 /\ bit i (w:int128)) /\ k - i = 127} =
                      if bit (k - 127) w then {k - 127} else {}`
          (fun th -> REWRITE_TAC[th]) THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING; NOT_IN_EMPTY] THEN GEN_TAC THEN
          COND_CASES_TAC THENL
           [REWRITE_TAC[IN_SING] THEN EQ_TAC THENL
             [STRIP_TAC THEN ASM_ARITH_TAC;
              DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
            REWRITE_TAC[NOT_IN_EMPTY] THEN STRIP_TAC THEN
            SUBGOAL_THEN `x = k - 127` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]]]; ALL_TAC] THEN
        COND_CASES_TAC THEN REWRITE_TAC[CARD_SING; CARD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `{i | i <= k /\ (i < 256 /\ bit i (w:int128)) /\ k - i = 127} = {}`
          (fun th -> REWRITE_TAC[th; CARD_CLAUSES; ODD]) THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN GEN_TAC THEN STRIP_TAC THEN
        SUBGOAL_THEN `128 <= x` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        MP_TAC(SPECL [`x:num`; `w:int128`] BIT_TRVL_128) THEN
        ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `{i | i <= k /\ (i < 256 /\ bit i (w:int128)) /\ k - i = 127} = {}`
        (fun th -> REWRITE_TAC[th; CARD_CLAUSES; ODD]) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN GEN_TAC THEN STRIP_TAC THEN ASM_ARITH_TAC];
    ASM_ARITH_TAC]);;

let POLY_OF_WORD_SHL_ZX_127 = prove(
  `!w:int128. poly_of_word(word_shl(word_zx w : 256 word) 127) =
              ring_mul bool_poly (poly_of_word w) (ring_pow bool_poly (poly_var bool_ring one) 127)`,
  GEN_TAC THEN REWRITE_TAC[GSYM POLY_OF_WORD_ZX_128_256] THEN
  SUBGOAL_THEN `ring_pow bool_poly (poly_var bool_ring one) 127 =
                poly_of_word(word(2 EXP 127) : 256 word)` SUBST1_TAC THENL
   [MP_TAC(SPEC `127` (INST_TYPE [`:256`, `:N`] POLY_VAR_POW_OF_WORD)) THEN
    REWRITE_TAC[DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[GSYM POLY_OF_WORD_PMUL_2N] THEN
  REWRITE_TAC[FUN_EQ_THM; poly_of_word; PMUL_2EXP127_BIT_NORMALIZE]);;

let POLY_REVN_254_AS_MUL = prove(
  `!w:int128. poly_revn 254 (poly_of_word w) =
              ring_mul bool_poly (poly_of_word(word_reversefields 1 w))
                                (ring_pow bool_poly (poly_var bool_ring one) 127)`,
  GEN_TAC THEN REWRITE_TAC[POLY_REVN_254_WORD128; POLY_OF_WORD_SHL_ZX_127]);;

(* ---- The main theorems -------------------------------------------------- *)

(* GHASH_POLYVAL_BRIDGE_CORE (GHASH_REDUCE_BITREV_CONG_MOD_POLYVAL):
   bit-reversing a GHASH reduction result, multiplied by x^127, is
   congruent to the product of bit-reversed inputs modulo Q(x). *)
let GHASH_POLYVAL_BRIDGE_CORE = prove(
  `!(a:int128) (b:int128).
    (ring_mul bool_poly
       (poly_of_word(word_reversefields 1 (ghash_reduce(word_pmul a b : 256 word)) : int128))
       (ring_pow bool_poly (poly_var bool_ring one) 127) ==
      ring_mul bool_poly (poly_of_word(word_reversefields 1 a : int128))
                         (poly_of_word(word_reversefields 1 b : int128))) (mod_polyval)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM POLY_REVN_254_AS_MUL; GSYM POLY_REVN_254_PMUL] THEN
  SUBGOAL_THEN
    `ring_add bool_poly
       (poly_revn 254 (poly_of_word(ghash_reduce(word_pmul (a:int128) (b:int128) : 256 word) : int128)))
       (poly_revn 254 (poly_of_word(word_pmul a b : 256 word))) =
     ring_mul bool_poly
       (poly_revn 126 (poly_of_word(word_xor
          (word_subword(word_pmul a b : 256 word)(128,128) : int128)
          (word_subword(ghash_reduce1(word_pmul a b : 256 word) : 256 word)(128,128) : int128))))
       polyval_poly`
    MP_TAC THENL
   [REWRITE_TAC[GSYM POLY_REVN_ADD; GSYM POLY_OF_WORD_XOR] THEN
    SUBGOAL_THEN `ring_add bool_poly (poly_of_word(ghash_reduce(word_pmul (a:int128) (b:int128) : 256 word) : int128)) (poly_of_word(word_pmul a b : 256 word)) = ring_add bool_poly (poly_of_word(word_pmul a b : 256 word)) (poly_of_word(ghash_reduce(word_pmul a b : 256 word) : int128))` SUBST1_TAC THENL
     [SIMP_TAC[RING_ADD_SYM; BOOL_POLY_OF_WORD]; ALL_TAC] THEN
    REWRITE_TAC[REDUCE_SUM_EQ_QUOTIENT_MUL] THEN
    MP_TAC(SPECL [`a:int128`; `b:int128`] QUOTIENT_BIT127) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP POLY_REVN_MUL_GHASH th]); ALL_TAC] THEN
  DISCH_TAC THEN
  REWRITE_TAC[cong] THEN REWRITE_TAC[mod_polyval] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[POLY_REVN_254_AS_MUL] THEN MATCH_MP_TAC RING_MUL THEN
    REWRITE_TAC[POLY_VARPOW_BOOL_POLY; BOOL_POLY_OF_WORD]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC RING_MUL THEN REWRITE_TAC[BOOL_POLY_OF_WORD]; ALL_TAC] THEN
  REWRITE_TAC[BOOL_POLY_SUB; POLY_REVN_254_AS_MUL] THEN
  SUBGOAL_THEN `poly_revn 254 (poly_of_word(word_pmul (a:int128) (b:int128) : 256 word)) = ring_mul bool_poly (poly_of_word(word_reversefields 1 a)) (poly_of_word(word_reversefields 1 b))` ASSUME_TAC THENL
   [REWRITE_TAC[POLY_REVN_254_PMUL; POLY_OF_WORD_PMUL_2N]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_add bool_poly
    (ring_mul bool_poly (poly_of_word(word_reversefields 1 (ghash_reduce(word_pmul (a:int128) (b:int128) : 256 word)))) (ring_pow bool_poly (poly_var bool_ring one) 127))
    (ring_mul bool_poly (poly_of_word(word_reversefields 1 a)) (poly_of_word(word_reversefields 1 b))) =
   ring_mul bool_poly (poly_revn 126 (poly_of_word(word_xor (word_subword(word_pmul a b : 256 word)(128,128) : int128) (word_subword(ghash_reduce1(word_pmul a b : 256 word) : 256 word)(128,128) : int128)))) polyval_poly`
    SUBST1_TAC THENL
   [FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th; GSYM POLY_REVN_254_AS_MUL]) THEN
    FIRST_X_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SIMP_TAC[IN_IDEAL_GENERATED_SING_EQ; POLYVAL_BOOL_POLY; ring_divides] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_MUL THEN REWRITE_TAC[POLY_REVN126_EQ_USHR_BITREV; BOOL_POLY_OF_WORD; POLYVAL_BOOL_POLY]; ALL_TAC] THEN
  EXISTS_TAC `poly_revn 126
    (poly_of_word(word_xor
       (word_subword(word_pmul (a:int128) (b:int128) : 256 word)(128,128) : int128)
       (word_subword(ghash_reduce1(word_pmul a b : 256 word) : 256 word)(128,128) : int128)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[POLY_REVN126_EQ_USHR_BITREV; BOOL_POLY_OF_WORD]; ALL_TAC] THEN
  SIMP_TAC[RING_MUL_SYM; POLYVAL_BOOL_POLY; POLY_REVN126_EQ_USHR_BITREV; BOOL_POLY_OF_WORD]);;

(* GHASH_POLYVAL_BRIDGE_RHS:
   twist(dot)*x^127 ≡ bitrev(a)*bitrev(b) (mod Q).
   Uses GHASH_TWIST_CORRECT and POLYVAL_DOT_CORRECT. *)
let GHASH_POLYVAL_BRIDGE_RHS = prove(
  `!(a:int128) (b:int128).
    (ring_mul bool_poly (poly_of_word(word_reversefields 1 a))
                        (poly_of_word(word_reversefields 1 b)) ==
     ring_mul bool_poly
       (poly_of_word(ghash_twist(polyval_dot (word_reversefields 1 a) (word_reversefields 1 b))))
       (ring_pow bool_poly (poly_var bool_ring one) 127)) (mod_polyval)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
  SUBGOAL_THEN
    `(ring_mul bool_poly
      (poly_of_word(ghash_twist(polyval_dot (word_reversefields 1 (a:int128)) (word_reversefields 1 b))))
      (ring_pow bool_poly (poly_var bool_ring one) 127) ==
     ring_mul bool_poly
      (poly_of_word(polyval_dot (word_reversefields 1 a) (word_reversefields 1 b)))
      (ring_pow bool_poly (poly_var bool_ring one) 128)) (mod_polyval)`
    MP_TAC THENL
   [MP_TAC(SPEC `polyval_dot (word_reversefields 1 (a:int128)) (word_reversefields 1 b)` GHASH_TWIST_CORRECT) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
      `(ring_mul bool_poly (poly_of_word(ghash_twist(polyval_dot (word_reversefields 1 (a:int128)) (word_reversefields 1 b))))
        (ring_pow bool_poly (poly_var bool_ring one) 127) ==
       ring_mul bool_poly (ring_mul bool_poly (poly_var bool_ring one)
         (poly_of_word(polyval_dot (word_reversefields 1 a) (word_reversefields 1 b))))
        (ring_pow bool_poly (poly_var bool_ring one) 127)) (mod_polyval)`
      MP_TAC THENL
     [MATCH_MP_TAC MOD_POLYVAL_MUL THEN
      REWRITE_TAC[MOD_POLYVAL_REFL; POLY_VARPOW_BOOL_POLY] THEN
      FIRST_X_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
      `ring_mul bool_poly (ring_mul bool_poly (poly_var bool_ring one)
        (poly_of_word(polyval_dot (word_reversefields 1 (a:int128)) (word_reversefields 1 b))))
        (ring_pow bool_poly (poly_var bool_ring one) 127) =
       ring_mul bool_poly (poly_of_word(polyval_dot (word_reversefields 1 a) (word_reversefields 1 b)))
        (ring_pow bool_poly (poly_var bool_ring one) 128)`
      SUBST1_TAC THENL
     [SUBGOAL_THEN `ring_pow bool_poly (poly_var bool_ring one) 128 =
        ring_mul bool_poly (poly_var bool_ring one) (ring_pow bool_poly (poly_var bool_ring one) 127)`
        SUBST1_TAC THENL
       [REWRITE_TAC[GSYM(CONJUNCT2 ring_pow)] THEN CONV_TAC NUM_REDUCE_CONV;
        MESON_TAC[RING_MUL_ASSOC; RING_MUL_SYM; BOOL_POLY_OF_WORD;
                  POLY_VAR_IN_BOOL_POLY; POLY_VARPOW_BOOL_POLY]]; ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
    EXISTS_TAC `ring_mul bool_poly
      (poly_of_word(polyval_dot (word_reversefields 1 (a:int128)) (word_reversefields 1 b)))
      (ring_pow bool_poly (poly_var bool_ring one) 128)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM ACCEPT_TAC;
      REWRITE_TAC[POLYVAL_DOT_CORRECT]]]);;

(* GHASH_POLYVAL_BRIDGE (GHASH_REDUCE_BITREV_EQ_POLYVAL_DOT):
   bit-reversing ghash_reduce equals ghash_twist(polyval_dot) —
   the word-level equality connecting GHASH to POLYVAL. *)
let GHASH_POLYVAL_BRIDGE = prove(
  `!(a:int128) (b:int128).
    word_reversefields 1 (ghash_reduce(word_pmul a b : 256 word)) =
    ghash_twist(polyval_dot (word_reversefields 1 a) (word_reversefields 1 b))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(SPEC `127` MOD_POLYVAL_CANCEL_VARPOW) THEN
  MP_TAC(SPECL [`a:int128`; `b:int128`] GHASH_POLYVAL_BRIDGE_CORE) THEN
  MP_TAC(SPECL [`a:int128`; `b:int128`] GHASH_POLYVAL_BRIDGE_RHS) THEN
  DISCH_THEN(fun rhs -> DISCH_THEN(fun lhs ->
    MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
    EXISTS_TAC `ring_mul bool_poly (poly_of_word(word_reversefields 1 (a:int128)))
                                   (poly_of_word(word_reversefields 1 (b:int128)))` THEN
    CONJ_TAC THENL [ACCEPT_TAC lhs; ACCEPT_TAC rhs])));;
