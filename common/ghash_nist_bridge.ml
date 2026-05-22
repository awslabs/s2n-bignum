(* ========================================================================= *)
(* NIST GHASH ↔ POLYVAL bridge (Gueron Proposition 1)                        *)
(*                                                                           *)
(* Formalizes the connection between:                                        *)
(*   - NIST SP 800-38D GHASH (bit-reflected, mod P(x)=x^128+x^7+x^2+x+1)     *)
(*   - POLYVAL (natural bit order, mod Q(x)=x^128+x^127+x^126+x^121+1)       *)
(*                                                                           *)
(* Key definitions:                                                          *)
(*   bit_reflect128 a = word_reversefields 1 a  (bit i ↦ bit 127-i)          *)
(*   nist_ghash h acc xs = ghash_polyval_acc (ghash_twist h) acc xs          *)
(*                                                                           *)
(* Key theorems:                                                             *)
(*   BIT_REFLECT128: bit-level characterization                              *)
(*   REFLECT128_INVOLUTION: self-inverse                                     *)
(*   REFLECT128_XOR: distributes over XOR                                    *)
(*   NIST_GHASH_IS_POLYVAL: bridge to ghash_polyval_acc                      *)
(* ========================================================================= *)


needs "common/polyval_ghash.ml";;

(* ========================================================================= *)
(* Step 1: Define bit-reflection on 128-bit words                            *)
(* ========================================================================= *)

let bit_reflect128 = new_definition
  `bit_reflect128 (a:int128) : int128 = word_reversefields 1 a`;;

(* bit i (bit_reflect128 a) <=> bit (127 - i) a, for i < 128                 *)
let BIT_REFLECT128 = prove
 (`!a:int128. !i. i < 128
    ==> (bit i (bit_reflect128 a) <=> bit (127 - i) a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bit_reflect128; BIT_WORD_REVERSEFIELDS] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> i < 1 * 128`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* bit_reflect128 is an involution                                           *)
let REFLECT128_INVOLUTION = prove
 (`!a:int128. bit_reflect128 (bit_reflect128 a) = a`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BIT_REFLECT128] THEN
  SUBGOAL_THEN `127 - i < 128` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[BIT_REFLECT128] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* bit_reflect128 distributes over XOR                                       *)
let REFLECT128_XOR = prove
 (`!a b:int128. bit_reflect128 (word_xor a b) =
                word_xor (bit_reflect128 a) (bit_reflect128 b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BIT_REFLECT128; BIT_WORD_XOR; DIMINDEX_128;
               ARITH_RULE `i < 128 ==> 127 - i < 128`]);;

(* bit_reflect128 of zero is zero                                            *)
let REFLECT128_0 = prove
 (`bit_reflect128 (word 0 : int128) = word 0`,
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BIT_REFLECT128; BIT_WORD_0]);;

(* ========================================================================= *)
(* Step 2: Product reversal identity and helper lemmas                       *)
(* ========================================================================= *)

(* Helper: bit index must be < 128 for 128-bit words                         *)
let BIT_LT_128 = prove
 (`!(w:int128) i. bit i w ==> i < 128`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_LT; NOT_CLAUSES] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`w:int128`; `i:num`] BIT_TRIVIAL) THEN
  REWRITE_TAC[DIMINDEX_128] THEN ASM_REWRITE_TAC[]);;

let BIT_TRIVIAL_128 = prove
 (`!(w:int128) i. 128 <= i ==> ~bit i w`,
  MESON_TAC[BIT_LT_128; NOT_LT]);;

(* Product reversal: reflecting inputs reverses the product bits.
   bit k (pmul(REF a, REF b)) = bit (254-k) (pmul(a, b)) for k <= 254.
   This is the bit-level form of REV_127(A)*REV_127(B) = REV_254(A*B). *)
let PMUL_REFLECT128 = prove
 (`!a b:int128. !k. k <= 254 ==>
    (bit k (word_pmul (bit_reflect128 a) (bit_reflect128 b) : (256)word) <=>
     bit (254 - k) (word_pmul a b : (256)word))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_PMUL_ALT] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= 254 ==> k < 256`;
               ARITH_RULE `k <= 254 ==> 254 - k < 256`] THEN
  SUBGOAL_THEN
    `CARD {i | i <= k /\ bit i (bit_reflect128 (a:int128)) /\ bit (k - i) (bit_reflect128 (b:int128))} =
     CARD {i | i <= 254 - k /\ bit i a /\ bit (254 - k - i) b}`
    (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
    `{i | i <= k /\ bit i (bit_reflect128 (a:int128)) /\ bit (k - i) (bit_reflect128 (b:int128))} =
     IMAGE (\j. 127 - j) {j | j <= 254 - k /\ bit j a /\ bit (254 - k - j) b}`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `i < 128` ASSUME_TAC THENL
       [MATCH_MP_TAC BIT_LT_128 THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `k - i < 128` ASSUME_TAC THENL
       [MATCH_MP_TAC BIT_LT_128 THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `127 - i:num` THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [MP_TAC(SPECL [`a:int128`; `i:num`] BIT_REFLECT128) THEN
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `254 - k - (127 - i) = 127 - (k - i)` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        MP_TAC(SPECL [`b:int128`; `k - i:num`] BIT_REFLECT128) THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `j < 128` ASSUME_TAC THENL
       [MATCH_MP_TAC BIT_LT_128 THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `254 - k - j < 128` ASSUME_TAC THENL
       [MATCH_MP_TAC BIT_LT_128 THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `127 - j < 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `k - (127 - j) < 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [MP_TAC(SPECL [`a:int128`; `127 - j:num`] BIT_REFLECT128) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `127 - (127 - j) = j` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
        MP_TAC(SPECL [`b:int128`; `k - (127 - j):num`] BIT_REFLECT128) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `127 - (k - (127 - j)) = 254 - k - j` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]]];
    MP_TAC(ISPECL [`\j:num. 127 - j`;
      `{j:num | j <= 254 - k /\ bit j (a:int128) /\ bit (254 - k - j) (b:int128)}`]
      CARD_IMAGE_INJ) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
        SUBGOAL_THEN `x < 128 /\ y < 128` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN MATCH_MP_TAC BIT_LT_128 THENL
           [EXISTS_TAC `a:int128`; EXISTS_TAC `a:int128`] THEN
          ASM_REWRITE_TAC[];
          ASM_ARITH_TAC];
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j <= 254 - k}` THEN
        SIMP_TAC[FINITE_NUMSEG_LE; SUBSET; IN_ELIM_THM]];
      SIMP_TAC[]]]);;

(* ========================================================================= *)
(* Step 3: Helper lemmas for the product reversal identity                   *)
(*                                                                           *)
(* The exponent bijection {128-e : e in {128,7,2,1,0}} = {128,127,126,121,0} *)
(* connects ghash_poly and polyval_poly as reciprocal polynomials.           *)
(* GHASH_POLYVAL_RING_SUM uses this to reindex ring_sum.                     *)
(* ========================================================================= *)

let GHASH_POLYVAL_EXPONENT_BIJECTION = prove(
  `IMAGE (\e. 128 - e) {128,7,2,1,0} = {128,127,126,121,0}`,
  REWRITE_TAC[IMAGE; EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:num` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `e:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `0`; EXISTS_TAC `1`; EXISTS_TAC `2`; EXISTS_TAC `7`; EXISTS_TAC `128`] THEN
    ARITH_TAC]);;

let GHASH_EXPONENT_INJ = prove(
  `!x y. x IN {128,7,2,1,0} /\ y IN {128,7,2,1,0} /\ 128 - x = 128 - y ==> x = y`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* Key ring_sum reindexing: ghash_poly exponents to polyval_poly exponents   *)
let GHASH_POLYVAL_RING_SUM = prove(
  `!n. ring_sum bool_poly {128,7,2,1,0}
         (\e. ring_pow bool_poly (poly_var bool_ring one) (n + 128 - e)) =
       ring_sum bool_poly {128,127,126,121,0}
         (\f. ring_pow bool_poly (poly_var bool_ring one) (n + f))`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`bool_poly`; `\e:num. 128 - e`;
    `\f:num. ring_pow bool_poly (poly_var bool_ring one) (n + f)`;
    `{128,7,2,1,0}`] RING_SUM_IMAGE) THEN
  REWRITE_TAC[GHASH_EXPONENT_INJ; GHASH_POLYVAL_EXPONENT_BIJECTION; o_DEF] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]));;

(* Bit helpers for the product reversal proof                                *)
let BIT_LT_127 = prove(
  `!(m:int128) i. ~bit 127 m /\ bit i m ==> i < 127`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `i < 128` ASSUME_TAC THENL
   [MATCH_MP_TAC BIT_LT_128 THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `i = 127` THENL [ASM_MESON_TAC[]; ASM_ARITH_TAC]);;

let BIT_WORD_ZX_LT127 = prove(
  `!(m:int128) i. ~bit 127 m ==>
    (bit i (word_zx m : (256)word) <=> i <= 126 /\ bit i m)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC[BIT_WORD_ZX; DIMINDEX_128; DIMINDEX_256; ARITH_RULE `128 <= 256`] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`m:int128`; `i:num`] BIT_LT_127) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let BIT_WORD_ZX_REFLECT = prove(
  `!(m:int128) i. bit i (word_zx(bit_reflect128 m) : (256)word) <=>
                  i < 128 /\ bit (127 - i) m`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bit_reflect128; BIT_WORD_ZX; DIMINDEX_128; DIMINDEX_256;
              BIT_REVERSEFIELDS_1; ARITH_RULE `128 - 1 - i = 127 - i`] THEN
  ASM_CASES_TAC `i < 128` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> i < 256`] THEN
  REWRITE_TAC[BIT_TRIVIAL; DIMINDEX_128] THEN ASM_ARITH_TAC);;

let WORD_ZX_SAME = prove(
  `!w:N word. word_zx w : N word = w`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX; LE_REFL] THEN
  SIMP_TAC[DIMINDEX_GE_1; LE_REFL; ARITH_RULE `1 <= n ==> n <= n`] THEN
  GEN_TAC THEN ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`w:N word`; `i:num`] BIT_TRIVIAL) THEN
  ASM_SIMP_TAC[NOT_LT]);;

let WORD_OF_POLY_GHASH = prove(
  `word_of_poly ghash_poly : (256)word =
   word 340282366920938463463374607431768211591`,
  MP_TAC(INST_TYPE [`:256`,`:N`] GHASH_POLY_OF_WORD) THEN
  REWRITE_TAC[DIMINDEX_256; ARITH_RULE `128 < 256`] THEN
  DISCH_THEN(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[WORD_OF_POLY_OF_WORD_GEN; WORD_ZX_SAME]);;

let WORD_OF_POLY_POLYVAL = prove(
  `word_of_poly polyval_poly : (256)word =
   word 598152598103212142806713177126155059201`,
  MP_TAC(INST_TYPE [`:256`,`:N`] POLYVAL_POLY_OF_WORD) THEN
  REWRITE_TAC[DIMINDEX_256; ARITH_RULE `128 < 256`] THEN
  DISCH_THEN(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[WORD_OF_POLY_OF_WORD_GEN; WORD_ZX_SAME]);;

let GHASH_WORD_DECOMP = prove(
  `(word 340282366920938463463374607431768211591 : (256)word) =
   word_add (word_shl (word 1 : (256)word) 128) (word 135)`,
  CONV_TAC WORD_RULE);;

let POLYVAL_WORD_DECOMP = prove(
  `(word 598152598103212142806713177126155059201 : (256)word) =
   word_add (word_add (word_add (word_shl (word 1 : (256)word) 128)
                                (word_shl (word 1 : (256)word) 127))
                      (word_add (word_shl (word 1 : (256)word) 126)
                                (word_shl (word 1 : (256)word) 121)))
            (word 1)`,
  CONV_TAC WORD_RULE);;

(* XOR decompositions of the ghash/polyval word constants (via BITBLAST)     *)
let GHASH_WORD_FULL_XOR = BITBLAST_RULE
 `word 340282366920938463463374607431768211591 : (256)word =
  word_xor (word_shl (word 1) 128)
   (word_xor (word_xor (word_shl (word 1) 7) (word_shl (word 1) 2))
             (word_xor (word_shl (word 1) 1) (word 1)))`;;

let POLYVAL_WORD_FULL_XOR = BITBLAST_RULE
 `word 598152598103212142806713177126155059201 : (256)word =
  word_xor (word_shl (word 1) 128)
   (word_xor (word_xor (word_shl (word 1) 127) (word_shl (word 1) 126))
             (word_xor (word_shl (word 1) 121) (word 1)))`;;

(* Bit characterization of single-bit shifted words                          *)
let BIT_WORD_SHL_1_256 = prove(
  `!n i. bit i (word_shl (word 1 : (256)word) n) <=> i = n /\ n < 256`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_WORD_SHL; DIMINDEX_256] THEN
  REWRITE_TAC[BIT_WORD; DIMINDEX_256] THEN
  ASM_CASES_TAC `n < 256` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `i:num = n` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[LE_REFL; SUB_REFL] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM_CASES_TAC `n:num <= i` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i < 256` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `0 < i - n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ODD] THEN
      SUBGOAL_THEN `1 DIV (2 EXP (i - n)) = 0` SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_LT THEN
        TRANS_TAC LTE_TRANS `2 EXP 1` THEN CONJ_TAC THENL
         [CONV_TAC NUM_REDUCE_CONV;
          REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
        REWRITE_TAC[ODD]]];
    ASM_CASES_TAC `i:num = n` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let BIT_WORD_1_256 = prove(
  `!i. bit i (word 1 : (256)word) <=> i = 0`,
  GEN_TAC THEN REWRITE_TAC[BIT_WORD; DIMINDEX_256] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `i < 256` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `0 < i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 DIV (2 EXP i) = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_LT THEN
    TRANS_TAC LTE_TRANS `2 EXP 1` THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
    REWRITE_TAC[ODD]]);;

(* Full bit characterizations of the ghash/polyval word constants            *)
let BIT_GHASH_WORD = prove(
  `!i. bit i (word 340282366920938463463374607431768211591 : (256)word) <=>
       i IN {128,7,2,1,0}`,
  GEN_TAC THEN REWRITE_TAC[GHASH_WORD_FULL_XOR] THEN
  REWRITE_TAC[BIT_WORD_XOR; BIT_WORD_SHL_1_256; BIT_WORD_1_256] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DIMINDEX_256] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `i < 256` THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC] THEN
  ASM_CASES_TAC `i = 128` THEN ASM_REWRITE_TAC[] THEN
  TRY(CONV_TAC NUM_REDUCE_CONV) THEN
  ASM_CASES_TAC `i = 7` THEN ASM_REWRITE_TAC[] THEN
  TRY(CONV_TAC NUM_REDUCE_CONV) THEN
  ASM_CASES_TAC `i = 2` THEN ASM_REWRITE_TAC[] THEN
  TRY(CONV_TAC NUM_REDUCE_CONV) THEN
  ASM_CASES_TAC `i = 1` THEN ASM_REWRITE_TAC[] THEN
  TRY(CONV_TAC NUM_REDUCE_CONV) THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[]);;

let BIT_POLYVAL_WORD = prove(
  `!i. bit i (word 598152598103212142806713177126155059201 : (256)word) <=>
       i IN {128,127,126,121,0}`,
  GEN_TAC THEN REWRITE_TAC[POLYVAL_WORD_FULL_XOR] THEN
  REWRITE_TAC[BIT_WORD_XOR; BIT_WORD_SHL_1_256; BIT_WORD_1_256] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DIMINDEX_256] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `i < 256` THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC] THEN
  ASM_CASES_TAC `i = 128` THEN ASM_REWRITE_TAC[] THEN
  TRY(CONV_TAC NUM_REDUCE_CONV) THEN
  ASM_CASES_TAC `i = 127` THEN ASM_REWRITE_TAC[] THEN
  TRY(CONV_TAC NUM_REDUCE_CONV) THEN
  ASM_CASES_TAC `i = 126` THEN ASM_REWRITE_TAC[] THEN
  TRY(CONV_TAC NUM_REDUCE_CONV) THEN
  ASM_CASES_TAC `i = 121` THEN ASM_REWRITE_TAC[] THEN
  TRY(CONV_TAC NUM_REDUCE_CONV) THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[]);;

(* Reciprocal relationship: ghash bit a <=> polyval bit (128-a)              *)
let GHASH_POLYVAL_RECIPROCAL = prove(
  `!a. a <= 128 ==>
    (bit a (word 340282366920938463463374607431768211591 : (256)word) <=>
     bit (128 - a) (word 598152598103212142806713177126155059201 : (256)word))`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_GHASH_WORD; BIT_POLYVAL_WORD] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  MAP_EVERY (fun n -> ASM_CASES_TAC (mk_eq(`a:num`, mk_small_numeral n)) THEN
    ASM_REWRITE_TAC[] THEN TRY(CONV_TAC NUM_REDUCE_CONV))
    [128; 7; 2; 1; 0] THEN
  ASM_ARITH_TAC);;

(* ========================================================================= *)
(* Step 4: Product reversal identity for ghash_poly × m ↔ polyval_poly × m'  *)
(*                                                                           *)
(* For m:int128 with ~bit 127 m, the 254-reversal of word_pmul(zx m)(P)      *)
(* equals word_pmul(zx(REF m))(Q), bit by bit.                               *)
(* This is the word-level form of REV_254(m·P) = REV_126(m)·Q.               *)
(* ========================================================================= *)

let PMUL_GHASH_POLYVAL_REFLECT = prove(
 `!m:int128. ~bit 127 m ==> !k. 1 <= k /\ k <= 255 ==>
   (bit (255 - k)
     (word_pmul (word_zx m : (256)word)
                (word 340282366920938463463374607431768211591 : (256)word) : (512)word) <=>
    bit k
     (word_pmul (word_zx(bit_reflect128 m) : (256)word)
                (word 598152598103212142806713177126155059201 : (256)word) : (512)word))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[BIT_WORD_PMUL_ALT] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= 255 ==> k < 512`;
               ARITH_RULE `1 <= k /\ k <= 255 ==> 255 - k < 512`] THEN
  REWRITE_TAC[BIT_GHASH_WORD; BIT_POLYVAL_WORD] THEN
  SUBGOAL_THEN
    `CARD {i | i <= 255 - k /\ bit i (word_zx m : (256)word) /\
               255 - k - i IN {128, 7, 2, 1, 0}} =
     CARD {i | i <= k /\
               bit i (word_zx (bit_reflect128 m) : (256)word) /\
               k - i IN {128, 127, 126, 121, 0}}`
    (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
    `{i | i <= k /\
          bit i (word_zx (bit_reflect128 m) : (256)word) /\
          k - i IN {128, 127, 126, 121, 0}} =
     IMAGE (\j. 127 - j)
       {j | j <= 255 - k /\ bit j (word_zx m : (256)word) /\
            255 - k - j IN {128, 7, 2, 1, 0}}`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(SPECL [`m:int128`; `i:num`] BIT_WORD_ZX_REFLECT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `1 <= i` ASSUME_TAC THENL
       [ASM_CASES_TAC `i = 0` THENL
         [UNDISCH_TAC `bit (127 - i) (m:int128)` THEN ASM_REWRITE_TAC[SUB_0] THEN
          ASM_MESON_TAC[];
          ASM_ARITH_TAC];
        ALL_TAC] THEN
      EXISTS_TAC `127 - i:num` THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `k - i IN {128, 127, 126, 121, 0}` THEN
        REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MP_TAC(SPECL [`m:int128`; `127 - i:num`] BIT_WORD_ZX_LT127) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `127 - i <= 126` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        UNDISCH_TAC `k - i IN {128, 127, 126, 121, 0}` THEN
        REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPECL [`m:int128`; `j:num`] BIT_WORD_ZX_LT127) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `j <= 126 /\ bit j (m:int128)` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `255 - k - j IN {128, 7, 2, 1, 0}` THEN
        REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MP_TAC(SPECL [`m:int128`; `127 - j:num`] BIT_WORD_ZX_REFLECT) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `127 - (127 - j) = j` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
        UNDISCH_TAC `255 - k - j IN {128, 7, 2, 1, 0}` THEN
        REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]];
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `x <= 126 /\ y <= 126` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MP_TAC(SPECL [`m:int128`; `x:num`] BIT_WORD_ZX_LT127) THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
          MP_TAC(SPECL [`m:int128`; `y:num`] BIT_WORD_ZX_LT127) THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
        ASM_ARITH_TAC];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j <= 255 - k}` THEN
      SIMP_TAC[FINITE_NUMSEG_LE; SUBSET; IN_ELIM_THM]]]);;

(* ========================================================================= *)
(* Step 5: Define nist_ghash and prove bridge to ghash_polyval_acc           *)
(*                                                                           *)
(* The NIST GHASH Horner iteration Y_j = (Y_{j-1} ⊕ X_j) • H                 *)
(* where • = ⊗₂ ⊗₂ x^{-127} (Gueron eq 3.10)                                 *)
(* equals polyval_dot(·, x·H) by eq 4.6.                                     *)
(* So nist_ghash = ghash_polyval_acc with ghash_twist(H) = x·H mod Q(x).     *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Step 6: GUERON_PROP1 — the main theorem                                   *)
(*                                                                           *)
(* bit_reflect128(ghash_reduce(word_pmul(REF a)(REF b)))                     *)
(*   = polyval_dot a (ghash_twist b)                                         *)
(*                                                                           *)
(* Proof structure:                                                          *)
(*   1. MOD_POLYVAL_WORD_EQ reduces to mod_polyval congruence                *)
(*   2. MOD_POLYVAL_CANCEL_VARPOW_GEN cancels x^128 from both sides          *)
(*   3. MOD_POLYVAL_TRANS splits into KEY CONGRUENCE + RHS                   *)
(*   4. RHS: a*x*b ≡ polyval_dot(a,ghash_twist b)*x^128 mod Q                *)
(*      solved by GHASH_TWIST_CORRECT + POLYVAL_DOT_CORRECT                  *)
(*   5. KEY CONGRUENCE: REF(S)*x^128 ≡ a*x*b mod Q                           *)
(*      From POLY_EQUIV_GHASH_REDUCE: P | G where                            *)
(*        G = poly_of_word S + poly_of_word(word_pmul(REF a)(REF b))         *)
(*      Extract quotient M with deg(M) <= 126.                               *)
(*      The 254-reversal of G = polyval_poly * REV_126(M) by                 *)
(*      PMUL_GHASH_POLYVAL_REFLECT, and equals REF(S)*x^128 + a*x*b          *)
(*      by PMUL_REFLECT128 + BIT_REFLECT128.                                 *)
(*      TODO: formalize the reversal divisibility polynomial equality.       *)
(* ========================================================================= *)

(* Helper lemmas for the degree bound in GUERON_PROP1                        *)
let RING_POLYNOMIAL_OF_CARRIER = prove(
  `!x:(1->num)->bool. x IN ring_carrier bool_poly ==> ring_polynomial bool_ring x`,
  GEN_TAC THEN REWRITE_TAC[bool_poly] THEN
  MP_TAC(ISPECL [`bool_ring`; `(:1)`; `x:(1->num)->bool`] RING_POLYNOMIAL_CARRIER_GEN) THEN
  REWRITE_TAC[SUBSET_UNIV] THEN MESON_TAC[]);;

let GHASH_POLY_NONZERO = prove(
  `~(ghash_poly = poly_0 bool_ring)`,
  DISCH_TAC THEN MP_TAC POLY_DEG_GHASH_POLY THEN
  ASM_REWRITE_TAC[POLY_DEG_0] THEN ARITH_TAC);;

let POLY_ADD_COEFF = prove(
 `!p q. p IN ring_carrier bool_poly /\ q IN ring_carrier bool_poly ==>
   !k. ring_add bool_poly p q (\v:1. k) <=> ~(p(\v. k) <=> q(\v. k))`,
 REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
 REWRITE_TAC[bool_poly; POLY_RING; poly_add; BOOL_RING]);;

let POLY_OF_WORD_COEFF = prove(
 `!w:N word. !k. poly_of_word w (\v:1. k) <=> bit k w`,
 REWRITE_TAC[poly_of_word]);;

let POLY_MUL_VARPOW_SHIFT = prove(
 `!n p. p IN ring_carrier bool_poly ==>
   !k. ring_mul bool_poly (ring_pow bool_poly (poly_var bool_ring one) n) p (\v:1. k) <=>
       n <= k /\ p(\v. k - n)`,
 REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
 REWRITE_TAC[GSYM bool_poly; BOOL_POLY_MUL] THEN
 REWRITE_TAC[POLY_MUL_UNIVARIATE; coeff] THEN
 SIMP_TAC[bool_poly; POLY_RING_VAR_POW_1; BOOL_RING; FUN_EQ_THM; FORALL_ONE_THM] THEN
 GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RAND] THEN
 REWRITE_TAC[COND_RATOR] THEN
 SUBGOAL_THEN `(\a. if a = n then (p:((1->num)->bool))(\v:1. k - a) else F) =
               (\a. if a = n then p(\v. k - n) else F)` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN `F = ring_0 bool_ring` (fun th -> ONCE_REWRITE_TAC[th]) THENL
    [REWRITE_TAC[BOOL_RING]; ALL_TAC] THEN
   REWRITE_TAC[RING_SUM_DELTA; IN_NUMSEG; LE_0; BOOL_RING; IN_UNIV] THEN
   MESON_TAC[]]);;

let AXB_EQ_XAB = prove(
 `!(a:int128) (b:int128).
   ring_mul bool_poly (poly_of_word a)
     (ring_mul bool_poly (poly_var bool_ring one) (poly_of_word b)) =
   ring_mul bool_poly (ring_pow bool_poly (poly_var bool_ring one) 1)
     (poly_of_word(word_pmul a b : (256)word))`,
 REPEAT GEN_TAC THEN
 SUBGOAL_THEN `ring_pow bool_poly (poly_var bool_ring one) 1 = poly_var bool_ring (one:1)`
   SUBST1_TAC THENL
  [MATCH_MP_TAC RING_POW_1 THEN REWRITE_TAC[GSYM bool_poly; POLY_VAR_BOOL_POLY]; ALL_TAC] THEN
 SUBGOAL_THEN `ring_mul bool_poly (poly_of_word (a:int128)) (poly_of_word (b:int128)) =
               poly_of_word(word_pmul a b : (256)word)` (fun th ->
   SUBGOAL_THEN `poly_of_word(a:int128) IN ring_carrier bool_poly /\
                 poly_of_word(b:int128) IN ring_carrier bool_poly /\
                 (poly_var bool_ring (one:1)) IN ring_carrier bool_poly` MP_TAC THENL
    [REWRITE_TAC[BOOL_POLY_OF_WORD; GSYM bool_poly; POLY_VAR_BOOL_POLY]; ALL_TAC] THEN
   STRIP_TAC THEN
   ASM_MESON_TAC[th; RING_MUL_ASSOC; RING_MUL_SYM; RING_MUL; GSYM bool_poly]) THEN
 REWRITE_TAC[GSYM POLY_OF_WORD_PMUL_2N]);;

let QP_EQ_QPMULP = prove(
 `!(p:int128).
   ring_mul bool_poly polyval_poly (poly_of_word(word_zx p : (256)word)) =
   poly_of_word(word_pmul (word 598152598103212142806713177126155059201 : (256)word)
                           (word_zx p : (256)word) : (512)word)`,
 GEN_TAC THEN
 SUBGOAL_THEN `polyval_poly = poly_of_word(word 598152598103212142806713177126155059201 : (256)word)`
   SUBST1_TAC THENL
  [MATCH_MP_TAC POLYVAL_POLY_OF_WORD THEN
   CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC; ALL_TAC] THEN
 REWRITE_TAC[GSYM POLY_OF_WORD_PMUL_2N]);;

let BIT_PMUL_128_BOUND = prove(
 `!(a:int128) (b:int128) j. 255 <= j ==> ~bit j (word_pmul a b : (256)word)`,
 REPEAT GEN_TAC THEN DISCH_TAC THEN
 REWRITE_TAC[BIT_WORD_PMUL_ALT; DIMINDEX_TYBIT0; DIMINDEX_128; DE_MORGAN_THM] THEN
 ASM_CASES_TAC `j < 2 * 128` THENL
  [DISJ2_TAC THEN
   SUBGOAL_THEN `{i | i <= j /\ bit i (a:int128) /\ bit (j - i) (b:int128)} = {}`
     SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
     X_GEN_TAC `i:num` THEN
     ASM_CASES_TAC `128 <= i` THENL
      [ASM_MESON_TAC[BIT_TRIVIAL_128]; ALL_TAC] THEN
     ASM_CASES_TAC `128 <= j - i` THENL
      [ASM_MESON_TAC[BIT_TRIVIAL_128]; ALL_TAC] THEN
     ASM_ARITH_TAC;
     REWRITE_TAC[CARD_CLAUSES; ODD]];
   DISJ1_TAC THEN ASM_ARITH_TAC]);;

(* Infrastructure for GUERON_PROP1 proof                                     *)

let GHASH_POLY_IN_CARRIER = prove(
  `ghash_poly IN ring_carrier bool_poly`,
  MP_TAC(INST_TYPE [`:256`,`:N`] GHASH_POLY_OF_WORD) THEN
  REWRITE_TAC[DIMINDEX_256; ARITH_RULE `128 < 256`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[BOOL_POLY_OF_WORD]);;

let GHASH_IDEAL_MEMBERSHIP = prove(
  `!w:(256)word. ring_add bool_poly (poly_of_word(ghash_reduce w)) (poly_of_word w)
                 IN ideal_generated bool_poly {ghash_poly}`,
  GEN_TAC THEN
  MP_TAC(SPEC `w:(256)word` POLY_EQUIV_GHASH_REDUCE) THEN
  REWRITE_TAC[mod_ghash; cong; BOOL_POLY_SUB] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let GHASH_QUOTIENT_EXISTS = prove(
  `!w:(256)word. ?q. q IN ring_carrier bool_poly /\
    ring_add bool_poly (poly_of_word(ghash_reduce w)) (poly_of_word w) =
    ring_mul bool_poly ghash_poly q`,
  GEN_TAC THEN
  MP_TAC(SPEC `w:(256)word` GHASH_IDEAL_MEMBERSHIP) THEN
  SUBGOAL_THEN `ideal_generated bool_poly {ghash_poly} =
    {ring_mul bool_poly ghash_poly x | x | x IN ring_carrier bool_poly}`
    SUBST1_TAC THENL
   [MATCH_MP_TAC IDEAL_GENERATED_SING_ALT THEN REWRITE_TAC[GHASH_POLY_IN_CARRIER];
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]]);;

let QUOTIENT_DEGREE_BOUND = prove(
  `!q. q IN ring_carrier bool_poly /\
       poly_deg bool_ring (ring_mul bool_poly ghash_poly q) <= 254
       ==> poly_deg bool_ring q <= 126`,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `q = ring_0 bool_poly` THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bool_poly; POLY_RING; POLY_DEG_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `poly_deg bool_ring (ring_mul bool_poly ghash_poly q) =
                128 + poly_deg bool_ring q` MP_TAC THENL
   [SUBGOAL_THEN `poly_deg bool_ring ghash_poly = 128` (fun th ->
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM th]) THENL
     [REWRITE_TAC[POLY_DEG_GHASH_POLY]; ALL_TAC] THEN
    SUBGOAL_THEN `ring_mul bool_poly ghash_poly q = poly_mul bool_ring ghash_poly q`
      SUBST1_TAC THENL
     [REWRITE_TAC[bool_poly; POLY_RING]; ALL_TAC] THEN
    MATCH_MP_TAC POLY_DEG_MUL THEN
    REWRITE_TAC[INTEGRAL_DOMAIN_BOOL_RING] THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `ghash_poly` RING_POLYNOMIAL_OF_CARRIER) THEN
      REWRITE_TAC[GHASH_POLY_IN_CARRIER]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `q:(1->num)->bool` RING_POLYNOMIAL_OF_CARRIER) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EQ_TAC THENL
     [DISCH_TAC THEN MP_TAC GHASH_POLY_NONZERO THEN ASM_REWRITE_TAC[poly_0];
      DISCH_TAC THEN
      UNDISCH_TAC `~(q = ring_0 bool_poly)` THEN
      REWRITE_TAC[bool_poly; POLY_RING] THEN ASM_REWRITE_TAC[poly_0]];
    ASM_ARITH_TAC]);;

let PMUL_128_DEG_BOUND = prove(
  `!(a:int128) (b:int128).
    poly_deg bool_ring (poly_of_word(word_pmul a b : (256)word)) <= 254`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `word_pmul (a:int128) (b:int128) : (256)word = word 0` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `poly_of_word(word 0 : (256)word) = poly_0 bool_ring`
      (fun th -> REWRITE_TAC[th; POLY_DEG_0]) THENL
     [REWRITE_TAC[FUN_EQ_THM; poly_of_word; poly_0; poly_const; BOOL_RING; BIT_WORD_0];
      ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[POLY_DEG_POLY_OF_WORD; DIMINDEX_256] THEN
  SUBGOAL_THEN `1 <= word_clz(word_pmul (a:int128) (b:int128) : (256)word)`
    (fun th -> MP_TAC th THEN ARITH_TAC) THEN
  REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  REWRITE_TAC[WORD_CLZ_EQ_0; DIMINDEX_256] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`a:int128`; `b:int128`; `255`] BIT_PMUL_128_BOUND) THEN
  ARITH_TAC);;

(* Helper: coefficient evaluation for multiplication by poly_var             *)
(* Helper: degree bound for pmul(Q_word, zx(REF m))                          *)
let RHS_PMUL_BOUND_DIRECT = prove(
 `!m:int128 j. 256 <= j ==>
   ~bit j (word_pmul (word 598152598103212142806713177126155059201 : (256)word)
                      (word_zx(bit_reflect128 m) : (256)word) : (512)word)`,
 REPEAT GEN_TAC THEN DISCH_TAC THEN
 REWRITE_TAC[BIT_WORD_PMUL_ALT] THEN
 CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
 ASM_CASES_TAC `j < 512` THENL
  [ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `{i | i <= j /\
     bit i (word 598152598103212142806713177126155059201 : (256)word) /\
     bit (j - i) (word_zx(bit_reflect128 (m:int128)) : (256)word)} = {}`
     SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
     X_GEN_TAC `i:num` THEN
     REWRITE_TAC[BIT_POLYVAL_WORD; BIT_WORD_ZX_REFLECT] THEN
     REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
     ASM_ARITH_TAC;
     REWRITE_TAC[CARD_CLAUSES; ODD]];
   ASM_REWRITE_TAC[]]);;

(* GUERON_PROP1 — the main theorem.
   Proof structure:
   1. Reduce to mod_polyval congruence via MOD_POLYVAL_WORD_EQ
   2. Cancel x^128 via MOD_POLYVAL_CANCEL_VARPOW_GEN
   3. Split into KEY CONGRUENCE (LHS) and RHS branch
   4. KEY CONGRUENCE: extract quotient, prove coefficient identity using
      PMUL_GHASH_POLYVAL_REFLECT + PMUL_REFLECT128 + BIT_REFLECT128
   5. RHS: use GHASH_TWIST_CORRECT + POLYVAL_DOT_CORRECT *)
let GUERON_PROP1 = prove(
 `!a b:int128.
  bit_reflect128(ghash_reduce(word_pmul (bit_reflect128 a) (bit_reflect128 b)))
  = polyval_dot a (ghash_twist b)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MOD_POLYVAL_WORD_EQ) THEN
  ABBREV_TAC `w = word_pmul (bit_reflect128 a) (bit_reflect128 b) : (256)word` THEN
  ABBREV_TAC `S = ghash_reduce w : int128` THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MOD_POLYVAL_CANCEL_VARPOW_GEN) THEN
  EXISTS_TAC `128` THEN REWRITE_TAC[BOOL_POLY_OF_WORD] THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC `ring_mul bool_poly (ring_pow bool_poly (poly_var bool_ring one) 1)
    (poly_of_word (word_pmul (a:int128) (b:int128) : (256)word))` THEN
  CONJ_TAC THENL
   [(* KEY CONGRUENCE: REF(S)*x^128 ≡ x*pmul(a,b) mod Q *)
    REWRITE_TAC[cong; mod_polyval; BOOL_POLY_SUB] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RING_MUL THEN REWRITE_TAC[GSYM bool_poly; BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY];
      MATCH_MP_TAC RING_MUL THEN REWRITE_TAC[GSYM bool_poly; BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY];
      ALL_TAC] THEN
    (* Extract quotient from GHASH_IDEAL_MEMBERSHIP *)
    MP_TAC(SPEC `w:(256)word` GHASH_QUOTIENT_EXISTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:(1->num)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `poly_deg bool_ring (q:(1->num)->bool) <= 126` ASSUME_TAC THENL
     [MATCH_MP_TAC QUOTIENT_DEGREE_BOUND THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `poly_deg bool_ring (ring_add bool_poly (poly_of_word (S:int128)) (poly_of_word (w:(256)word))) <= 254`
        MP_TAC THENL
       [MP_TAC(SPECL [`bit_reflect128 (a:int128)`; `bit_reflect128 (b:int128)`] PMUL_128_DEG_BOUND) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [bool_poly] THEN
        MATCH_MP_TAC POLY_DEG_RING_ADD_LE THEN
        REWRITE_TAC[GSYM bool_poly; BOOL_POLY_OF_WORD] THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPEC `S:int128` POLY_DEG_POLY_OF_WORD_BOUND) THEN
        REWRITE_TAC[DIMINDEX_128] THEN ARITH_TAC;
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ABBREV_TAC `m = (word_of_poly q : int128)` THEN
    SUBGOAL_THEN `q = poly_of_word (m:int128)` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC POLY_OF_WORD_OF_POLY THEN ASM_REWRITE_TAC[DIMINDEX_128] THEN
      UNDISCH_TAC `poly_deg bool_ring (q:(1->num)->bool) <= 126` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~bit 127 (m:int128)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `127 <= poly_deg bool_ring (poly_of_word (m:int128))` MP_TAC THENL
       [REWRITE_TAC[POLY_DEG_POLY_OF_WORD; DIMINDEX_128] THEN
        SUBGOAL_THEN `~(m:int128 = word 0)` ASSUME_TAC THENL
         [DISCH_TAC THEN UNDISCH_TAC `bit 127 (m:int128)` THEN
          ASM_REWRITE_TAC[BIT_WORD_0]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`m:int128`; `127`] WORD_CLZ_LBOUND) THEN
        ASM_REWRITE_TAC[DIMINDEX_128] THEN ARITH_TAC;
        UNDISCH_TAC `q = poly_of_word (m:int128)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    (* Convert ideal membership to existential *)
    SUBGOAL_THEN
      `ideal_generated bool_poly {polyval_poly} =
       {ring_mul bool_poly polyval_poly x | x | x IN ring_carrier bool_poly}`
      SUBST1_TAC THENL
     [MATCH_MP_TAC IDEAL_GENERATED_SING_ALT THEN
      MP_TAC(INST_TYPE [`:256`,`:N`] POLYVAL_POLY_OF_WORD) THEN
      REWRITE_TAC[DIMINDEX_256; ARITH_RULE `128 < 256`] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[BOOL_POLY_OF_WORD];
      REWRITE_TAC[IN_ELIM_THM]] THEN
    EXISTS_TAC `poly_of_word(word_zx(bit_reflect128 (m:int128)) : (256)word)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[BOOL_POLY_OF_WORD];
      ALL_TAC] THEN
    (* Rewrite RHS: Q*poly(zx(REF m)) = poly(pmul(Q_word,zx(REF m))) *)
    GEN_REWRITE_TAC RAND_CONV
     [SPEC `bit_reflect128 (m:int128)` QP_EQ_QPMULP] THEN
    (* Commute first term and convert to coefficient form *)
    SUBGOAL_THEN
      `ring_mul bool_poly (poly_of_word (bit_reflect128 (S:int128)))
        (ring_pow bool_poly (poly_var bool_ring one) 128) =
       ring_mul bool_poly (ring_pow bool_poly (poly_var bool_ring one) 128)
        (poly_of_word (bit_reflect128 S))`
      SUBST1_TAC THENL
     [MATCH_MP_TAC RING_MUL_SYM THEN
      REWRITE_TAC[GSYM bool_poly; BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    GEN_REWRITE_TAC I [FORALL_FUN_FROM_1] THEN
    X_GEN_TAC `k:num` THEN
    (* Evaluate LHS coefficients *)
    MP_TAC(SPECL
      [`ring_mul bool_poly (ring_pow bool_poly (poly_var bool_ring one) 128)
         (poly_of_word (bit_reflect128 (S:int128)))`;
       `ring_mul bool_poly (ring_pow bool_poly (poly_var bool_ring one) 1)
         (poly_of_word (word_pmul (a:int128) (b:int128) : (256)word))`]
      POLY_ADD_COEFF) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC RING_MUL THEN
      REWRITE_TAC[GSYM bool_poly; BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`128`; `poly_of_word(bit_reflect128 (S:int128))`] POLY_MUL_VARPOW_SHIFT) THEN
    REWRITE_TAC[BOOL_POLY_OF_WORD] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN REWRITE_TAC[POLY_OF_WORD_COEFF] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`1`; `poly_of_word(word_pmul (a:int128) (b:int128) : (256)word)`] POLY_MUL_VARPOW_SHIFT) THEN
    REWRITE_TAC[BOOL_POLY_OF_WORD] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN REWRITE_TAC[POLY_OF_WORD_COEFF] THEN
    DISCH_THEN SUBST1_TAC THEN
    (* Evaluate RHS coefficient *)
    REWRITE_TAC[POLY_OF_WORD_COEFF] THEN
    (* Case k = 0 *)
    ASM_CASES_TAC `k = 0` THENL
     [ASM_REWRITE_TAC[ARITH_RULE `~(128 <= 0)`; ARITH_RULE `~(1 <= 0)`] THEN
      REWRITE_TAC[BIT_WORD_PMUL_ALT] THEN
      CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN REWRITE_TAC[ARITH_RULE `0 < 512`] THEN
      SUBGOAL_THEN `{i | i <= 0 /\
        bit i (word 598152598103212142806713177126155059201 : (256)word) /\
        bit (0 - i) (word_zx(bit_reflect128 (m:int128)) : (256)word)} = {}`
        (fun th -> REWRITE_TAC[th; CARD_CLAUSES; ODD]) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; LE; SUB_0] THEN
      REWRITE_TAC[BIT_WORD_ZX_REFLECT; ARITH_RULE `127 - 0 = 127`] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    (* Case k > 255: degree bounds *)
    ASM_CASES_TAC `k <= 255` THENL
     [ALL_TAC;
      SUBGOAL_THEN `~bit k (word_pmul (word 598152598103212142806713177126155059201 : (256)word)
        (word_zx(bit_reflect128 (m:int128)) : (256)word) : (512)word)` (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_MP_TAC RHS_PMUL_BOUND_DIRECT THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~bit (k-1) (word_pmul (a:int128) (b:int128) : (256)word)` (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_MP_TAC BIT_PMUL_128_BOUND THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `128 <= k` THENL
       [ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `~bit (k-128) (bit_reflect128 (S:int128))` (fun th -> REWRITE_TAC[th]) THEN
        MATCH_MP_TAC BIT_TRIVIAL_128 THEN ASM_ARITH_TAC;
        ASM_REWRITE_TAC[]]] THEN
    (* Main case: 1 <= k <= 255. Use PMUL_GHASH_POLYVAL_REFLECT *)
    ONCE_REWRITE_TAC[WORD_PMUL_SYM] THEN
    MP_TAC(SPEC `m:int128` PMUL_GHASH_POLYVAL_REFLECT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    (* Derive bit-level form of assumption: bit j (pmul(zx m, P_word)) <=> ~(bit j S <=> bit j w) *)
    SUBGOAL_THEN `!j. bit j (word_pmul (word_zx (m:int128) : (256)word)
        (word 340282366920938463463374607431768211591 : (256)word) : (512)word) <=>
      ~(bit j (S:int128) <=> bit j (w:(256)word))`
      (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      SUBGOAL_THEN `poly_of_word (word_pmul (word_zx (m:int128) : (256)word)
        (word 340282366920938463463374607431768211591 : (256)word) : (512)word) =
        ring_add bool_poly (poly_of_word (S:int128)) (poly_of_word (w:(256)word))`
        (fun th -> MP_TAC(AP_TERM `\p:(1->num)->bool. p (\v:1. j)` th)) THENL
       [REWRITE_TAC[POLY_OF_WORD_PMUL_2N] THEN
        SUBGOAL_THEN `poly_of_word (word_zx (m:int128) : (256)word) = poly_of_word (m:int128)`
          SUBST1_TAC THENL
         [MATCH_MP_TAC POLY_OF_WORD_ZX THEN
          CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `ring_mul bool_poly (poly_of_word (m:int128))
          (poly_of_word (word 340282366920938463463374607431768211591 : (256)word)) =
          ring_mul bool_poly (poly_of_word (word 340282366920938463463374607431768211591 : (256)word))
            (poly_of_word (m:int128))`
          SUBST1_TAC THENL
         [MATCH_MP_TAC RING_MUL_SYM THEN REWRITE_TAC[GSYM bool_poly; BOOL_POLY_OF_WORD]; ALL_TAC] THEN
        CONV_TAC SYM_CONV THEN
        UNDISCH_TAC `ring_add bool_poly (poly_of_word (ghash_reduce w)) (poly_of_word w) =
          ring_mul bool_poly ghash_poly q` THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(INST_TYPE [`:256`,`:N`] GHASH_POLY_OF_WORD) THEN
        CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
        REWRITE_TAC[ARITH_RULE `128 < 256`] THEN
        SIMP_TAC[];
        MP_TAC(SPECL [`poly_of_word(S:int128)`; `poly_of_word(w:(256)word)`] POLY_ADD_COEFF) THEN
        REWRITE_TAC[BOOL_POLY_OF_WORD] THEN
        DISCH_THEN(MP_TAC o SPEC `j:num`) THEN REWRITE_TAC[POLY_OF_WORD_COEFF] THEN
        DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[POLY_OF_WORD_COEFF] THEN CONV_TAC TAUT];
      ALL_TAC] THEN
    (* Rewrite bit (255-k) w using PMUL_REFLECT128 *)
    SUBGOAL_THEN `bit (255 - k) (w:(256)word) <=> bit (k - 1) (word_pmul (b:int128) (a:int128) : (256)word)`
      SUBST1_TAC THENL
     [EXPAND_TAC "w" THEN
      MP_TAC(SPECL [`a:int128`; `b:int128`; `255 - k`] PMUL_REFLECT128) THEN
      ANTS_TAC THENL [UNDISCH_TAC `k <= 255` THEN UNDISCH_TAC `1 <= k` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `254 - (255 - k) = k - 1` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `k <= 255` THEN UNDISCH_TAC `1 <= k` THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
        REWRITE_TAC[]];
      ALL_TAC] THEN
    (* Case split on 128 <= k *)
    ASM_CASES_TAC `128 <= k` THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `bit (255 - k) (S:int128) = bit (k - 128) (bit_reflect128 S)`
        SUBST1_TAC THENL
       [MP_TAC(SPECL [`S:int128`; `k - 128`] BIT_REFLECT128) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `k <= 255` THEN UNDISCH_TAC `128 <= k` THEN ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `127 - (k - 128) = 255 - k` (fun th -> REWRITE_TAC[th]) THENL
         [UNDISCH_TAC `k <= 255` THEN UNDISCH_TAC `128 <= k` THEN ARITH_TAC;
          DISCH_THEN(fun th -> REWRITE_TAC[th])];
        REWRITE_TAC[]];
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~bit (255 - k) (S:int128)` (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC BIT_TRIVIAL_128 THEN
      UNDISCH_TAC `~(128 <= k)` THEN ARITH_TAC];
    (* RHS branch: a*x*b ≡ polyval_dot(a, ghash_twist b)*x^128 mod Q *)
    ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
    MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
    EXISTS_TAC `ring_mul bool_poly (poly_of_word (a:int128)) (poly_of_word (ghash_twist (b:int128)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[POLYVAL_DOT_CORRECT];
      REWRITE_TAC[GSYM AXB_EQ_XAB] THEN
      MATCH_MP_TAC MOD_POLYVAL_MUL THEN REWRITE_TAC[BOOL_POLY_OF_WORD] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[MOD_POLYVAL_REFL; BOOL_POLY_OF_WORD];
        REWRITE_TAC[GHASH_TWIST_CORRECT]]]])

(* ========================================================================= *)
(* NIST GHASH "dot" operation and recursive GHASH definition.                *)
(*                                                                           *)
(* nist_dot is the native NIST GHASH multiply: bit-reflect inputs,           *)
(* carry-less multiply, reduce mod P(x), bit-reflect the result.             *)
(*                                                                           *)
(* nist_ghash is defined recursively using nist_dot, matching the NIST       *)
(* SP 800-38D specification directly.                                        *)
(*                                                                           *)
(* NIST_GHASH_IS_POLYVAL bridges to ghash_polyval_acc via GUERON_PROP1.      *)
(* ========================================================================= *)

let nist_dot = new_definition
  `nist_dot (a:int128) (b:int128) : int128 =
   bit_reflect128(ghash_reduce(word_pmul (bit_reflect128 a) (bit_reflect128 b)))`;;

(* GUERON_PROP1 restated in terms of nist_dot                                *)
let NIST_DOT_IS_POLYVAL_DOT = prove
 (`!a b:int128. nist_dot a b = polyval_dot a (ghash_twist b)`,
  REWRITE_TAC[nist_dot; GUERON_PROP1]);;

let nist_ghash = define
 `nist_ghash (h:int128) (acc:int128) [] = acc /\
  nist_ghash h acc (CONS x xs) =
    nist_ghash h (nist_dot (word_xor acc x) h) xs`;;

(* The core bridge: NIST GHASH = POLYVAL Horner with twisted key.            *)
(* Proof by list induction; the step case uses GUERON_PROP1 via              *)
(* NIST_DOT_IS_POLYVAL_DOT to rewrite nist_dot to polyval_dot.               *)
let NIST_GHASH_IS_POLYVAL = prove
 (`!h acc xs. nist_ghash h acc xs = ghash_polyval_acc (ghash_twist h) acc xs`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[nist_ghash; ghash_polyval_acc; NIST_DOT_IS_POLYVAL_DOT]);;

let NIST_GHASH_NIL = prove
 (`!h acc. nist_ghash h acc [] = acc`,
  REWRITE_TAC[nist_ghash]);;

let NIST_GHASH_CONS = prove
 (`!h acc x xs. nist_ghash h acc (CONS x xs) =
                nist_ghash h (nist_dot (word_xor acc x) h) xs`,
  REWRITE_TAC[nist_ghash]);;

let NIST_GHASH_APPEND = prove
 (`!h xs ys acc. nist_ghash h acc (APPEND xs ys) =
                 nist_ghash h (nist_ghash h acc xs) ys`,
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL; GHASH_ACC_APPEND]);;
