(* ========================================================================= *)
(* Karatsuba carry-less multiplication lemma for GHASH.                      *)
(* Shows: word_pmul a b = Karatsuba decomposition using 3 half-size pmuls.   *)
(* ========================================================================= *)

needs "common/polyval.ml";;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas for polynomial-level conversion.                            *)
(* ------------------------------------------------------------------------- *)

let WORD_DECOMPOSE_128 = BITBLAST_RULE
  `!(a:128 word).
    a = word_xor (word_zx (word_subword a (0,64) : 64 word))
                 (word_shl (word_zx (word_subword a (64,64) : 64 word)) 64)`;;

let POLY_OF_WORD_INJ = prove(
  `!(x:N word) (y:N word). poly_of_word x = poly_of_word y ==> x = y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM WORD_OF_POLY_OF_WORD] THEN
  AP_TERM_TAC THEN ASM_REWRITE_TAC[]);;

let POLY_OF_WORD_PMUL_GEN = prove(
  `!(x:M word) (y:N word).
    poly_deg bool_ring (ring_mul bool_poly (poly_of_word x) (poly_of_word y))
    < dimindex(:P)
    ==> poly_of_word(word_pmul x y : P word) =
        ring_mul bool_poly (poly_of_word x) (poly_of_word y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_PMUL_POLY] THEN
  ABBREV_TAC `p = ring_mul bool_poly (poly_of_word (x:M word)) (poly_of_word (y:N word))` THEN
  SUBGOAL_THEN `p IN ring_carrier bool_poly` ASSUME_TAC THENL
  [EXPAND_TAC "p" THEN SIMP_TAC[RING_MUL; BOOL_POLY_OF_WORD]; ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_OF_POLY_OF_WORD_GEN] THEN
  SUBGOAL_THEN `poly_of_word((word_of_poly:((1->num)->bool)->P word) p) = p`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC(INST_TYPE [`:P`,`:N`] POLY_OF_WORD_OF_POLY) THEN
  ASM_REWRITE_TAC[]);;

let POLY_VAR_POW_OF_WORD_256 = INST_TYPE [`:256`,`:N`] POLY_VAR_POW_OF_WORD;;

let zx_128_256 = prove
 (`!w:128 word. poly_of_word(word_zx w : 256 word) = poly_of_word w`,
  GEN_TAC THEN MATCH_MP_TAC POLY_OF_WORD_ZX THEN
  REWRITE_TAC[DIMINDEX_128; DIMINDEX_256] THEN ARITH_TAC);;

let zx_64_128 = prove
 (`!w:64 word. poly_of_word(word_zx w : 128 word) = poly_of_word w`,
  GEN_TAC THEN MATCH_MP_TAC POLY_OF_WORD_ZX THEN
  REWRITE_TAC[DIMINDEX_64; DIMINDEX_128] THEN ARITH_TAC);;

let PMUL_DEG_TAC_GEN dim_out dim_in =
  REWRITE_TAC[bool_poly; POLY_RING; dim_out] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_MUL_LE o lhand o snd) THEN
  REWRITE_TAC[RING_POLYNOMIAL_OF_WORD] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS) THEN
  REWRITE_TAC[dim_in; POLY_DEG_POLY_OF_WORD; dim_out] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_CLZ_CONV) THEN
  TRY(MATCH_MP_TAC(ARITH_RULE `a < 128 /\ b <= 128 ==> a + b < 256`) THEN
      CONJ_TAC THEN REWRITE_TAC[WORD_CLZ_LT_DIMINDEX; dim_in]) THEN
  ARITH_TAC;;

let PMUL_DEG_TAC = PMUL_DEG_TAC_GEN DIMINDEX_256 DIMINDEX_128;;

let pmul_shl_zx = prove(
  `(!w:128 word.
     poly_of_word(word_pmul (word_zx w : 256 word) (word(2 EXP 64) : 256 word) : 256 word) =
     ring_mul bool_poly (poly_of_word w) (poly_of_word(word(2 EXP 64) : 256 word))) /\
   (!w:128 word.
     poly_of_word(word_pmul (word_zx w : 256 word) (word(2 EXP 128) : 256 word) : 256 word) =
     ring_mul bool_poly (poly_of_word w) (poly_of_word(word(2 EXP 128) : 256 word)))`,
  CONJ_TAC THEN GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CONJUNCT1 WORD_PMUL_ZX] THEN
  MATCH_MP_TAC POLY_OF_WORD_PMUL_GEN THEN PMUL_DEG_TAC);;

let pmul_128_256 = prove(
  `!x:128 word y:128 word.
     poly_of_word(word_pmul x y : 256 word) =
     ring_mul bool_poly (poly_of_word x) (poly_of_word y)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC POLY_OF_WORD_PMUL_GEN THEN PMUL_DEG_TAC);;

let pow64_256 = prove
 (`poly_of_word(word(2 EXP 64) : 256 word) =
   ring_pow bool_poly (poly_var bool_ring one) 64`,
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC POLY_VAR_POW_OF_WORD_256 THEN
  REWRITE_TAC[DIMINDEX_256] THEN ARITH_TAC);;

let pow128_256 = prove
 (`poly_of_word(word(2 EXP 128) : 256 word) =
   ring_pow bool_poly (poly_var bool_ring one) 128`,
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC POLY_VAR_POW_OF_WORD_256 THEN
  REWRITE_TAC[DIMINDEX_256] THEN ARITH_TAC);;

let shl_zx_64_to_poly = prove(
  `!w:64 word. poly_of_word(word_shl (word_zx w : 128 word) 64) =
     ring_mul bool_poly (poly_of_word w)
                        (ring_pow bool_poly (poly_var bool_ring one) 64)`,
  GEN_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 WORD_PMUL_POW2)] THEN
  ONCE_REWRITE_TAC[CONJUNCT1 WORD_PMUL_ZX] THEN
  REWRITE_TAC[GSYM(prove(
    `poly_of_word(word(2 EXP 64) : 128 word) =
     ring_pow bool_poly (poly_var bool_ring one) 64`,
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(INST_TYPE [`:128`,`:N`] POLY_VAR_POW_OF_WORD) THEN
    REWRITE_TAC[DIMINDEX_128] THEN ARITH_TAC))] THEN
  MATCH_MP_TAC POLY_OF_WORD_PMUL_GEN THEN
  PMUL_DEG_TAC_GEN DIMINDEX_128 DIMINDEX_64);;

(* ------------------------------------------------------------------------- *)
(* Schoolbook ring identity: (a+bx)(c+dx) = ac + (ad+bc)x + bdx^2.           *)
(* Proved by RING_RULE (universal ring identity, no char-2 needed).          *)
(* ------------------------------------------------------------------------- *)

let SCHOOLBOOK_RING = GEN_ALL(RING_RULE
  `ring_mul r (ring_add r a (ring_mul r b x))
              (ring_add r c (ring_mul r d x)) =
   ring_add r (ring_mul r a c)
     (ring_add r (ring_mul r (ring_add r (ring_mul r a d) (ring_mul r b c)) x)
                  (ring_mul r (ring_mul r b d) (ring_mul r x x)))`);;

(* ------------------------------------------------------------------------- *)
(* Schoolbook expansion of 128x128 carry-less multiplication.                *)
(* ------------------------------------------------------------------------- *)

let PMUL_SCHOOLBOOK = prove(
  `!(a:128 word) (b:128 word).
    let al = word_subword a (0,64) : 64 word in
    let ah = word_subword a (64,64) : 64 word in
    let bl = word_subword b (0,64) : 64 word in
    let bh = word_subword b (64,64) : 64 word in
    (word_pmul a b : 256 word) =
    word_xor (word_xor (word_zx (word_pmul al bl : 128 word) : 256 word)
                        (word_shl (word_zx (word_xor (word_pmul al bh : 128 word)
                                                     (word_pmul ah bl)) : 256 word) 64))
             (word_shl (word_zx (word_pmul ah bh : 128 word) : 256 word) 128)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC POLY_OF_WORD_INJ THEN
  REWRITE_TAC[POLY_OF_WORD_XOR; zx_128_256;
              GSYM(CONJUNCT2 WORD_PMUL_POW2)] THEN
  REWRITE_TAC[pmul_shl_zx; pow64_256; pow128_256; pmul_128_256] THEN
  REWRITE_TAC[POLY_OF_WORD_XOR] THEN
  ONCE_REWRITE_TAC[POLY_OF_WORD_PMUL_2N] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [WORD_DECOMPOSE_128] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [WORD_DECOMPOSE_128] THEN
  REWRITE_TAC[POLY_OF_WORD_XOR; zx_64_128; shl_zx_64_to_poly] THEN
  ABBREV_TAC `al = poly_of_word(word_subword (a:128 word) (0,64) : 64 word)` THEN
  ABBREV_TAC `ah = poly_of_word(word_subword (a:128 word) (64,64) : 64 word)` THEN
  ABBREV_TAC `bl = poly_of_word(word_subword (b:128 word) (0,64) : 64 word)` THEN
  ABBREV_TAC `bh = poly_of_word(word_subword (b:128 word) (64,64) : 64 word)` THEN
  ABBREV_TAC `x64 = ring_pow bool_poly (poly_var bool_ring one) 64` THEN
  SUBGOAL_THEN
    `al IN ring_carrier bool_poly /\ ah IN ring_carrier bool_poly /\
     bl IN ring_carrier bool_poly /\ bh IN ring_carrier bool_poly /\
     x64 IN ring_carrier bool_poly`
    STRIP_ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["al";"ah";"bl";"bh";"x64"] THEN
   SIMP_TAC[BOOL_POLY_OF_WORD; RING_POW; POLY_VAR_BOOL_POLY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`al:((1->num)->bool)`; `bl:((1->num)->bool)`;
                 `ah:((1->num)->bool)`; `bh:((1->num)->bool)`;
                 `bool_poly`; `x64:((1->num)->bool)`] SCHOOLBOOK_RING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `ring_mul bool_poly x64 x64 =
                ring_pow bool_poly (poly_var bool_ring one) 128`
    SUBST1_TAC THENL
  [EXPAND_TAC "x64" THEN SIMP_TAC[GSYM RING_POW_ADD; POLY_VAR_BOOL_POLY] THEN
   CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN
    `ring_mul bool_poly al bl IN ring_carrier bool_poly /\
     ring_mul bool_poly (ring_add bool_poly (ring_mul bool_poly al bh)
                                            (ring_mul bool_poly ah bl)) x64
       IN ring_carrier bool_poly /\
     ring_mul bool_poly (ring_mul bool_poly ah bh)
                        (ring_pow bool_poly (poly_var bool_ring one) 128)
       IN ring_carrier bool_poly`
    STRIP_ASSUME_TAC THENL
  [ASM_SIMP_TAC[RING_MUL; RING_ADD; RING_POW; POLY_VAR_BOOL_POLY]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_ADD_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Main theorem: Karatsuba decomposition of carry-less multiplication.       *)
(* word_pmul(a,b) = p_lo XOR shl(mid,64) XOR shl(p_hi,128)                   *)
(* where mid = p_mid XOR p_lo XOR p_hi (Karatsuba tidy-up).                  *)
(* Proof: schoolbook identity (RING_RULE) + char-2 tidy-up (WORD_BITWISE).   *)
(* ------------------------------------------------------------------------- *)

let PMUL_KARATSUBA = prove(
  `!(a:128 word) (b:128 word).
    let a_lo = word_subword a (0,64) : 64 word in
    let a_hi = word_subword a (64,64) : 64 word in
    let b_lo = word_subword b (0,64) : 64 word in
    let b_hi = word_subword b (64,64) : 64 word in
    let p_lo = word_pmul a_lo b_lo : 128 word in
    let p_hi = word_pmul a_hi b_hi : 128 word in
    let p_mid = word_pmul (word_xor a_lo a_hi) (word_xor b_lo b_hi) : 128 word in
    let mid = word_xor (word_xor p_mid p_lo) p_hi in
    (word_pmul a b : 256 word) =
    word_xor (word_xor (word_zx p_lo : 256 word)
                        (word_shl (word_zx mid : 256 word) 64))
             (word_shl (word_zx p_hi : 256 word) 128)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC(LAND_CONV(REWR_CONV(REWRITE_RULE[LET_DEF; LET_END_DEF]
    (SPECL [`a:128 word`; `b:128 word`] PMUL_SCHOOLBOOK)))) THEN
  BINOP_TAC THENL [ALL_TAC; REFL_TAC] THEN
  BINOP_TAC THENL [REFL_TAC; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_PMUL_XOR] THEN CONV_TAC WORD_BITWISE_RULE);;
