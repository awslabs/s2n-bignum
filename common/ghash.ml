(* ========================================================================= *)
(* GHASH polynomial both via machine words and as an element of GF(2)[X].    *)
(* ========================================================================= *)

needs "common/misc.ml";;
needs "Library/rabin_test.ml";;

(* ------------------------------------------------------------------------- *)
(* Some basics for univariate polynomials to be less tiresome.               *)
(* The library theory of polynomials has some cruft for arbitrary monomials. *)
(* ------------------------------------------------------------------------- *)

let coeff = define
 `coeff:num->1->num = \d v. d`;;

let POLY_MUL_UNIVARIATE = prove
 (`!r (p:(1->num)->R) q.
      poly_mul r p q =
      \m. ring_sum r (0..m one)
              (\i. ring_mul r (p(coeff i)) (q(coeff(m one - i))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[poly_mul; coeff] THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  GEN_REWRITE_TAC I [FORALL_FUN_FROM_1] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC RING_SUM_EQ_GENERAL_INVERSES THEN
  EXISTS_TAC `\mm. (FST:(1->num)#(1->num)->1->num) mm one` THEN
  EXISTS_TAC `\i. (\v:1. i),(\v:1. k - i)` THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_ELIM_PAIR_THM] THEN
  REWRITE_TAC[FORALL_FUN_FROM_1; coeff; monomial_mul] THEN
  REWRITE_TAC[MESON[] `(\x:1. a) = (\x. b) <=> a = b`] THEN
  REWRITE_TAC[IN_NUMSEG; LE_0] THEN
  SIMP_TAC[ARITH_RULE `i + j:num = k <=> i <= k /\ j = k - i`]);;

(* ------------------------------------------------------------------------- *)
(* A lemma for mapping between integer and boolean points of view            *)
(* ------------------------------------------------------------------------- *)

let BITVAL_RING_SUM_BOOL_RING = prove
 (`!f (s:K->bool).
        FINITE s
        ==> bitval(ring_sum bool_ring s f) = nsum s (bitval o f) MOD 2`,
  GEN_TAC THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NSUM_CLAUSES; RING_SUM_CLAUSES; BOOL_RING; IN_UNIV] THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `s:K->bool`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[BITVAL_NOT; BITVAL_IFF; BITVAL_CLAUSES] THEN
  REWRITE_TAC[o_THM; bitval] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Correspondence between binary polynomials and machine words.              *)
(* Polynomials are members of `poly_ring bool_ring (:1)` = GF(2)[X].         *)
(* They are mapped to and from machine words of length N, type `:N word`.    *)
(* ------------------------------------------------------------------------- *)

let bool_poly = define
 `bool_poly = poly_ring bool_ring (:1)`;;

let word_of_poly = define
 `(word_of_poly:((1->num)->bool)->N word) p = word_of_bits {i | p(coeff i)}`;;

let poly_of_word = define
 `(poly_of_word:N word->(1->num)->bool) w = \m. bit (m one) w`;;

let BOOL_POLY_OF_WORD = prove
 (`!w:N word. poly_of_word w IN ring_carrier bool_poly`,
  REWRITE_TAC[bool_poly; POLY_RING; ring_polynomial; ring_powerseries;
              IN_ELIM_THM; BOOL_RING; SUBSET_UNIV; IN_UNIV] THEN
  REWRITE_TAC[FINITE_MONOMIAL_VARS_1; INFINITE] THEN
  REWRITE_TAC[poly_of_word] THEN GEN_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE coeff {i | i < dimindex(:N)}` THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
  REWRITE_TAC[FORALL_FUN_FROM_1; IN_IMAGE; IN_ELIM_THM; coeff] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let POLY_DEG_POLY_OF_WORD = prove
 (`!w:N word. poly_deg bool_ring (poly_of_word w) < dimindex(:N)`,
  GEN_TAC THEN
  SIMP_TAC[DIMINDEX_NONZERO; ARITH_RULE
   `~(n = 0) ==> (x < n <=> x <= n - 1)`] THEN
  MATCH_MP_TAC POLY_DEG_LE THEN
  REWRITE_TAC[RING_POLYNOMIAL; BOOL_POLY_OF_WORD; GSYM bool_poly] THEN
  REWRITE_TAC[FORALL_FUN_FROM_1; BOOL_RING; MONOMIAL_DEG_UNIVARIATE] THEN
  REWRITE_TAC[poly_of_word; coeff] THEN
  ONCE_REWRITE_TAC[BIT_GUARD] THEN ARITH_TAC);;

let WORD_OF_POLY_OF_WORD = prove
 (`!w:N word. word_of_poly (poly_of_word w) = w`,
  GEN_TAC THEN REWRITE_TAC[word_of_poly; poly_of_word] THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  SIMP_TAC[BIT_WORD_OF_BITS; coeff; IN_ELIM_THM]);;

let WORD_OF_POLY_OF_WORD_GEN = prove
 (`!w:N word. word_of_poly (poly_of_word w):M word = word_zx w`,
  GEN_TAC THEN REWRITE_TAC[word_of_poly; poly_of_word] THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  SIMP_TAC[BIT_WORD_OF_BITS; BIT_WORD_ZX; coeff; IN_ELIM_THM]);;

let POLY_OF_WORD_OF_POLY = prove
 (`!p. p IN ring_carrier bool_poly /\
       poly_deg bool_ring p < dimindex(:N)
       ==> poly_of_word (word_of_poly p:N word) = p`,
  REWRITE_TAC[bool_poly; GSYM RING_POLYNOMIAL] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `dimindex(:N)` o MATCH_MP POLY_DEG_GE_EQ) THEN
  ASM_REWRITE_TAC[GSYM NOT_LT; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  GEN_REWRITE_TAC RAND_CONV [FUN_EQ_THM] THEN
  REWRITE_TAC[FORALL_FUN_FROM_1; word_of_poly; poly_of_word] THEN
  REWRITE_TAC[BIT_WORD_OF_BITS; coeff; BOOL_RING; MONOMIAL_DEG_UNIVARIATE] THEN
  SET_TAC[]);;

let POLY_OF_WORD_OF_POLY_EQ = prove
 (`!p. p IN ring_carrier bool_poly
       ==> (poly_of_word (word_of_poly p:N word) = p <=>
            poly_deg bool_ring p < dimindex(:N))`,
  MESON_TAC[POLY_OF_WORD_OF_POLY; POLY_DEG_POLY_OF_WORD]);;

(* ------------------------------------------------------------------------- *)
(* XOR and PMUL correspond to addition and multiplication of polynomials.    *)
(* ------------------------------------------------------------------------- *)

let WORD_XOR_POLY = prove
 (`!x y:N word.
        word_xor x y =
        word_of_poly (ring_add bool_poly (poly_of_word x) (poly_of_word y))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[word_of_poly; bool_poly; POLY_RING; BOOL_RING; poly_add] THEN
  REWRITE_TAC[BIT_WORD_OF_BITS; IN_ELIM_THM; BIT_WORD_XOR] THEN
  REWRITE_TAC[poly_of_word; coeff]);;

let POLY_OF_WORD_XOR = prove
 (`!(x:N word) (y:N word).
        poly_of_word(word_xor x y) =
        ring_add bool_poly (poly_of_word x) (poly_of_word y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_XOR_POLY] THEN
  MATCH_MP_TAC POLY_OF_WORD_OF_POLY THEN
  SIMP_TAC[RING_ADD; BOOL_POLY_OF_WORD] THEN
  REWRITE_TAC[bool_poly; POLY_RING] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_ADD_LE o lhand o snd) THEN
  REWRITE_TAC[RING_POLYNOMIAL; BOOL_POLY_OF_WORD; GSYM bool_poly] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS) THEN
  MATCH_MP_TAC(ARITH_RULE `x < n /\ y < n ==> MAX x y < n`) THEN
  REWRITE_TAC[POLY_DEG_POLY_OF_WORD]);;

let WORD_PMUL_POLY = prove
 (`!x y. (word_pmul:M word->N word->P word) x y =
         word_of_poly (ring_mul bool_poly (poly_of_word x) (poly_of_word y))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[GSYM EQ_BITVAL; BITVAL_BIT_WORD_PMUL] THEN
  REWRITE_TAC[word_of_poly; bool_poly; POLY_RING] THEN
  ASM_REWRITE_TAC[POLY_MUL_UNIVARIATE; BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
  REWRITE_TAC[coeff; BOOL_RING] THEN
  SIMP_TAC[BITVAL_RING_SUM_BOOL_RING; FINITE_NUMSEG] THEN
  REWRITE_TAC[o_DEF; BITVAL_AND; poly_of_word]);;

let POLY_OF_WORD_PMUL_2N = prove
 (`!(x:N word) (y:N word).
        poly_of_word(word_pmul x y:((N)tybit0)word) =
        ring_mul bool_poly (poly_of_word x) (poly_of_word y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_PMUL_POLY] THEN
  MATCH_MP_TAC POLY_OF_WORD_OF_POLY THEN
  SIMP_TAC[RING_MUL; BOOL_POLY_OF_WORD; DIMINDEX_TYBIT0] THEN
  REWRITE_TAC[bool_poly; POLY_RING] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_MUL_LE o lhand o snd) THEN
  REWRITE_TAC[RING_POLYNOMIAL; BOOL_POLY_OF_WORD; GSYM bool_poly] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS) THEN
  MATCH_MP_TAC(ARITH_RULE `x < n /\ y < n ==> x + y < 2 * n`) THEN
  REWRITE_TAC[POLY_DEG_POLY_OF_WORD]);;
