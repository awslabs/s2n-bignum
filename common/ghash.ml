(* ========================================================================= *)
(* GHASH polynomial both via machine words and as an element of GF(2)[X].    *)
(* ========================================================================= *)

needs "common/misc.ml";;
needs "Library/rabin_test.ml";;

(* ------------------------------------------------------------------------- *)
(* General trivia                                                            *)
(* ------------------------------------------------------------------------- *)

let BOOL_RING_SUB = prove
 (`ring_sub bool_ring = \x y. ~(x <=> y)`,
  SIMP_TAC[FUN_EQ_THM; ring_sub; BOOL_RING; I_DEF]);;

let POLY_RING_VAR_POW_1 = prove
 (`!(r:A ring) i.
         ring_pow (poly_ring r (:1)) (poly_var r i) k =
         \m. if m = \j. k then ring_1 r else ring_0 r`,
  REWRITE_TAC[POLY_RING_VAR_POW] THEN
  REWRITE_TAC[MESON[one] `i:1 = j <=> T`]);;

(* ------------------------------------------------------------------------- *)
(* Some basics for univariate polynomials to be less tiresome.               *)
(* The library theory of polynomials has some cruft for arbitrary monomials. *)
(* ------------------------------------------------------------------------- *)

let coeff = define
 `coeff = \i (p:(1->num)->A). p(\v:1. i)`;;

let POLY_MUL_UNIVARIATE = prove
 (`!r (p:(1->num)->R) q.
      poly_mul r p q =
      \m. ring_sum r (0..m one)
              (\i. ring_mul r (coeff i p) (coeff (m one - i) q))`,
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

let BOOL_POLY_NEG = prove
 (`ring_neg bool_poly = I`,
  REWRITE_TAC[FUN_EQ_THM; bool_poly; POLY_RING; BOOL_RING; poly_neg; I_DEF]);;

let BOOL_POLY_SUB = prove
 (`ring_sub bool_poly = ring_add bool_poly`,
  REWRITE_TAC[FUN_EQ_THM; bool_poly; POLY_RING_CLAUSES;
              BOOL_RING; poly_add; poly_sub; BOOL_RING_SUB]);;

let POLY_VAR_BOOL_POLY = prove
 (`poly_var bool_ring one IN ring_carrier bool_poly`,
  REWRITE_TAC[bool_poly; POLY_VAR; IN_UNIV]);;

let POLY_VARPOW_BOOL_POLY = prove
 (`!n. ring_pow bool_poly (poly_var bool_ring one) n IN ring_carrier bool_poly`,
  SIMP_TAC[RING_POW; POLY_VAR_BOOL_POLY]);;

let word_of_poly = define
 `(word_of_poly:((1->num)->bool)->N word) p = word_of_bits {i | coeff i p}`;;

let poly_of_word = define
 `(poly_of_word:N word->(1->num)->bool) w = \m. bit (m one) w`;;

let BOOL_POLY_OF_WORD = prove
 (`!w:N word. poly_of_word w IN ring_carrier bool_poly`,
  REWRITE_TAC[bool_poly; POLY_RING; ring_polynomial; ring_powerseries;
              IN_ELIM_THM; BOOL_RING; SUBSET_UNIV; IN_UNIV] THEN
  REWRITE_TAC[FINITE_MONOMIAL_VARS_1; INFINITE] THEN
  REWRITE_TAC[poly_of_word] THEN GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\i (v:1). i) {i | i < dimindex(:N)}` THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
  REWRITE_TAC[FORALL_FUN_FROM_1; IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let RING_POLYNOMIAL_OF_WORD = prove
 (`!w:N word. ring_polynomial bool_ring (poly_of_word w)`,
  REWRITE_TAC[RING_POLYNOMIAL; GSYM bool_poly; BOOL_POLY_OF_WORD]);;

let POLY_DEG_POLY_OF_WORD = prove
 (`!w:N word.
        poly_deg bool_ring (poly_of_word w) =
        dimindex(:N) - 1 - word_clz w`,
  GEN_TAC THEN MATCH_MP_TAC POLY_DEG_UNIQUE THEN
  REWRITE_TAC[RING_POLYNOMIAL_OF_WORD] THEN
  REWRITE_TAC[MONOMIAL_DEG_UNIVARIATE; poly_of_word] THEN
  SIMP_TAC[FORALL_FUN_FROM_1; EXISTS_FUN_FROM_1; MONOMIAL_DEG_UNIVARIATE] THEN
  REWRITE_TAC[BOOL_RING] THEN
  SIMP_TAC[WORD_CLZ_LBOUND_ALT; ARITH_RULE `c + i < n ==> i <= n - 1 - c`] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  MP_TAC(ISPECL [`w:N word`; `word_clz(w:N word)`] WORD_CLZ_UNIQUE) THEN
  REWRITE_TAC[ARITH_RULE `n - 1 - w = n - w - 1`] THEN
  ASM_CASES_TAC `bit (dimindex(:N) - word_clz w - 1) (w:N word)` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let POLY_DEG_POLY_OF_WORD_BOUND = prove
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

let POLY_OF_WORD_ZX = prove
 (`!x. dimindex(:M) <= dimindex(:N)
       ==> poly_of_word((word_zx:M word->N word) x) = poly_of_word x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM WORD_OF_POLY_OF_WORD_GEN] THEN
  MATCH_MP_TAC POLY_OF_WORD_OF_POLY THEN
  ASM_MESON_TAC[POLY_DEG_POLY_OF_WORD_BOUND; LTE_TRANS; BOOL_POLY_OF_WORD]);;

let POLY_OF_WORD_OF_POLY_EQ = prove
 (`!p. p IN ring_carrier bool_poly
       ==> (poly_of_word (word_of_poly p:N word) = p <=>
            poly_deg bool_ring p < dimindex(:N))`,
  MESON_TAC[POLY_OF_WORD_OF_POLY; POLY_DEG_POLY_OF_WORD_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* XOR and PMUL correspond to addition and multiplication of polynomials.    *)
(* ------------------------------------------------------------------------- *)

let POLY_OF_WORD_0 = prove
 (`poly_of_word (word 0:N word) = ring_0 bool_poly`,
  REWRITE_TAC[poly_of_word; bool_poly; BIT_WORD_0; POLY_0] THEN
  REWRITE_TAC[POLY_RING; BOOL_RING; POLY_0]);;

let POLY_OF_WORD_1 = prove
 (`poly_of_word (word 1:N word) = ring_1 bool_poly`,
  REWRITE_TAC[poly_of_word; bool_poly; BIT_WORD_1; POLY_RING; poly_1] THEN
  REWRITE_TAC[BOOL_RING; poly_const; monomial_1] THEN
  REWRITE_TAC[MESON[] `(if p then T else F) <=> p`] THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN REWRITE_TAC[FORALL_FUN_FROM_1] THEN
  REWRITE_TAC[FUN_EQ_THM]);;

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
  REWRITE_TAC[POLY_DEG_POLY_OF_WORD_BOUND]);;

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
  REWRITE_TAC[POLY_DEG_POLY_OF_WORD_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* The GHASH polynomial p(x) = x^128 + x^7 + x^2 + x + 1                     *)
(* ------------------------------------------------------------------------- *)

let ghash_poly = define
 `ghash_poly =
  ring_sum bool_poly {128,7,2,1,0}
    (\i. ring_pow bool_poly (poly_var bool_ring one) i)`;;

let GHASH_BOOL_POLY = prove
 (`ghash_poly IN ring_carrier bool_poly`,
  REWRITE_TAC[ghash_poly; RING_SUM]);;

let RING_POLYNOMIAL_GHASH_POLY = prove
 (`ring_polynomial bool_ring ghash_poly`,
  REWRITE_TAC[RING_POLYNOMIAL; GSYM bool_poly; GHASH_BOOL_POLY]);;

let GHASH_POLY_OF_WORD = prove
 (`128 < dimindex(:N)
   ==> ghash_poly =
       poly_of_word(word 0x100000000000000000000000000000087:N word)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ghash_poly] THEN
  SIMP_TAC[RING_SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
           IN_INSERT; ARITH_EQ; NOT_IN_EMPTY] THEN
  REWRITE_TAC[POLY_VARPOW_BOOL_POLY] THEN
  REWRITE_TAC[bool_poly; POLY_RING_VAR_POW_1] THEN
  REWRITE_TAC[POLY_RING; poly_add; POLY_0; poly_of_word] THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  REWRITE_TAC[FORALL_FUN_FROM_1] THEN
  REWRITE_TAC[FUN_EQ_THM; BOOL_RING] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i < 129` THENL
   [POP_ASSUM MP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[BIT_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `F` THEN CONJ_TAC THENL
   [REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC;
    REWRITE_TAC[BIT_WORD]] THEN
  MATCH_MP_TAC(MESON[ODD] `n = 0 ==> ~(p /\ ODD n)`) THEN
  SIMP_TAC[DIV_EQ_0; ARITH_EQ; EXP_EQ_0] THEN
  TRANS_TAC LTE_TRANS `2 EXP 129` THEN REWRITE_TAC[LE_EXP] THEN
  ASM_ARITH_TAC);;

let POLY_DEG_GHASH_POLY = prove
 (`poly_deg bool_ring ghash_poly = 128`,
  MP_TAC(INST_TYPE [`:129`,`:N`] GHASH_POLY_OF_WORD) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[POLY_DEG_POLY_OF_WORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Equivalence modulo the ghash polynomial, and reduction at word level      *)
(* ------------------------------------------------------------------------- *)

let mod_ghash = define
 `mod_ghash p q <=>
  p IN ring_carrier bool_poly /\ q IN ring_carrier bool_poly /\
  ring_sub bool_poly p q IN ideal_generated bool_poly {ghash_poly}`;;

let MOD_GHASH_0 = prove
 (`!p. (p == ring_0 bool_poly) (mod_ghash) <=>
       ring_divides bool_poly ghash_poly p`,
  GEN_TAC THEN REWRITE_TAC[mod_ghash; cong; ring_divides] THEN
  ASM_CASES_TAC `p IN ring_carrier bool_poly` THEN
  ASM_SIMP_TAC[IN_IDEAL_GENERATED_SING_EQ; RING_SUB_RZERO; GHASH_BOOL_POLY;
               ring_divides; RING_0]);;

let MOD_GHASH_REFL = prove
 (`!p. (p == p) (mod_ghash) <=> p IN ring_carrier bool_poly`,
  GEN_TAC THEN REWRITE_TAC[cong; mod_ghash] THEN
  ASM_CASES_TAC `p IN ring_carrier bool_poly` THEN
  ASM_SIMP_TAC[RING_SUB_REFL; IN_RING_IDEAL_0; RING_IDEAL_IDEAL_GENERATED]);;

let MOD_GHASH_REFL_GEN = prove
 (`!p q. p IN ring_carrier bool_poly /\ q = p ==> (p == q) (mod_ghash)`,
  MESON_TAC[MOD_GHASH_REFL]);;

let MOD_GHASH_SYM = prove
 (`!p q. (p == q) (mod_ghash) <=> (q == p) (mod_ghash)`,
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`p IN ring_carrier bool_poly`; `q IN ring_carrier bool_poly`] THEN
  ASM_REWRITE_TAC[cong; mod_ghash] THEN
  ASM_MESON_TAC[IN_RING_IDEAL_NEG; RING_IDEAL_IDEAL_GENERATED;
                RING_RULE `ring_neg r (ring_sub r a b) = ring_sub r b a`]);;

let MOD_GHASH_TRANS = prove
 (`!p q r.
      (p == q) (mod_ghash) /\ (q == r) (mod_ghash) ==> (p == r) (mod_ghash)`,
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`p IN ring_carrier bool_poly`; `q IN ring_carrier bool_poly`;
    `r IN ring_carrier bool_poly`] THEN
  ASM_REWRITE_TAC[cong; mod_ghash] THEN
  ASM_MESON_TAC[IN_RING_IDEAL_ADD; RING_IDEAL_IDEAL_GENERATED; RING_RULE
   `ring_add r (ring_sub r a b) (ring_sub r b c) = ring_sub r a c`]);;

let MOD_GHASH_ADD = prove
 (`!p p' q q'.
      (p == p') (mod_ghash) /\ (q == q') (mod_ghash)
      ==> (ring_add bool_poly p q == ring_add bool_poly p' q') (mod_ghash)`,
 REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`p IN ring_carrier bool_poly`; `p' IN ring_carrier bool_poly`;
    `q IN ring_carrier bool_poly`; `q' IN ring_carrier bool_poly`] THEN
  ASM_SIMP_TAC[cong; mod_ghash; RING_ADD] THEN
  ASM_MESON_TAC[IN_RING_IDEAL_ADD; RING_IDEAL_IDEAL_GENERATED; RING_RULE
   `ring_add r (ring_sub r p p') (ring_sub r q q') =
    ring_sub r (ring_add r p q) (ring_add r p' q')`]);;

let MOD_GHASH_SUB = prove
 (`!p p' q q'.
      (p == p') (mod_ghash) /\ (q == q') (mod_ghash)
      ==> (ring_sub bool_poly p q == ring_sub bool_poly p' q') (mod_ghash)`,
 REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`p IN ring_carrier bool_poly`; `p' IN ring_carrier bool_poly`;
    `q IN ring_carrier bool_poly`; `q' IN ring_carrier bool_poly`] THEN
  ASM_SIMP_TAC[cong; mod_ghash; RING_SUB] THEN
  ASM_MESON_TAC[IN_RING_IDEAL_SUB; RING_IDEAL_IDEAL_GENERATED; RING_RULE
   `ring_sub r (ring_sub r p p') (ring_sub r q q') =
    ring_sub r (ring_sub r p q) (ring_sub r p' q')`]);;

let MOD_GHASH_MUL = prove
 (`!p p' q q'.
      (p == p') (mod_ghash) /\ (q == q') (mod_ghash)
      ==> (ring_mul bool_poly p q == ring_mul bool_poly p' q') (mod_ghash)`,
 REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`p IN ring_carrier bool_poly`; `p' IN ring_carrier bool_poly`;
    `q IN ring_carrier bool_poly`; `q' IN ring_carrier bool_poly`] THEN
  ASM_SIMP_TAC[cong; mod_ghash; RING_MUL] THEN
  ASM_MESON_TAC[IN_RING_IDEAL_ADD; IN_RING_IDEAL_LMUL;
                RING_IDEAL_IDEAL_GENERATED; RING_RULE
   `ring_add r (ring_mul r q (ring_sub r p p'))
               (ring_mul r p' (ring_sub r q q')) =
    ring_sub r (ring_mul r p q) (ring_mul r p' q')`]);;

let ghash_reduce1 = define
 `ghash_reduce1 (x:N word) =
  word_xor (word_subword x (0,128):N word)
           (word_pmul (word_ushr x 128) (word 0x87:N word))`;;

let GHASH_REDUCE1 = prove
 (`!x:N word.
        ghash_reduce1 x =
        word_xor (word_subword x (0,128))
         (word_xor (word_shl (word_ushr x 128) 7)
           (word_xor (word_shl (word_ushr x 128) 2)
             (word_xor (word_shl (word_ushr x 128) 1)
                       (word_ushr x 128))))`,
  let lemma = prove
   (`word 0x87:N word = word_zx(word 0x87:byte)`,
    REWRITE_TAC[word_zx] THEN CONV_TAC WORD_REDUCE_CONV) in
  GEN_TAC THEN REWRITE_TAC[ghash_reduce1] THEN
  ONCE_REWRITE_TAC[WORD_PMUL_SYM] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[lemma] THEN
  ASM_REWRITE_TAC[BIT_WORD_XOR_ALT; BIT_WORD_PMUL] THEN
  ASM_REWRITE_TAC[BIT_WORD_SHL; BIT_WORD_USHR] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[BIT_WORD_ZX; BIT_WORD; DIMINDEX_8] THEN
  REWRITE_TAC[GSYM BITVAL_AND; GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
  REWRITE_TAC[bitval] THEN ONCE_REWRITE_TAC[MESON[]
   `(if p /\ q then a else b) = if p then (if q then a else b) else b`] THEN
  ONCE_REWRITE_TAC[GSYM NSUM_RESTRICT_SET] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{i | i IN s /\ P i} = {i | i IN {j | P j} /\ i IN s}`] THEN
  REWRITE_TAC[NSUM_RESTRICT_SET] THEN
  REWRITE_TAC[NUMSEG_LT; ARITH; IN_NUMSEG; LE_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[COND_ID; ADD_CLAUSES] THEN
  REWRITE_TAC[MESON[]
   `(if p then (if q then a else b) else b) = (if p /\ q then a else b)`] THEN
  REWRITE_TAC[GSYM bitval; ODD_ADD; ODD_BITVAL] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  ASM_SIMP_TAC[ARITH_RULE `i:num < N ==> (a <= i /\ a < N <=> a <= i)`] THEN
  REWRITE_TAC[ADD_CLAUSES; SUB_0; LE_0] THEN CONV_TAC TAUT);;

let POLY_EQUIV_GHASH_REDUCE1 = prove
 (`!x:N word. (poly_of_word(ghash_reduce1 x) == poly_of_word x) (mod_ghash)`,
  let lemma = prove
   (`!x:N word.
          word_subword x (0,128) =
          word_xor x (word_shl (word_ushr x 128) 128)`,
    GEN_TAC THEN ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
    SIMP_TAC[BIT_WORD_SUBWORD; BIT_WORD_XOR; BIT_WORD_SHL; BIT_WORD_USHR] THEN
    SIMP_TAC[ADD_CLAUSES; ARITH_RULE `i < MIN a b <=> i < a /\ i < b`] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `128 <= i` THEN ASM_SIMP_TAC[GSYM NOT_LE; SUB_ADD]) in
  GEN_TAC THEN REWRITE_TAC[cong; mod_ghash; BOOL_POLY_OF_WORD] THEN
  SIMP_TAC[IDEAL_GENERATED_SING; GHASH_BOOL_POLY; IN_ELIM_THM] THEN
  REWRITE_TAC[ring_divides; GHASH_BOOL_POLY] THEN
  SIMP_TAC[RING_SUB; BOOL_POLY_OF_WORD] THEN
  EXISTS_TAC `poly_of_word(word_ushr x 128:N word)` THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD] THEN
  REWRITE_TAC[ghash_reduce1; lemma] THEN
  REWRITE_TAC[BOOL_POLY_SUB; GSYM POLY_OF_WORD_XOR] THEN
  REWRITE_TAC[WORD_BITWISE_RULE
   `word_xor (word_xor (word_xor x a) b) x = word_xor a b`] THEN
  ASM_CASES_TAC `word_ushr x 128:N word = word 0` THENL
   [ASM_REWRITE_TAC[POLY_OF_WORD_0; WORD_PMUL_0; WORD_SHL_0; WORD_XOR_0] THEN
    SIMP_TAC[RING_MUL_RZERO; GHASH_BOOL_POLY];
    ALL_TAC] THEN
  SUBGOAL_THEN `128 < dimindex(:N)` MP_TAC THENL
   [POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_LT; WORD_USHR_EQ_0] THEN DISCH_TAC THEN
    TRANS_TAC LTE_TRANS `2 EXP dimindex(:N)` THEN
    REWRITE_TAC[VAL_BOUND; LE_EXP] THEN ASM_ARITH_TAC;
    POP_ASSUM(K ALL_TAC) THEN DISCH_TAC] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 WORD_PMUL_POW2)] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 WORD_PMUL_XOR)] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_PMUL_SYM] THEN
  MP_TAC(ISPECL [`word(2 EXP 128):N word`; `word 0x87:N word`]
    WORD_ADD_XOR) THEN
  REWRITE_TAC[WORD_AND_POW2; BIT_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_PMUL_POLY] THEN
  ASM_SIMP_TAC[GSYM GHASH_POLY_OF_WORD] THEN
  MATCH_MP_TAC POLY_OF_WORD_OF_POLY THEN
  SIMP_TAC[RING_MUL; GHASH_BOOL_POLY; BOOL_POLY_OF_WORD] THEN
  REWRITE_TAC[bool_poly; POLY_RING] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_MUL_LE o lhand o snd) THEN
  REWRITE_TAC[RING_POLYNOMIAL_GHASH_POLY; POLY_DEG_GHASH_POLY;
              POLY_DEG_POLY_OF_WORD; RING_POLYNOMIAL_OF_WORD] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS) THEN
  MATCH_MP_TAC(ARITH_RULE `128 < n /\ 128 <= c ==> 128 + n - 1 - c < n`) THEN
  ASM_SIMP_TAC[WORD_LE_CLZ; LT_IMP_LE; BIT_WORD_USHR] THEN
  MESON_TAC[BIT_GUARD]);;

(* ------------------------------------------------------------------------- *)
(* Fixed-size eduction from 256 to 128 bits: 2 rounds of simple reduction.   *)
(* ------------------------------------------------------------------------- *)

let ghash_reduce = define
 `(ghash_reduce:256 word -> 128 word) x =
  word_zx(ghash_reduce1(ghash_reduce1 x))`;;

let POLY_EQUIV_GHASH_REDUCE = prove
 (`!x. (poly_of_word(ghash_reduce x) == poly_of_word x) (mod_ghash)`,
  GEN_TAC THEN
  MP_TAC(ISPEC `x:256 word` POLY_EQUIV_GHASH_REDUCE1) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] MOD_GHASH_TRANS) THEN
  MP_TAC(ISPEC `ghash_reduce1 x:256 word` POLY_EQUIV_GHASH_REDUCE1) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] MOD_GHASH_TRANS) THEN
  REWRITE_TAC[ghash_reduce; GSYM WORD_OF_POLY_OF_WORD_GEN] THEN
  MATCH_MP_TAC MOD_GHASH_REFL_GEN THEN REWRITE_TAC[BOOL_POLY_OF_WORD] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC POLY_OF_WORD_OF_POLY THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_DEG_POLY_OF_WORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  MATCH_MP_TAC(ARITH_RULE `128 <= a ==> 256 - 1 - a < 128`) THEN
  REWRITE_TAC[WORD_LE_CLZ] THEN ONCE_REWRITE_TAC[BIT_GUARD] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[TAUT `p /\ q ==> r <=> p ==> ~r ==> ~q`] THEN
  REWRITE_TAC[GHASH_REDUCE1] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Some explicit computations of high powers of X.                           *)
(* ------------------------------------------------------------------------- *)

let [X_POWPOW_128; X_POWPOW_64] =
  let base = prove
   (`(ring_pow bool_poly (poly_var bool_ring one) (2 EXP 0) ==
      poly_of_word(word 0x2:int128)) (mod_ghash)`,
    MATCH_MP_TAC MOD_GHASH_REFL_GEN THEN
    REWRITE_TAC[POLY_VARPOW_BOOL_POLY] THEN
    REWRITE_TAC[EXP; POLY_RING_VAR_POW_1; bool_poly] THEN
    REWRITE_TAC[poly_of_word] THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    GEN_REWRITE_TAC I [FORALL_FUN_FROM_1] THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN
    REWRITE_TAC[MESON[] `(\x:1. a) = (\x. b) <=> a = b`] THEN
    REWRITE_TAC[BOOL_RING; MESON[] `(if p then T else F) <=> p`] THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (ARITH_RULE `k = 0 \/ k = 1 \/ 2 <= k`) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC(TAUT `~q /\ ~p ==> (p <=> q)`) THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[BIT_WORD]] THEN
    UNDISCH_TAC `2 <= k` THEN
    REWRITE_TAC[TAUT `r ==> ~(p /\ q) <=> p ==> r ==> ~q`] THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    SPEC_TAC(`k:num`,`k:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV)
  and step = prove
   (`!(x:int128) n.
     (ring_pow bool_poly (poly_var bool_ring one) (2 EXP n) ==
      poly_of_word x) (mod_ghash)
     ==> (ring_pow bool_poly (poly_var bool_ring one) (2 EXP SUC n) ==
          poly_of_word(ghash_reduce(word_pmul x x))) (mod_ghash)`,
    REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOD_GHASH_MUL o W CONJ) THEN
    SIMP_TAC[GSYM RING_POW_2; POLY_VARPOW_BOOL_POLY] THEN
    SIMP_TAC[RING_POW_POW; POLY_VAR_BOOL_POLY] THEN
    REWRITE_TAC[EXP; MULT_SYM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] MOD_GHASH_TRANS) THEN
    REWRITE_TAC[GSYM POLY_OF_WORD_PMUL_2N] THEN
    ONCE_REWRITE_TAC[MOD_GHASH_SYM] THEN
    REWRITE_TAC[POLY_EQUIV_GHASH_REDUCE]) in
  let rec rules n =
    if n = 0 then [base] else
    let lis = rules(n - 1) in
    let th1 = MATCH_MP step (hd lis) in
    let th2 = CONV_RULE(RATOR_CONV(BINOP2_CONV
               (RAND_CONV(RAND_CONV NUM_SUC_CONV))
               (ONCE_DEPTH_CONV WORD_PMUL_CONV THENC
                REWRITE_CONV[ghash_reduce; ghash_reduce1] THENC
                DEPTH_CONV(WORD_RED_CONV ORELSEC WORD_PMUL_CONV)))) th1 in
    th2::lis in
  let lis = rev(rules 128) in
  let th_0 = SIMP_RULE[EXP; RING_POW_1; POLY_VAR_BOOL_POLY] (el 0 lis)
  and th_64 = el 64 lis
  and th_128 = el 128 lis in
  map
   (REWRITE_RULE[GSYM BOOL_POLY_SUB; POLY_OF_WORD_0] o
    CONV_RULE WORD_REDUCE_CONV o
    REWRITE_RULE[GSYM POLY_OF_WORD_XOR; BOOL_POLY_SUB])
   [MATCH_MP MOD_GHASH_SUB (CONJ th_128 th_0);
    MATCH_MP MOD_GHASH_SUB (CONJ th_64 th_0)];;

(* ------------------------------------------------------------------------- *)
(* Now use the Rabin test to prove irreducibility.                           *)
(* ------------------------------------------------------------------------- *)

let FINITE_BOOL_RING = prove
 (`FINITE(ring_carrier bool_ring)`,
  REWRITE_TAC[BOOL_RING; FINITE_BOOL]);;

let CARD_BOOL_RING = prove
 (`CARD(ring_carrier bool_ring) = 2`,
  REWRITE_TAC[BOOL_RING; CARD_BOOL]);;

let BEZOUT_BOOL_POLY = prove
 (`bezout_ring bool_poly`,
  REWRITE_TAC[bool_poly] THEN
  MESON_TAC[PID_EQ_UFD_BEZOUT_RING; PID_POLY_RING; FIELD_BOOL_RING]);;

let RING_IRREDUCBLE_GHASH_POLYNOMIAL = prove
 (`ring_irreducible bool_poly ghash_poly`,
  let lemma = prove
   (`!s t. s IN ring_carrier bool_poly /\
           t IN ring_carrier bool_poly /\
           ring_add bool_poly (ring_mul bool_poly s ghash_poly)
                              (ring_mul bool_poly t p') =
           ring_1 bool_poly
           ==> (p == p') (mod_ghash) ==> ring_coprime bool_poly (ghash_poly,p)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SIMP_TAC[cong; mod_ghash; IN_IDEAL_GENERATED_SING_EQ; GHASH_BOOL_POLY] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_divides]) THEN
    ASM_SIMP_TAC[RING_SUB; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `d:(1->num)->bool` THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[BEZOUT_RING_COPRIME; BEZOUT_BOOL_POLY] THEN
    EXISTS_TAC `ring_sub bool_poly s (ring_mul bool_poly t d)` THEN
    EXISTS_TAC `t:(1->num)->bool` THEN
    ASM_SIMP_TAC[RING_SUB; RING_MUL] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    SPEC_TAC(`bool_poly`,`r:((1->num)->bool)ring`) THEN
    RING_TAC) in
  REWRITE_TAC[bool_poly] THEN MATCH_MP_TAC RABIN_IRREDUCIBILITY_SUFFICIENT THEN
  EXISTS_TAC `128` THEN REWRITE_TAC[POLY_DEG_GHASH_POLY] THEN
  REWRITE_TAC[FIELD_BOOL_RING; FINITE_BOOL_RING; CARD_BOOL_RING] THEN
  REWRITE_TAC[GSYM bool_poly; GHASH_BOOL_POLY] THEN CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM
     `poly_deg bool_ring:((1->num)->bool)->num`) THEN
    REWRITE_TAC[POLY_DEG_GHASH_POLY] THEN
    REWRITE_TAC[bool_poly; POLY_RING; POLY_DEG_0; ARITH_EQ];
    REWRITE_TAC[ARITH_EQ] THEN
    REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 7`)]] THEN
  SIMP_TAC[IMP_CONJ; PRIME_DIVEXP_EQ] THEN
  SIMP_TAC[DIVIDES_PRIME_PRIME; PRIME_2; ARITH_EQ] THEN
  ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; PRIME_2] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  REWRITE_TAC[GSYM MOD_GHASH_0; X_POWPOW_128] THEN
  MP_TAC X_POWPOW_64 THEN MATCH_MP_TAC lemma THEN
  MAP_EVERY EXISTS_TAC
   [`poly_of_word(word 0x34f319a5fb685836214ec51f73e3547b:129 word)`;
    `poly_of_word(word 0x9e4af928ddbc838a41a8cafd2c95b018:129 word)`] THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD] THEN
  MP_TAC(INST_TYPE [`:129`,`:N`] GHASH_POLY_OF_WORD) THEN
  MP_TAC(INST_TYPE [`:128`,`:M`; `:129`,`:N`] POLY_OF_WORD_ZX) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC(ONCE_DEPTH_CONV WORD_ZX_CONV) THEN
  REWRITE_TAC[GSYM POLY_OF_WORD_PMUL_2N; GSYM POLY_OF_WORD_XOR] THEN
  CONV_TAC(DEPTH_CONV(WORD_PMUL_CONV ORELSEC WORD_RED_CONV)) THEN
  REWRITE_TAC[POLY_OF_WORD_1]);;
