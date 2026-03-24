(* ========================================================================= *)
(* POLYVAL: The POLYVAL polynomial Q(x) from RFC 8452 (AES-GCM-SIV).        *)
(* Q(x) = x^128 + x^127 + x^126 + x^121 + 1.                              *)
(* Also used for GHASH via Gueron's reinterpretation (CSCML 2023).          *)
(* See: RFC 8452, Section 3 and Appendix A.                                 *)
(* See: Gueron, "A New Interpretation for the GHASH Authenticator of         *)
(* AES-GCM", CSCML 2023, LNCS 13914, pp. 424-438.                          *)
(* ========================================================================= *)

needs "common/ghash.ml";;

(* ------------------------------------------------------------------------- *)
(* The Q(x) polynomial: x^128 + x^127 + x^126 + x^121 + 1                  *)
(* This has the special form x^128 + W(x)*x^64 + 1 where                    *)
(* W(x) = x^63 + x^62 + x^57 = 0xC200000000000000.                         *)
(* ------------------------------------------------------------------------- *)

let polyval_poly = define
 `polyval_poly =
  ring_sum bool_poly {128,127,126,121,0}
    (\i. ring_pow bool_poly (poly_var bool_ring one) i)`;;

let POLYVAL_BOOL_POLY = prove
 (`polyval_poly IN ring_carrier bool_poly`,
  REWRITE_TAC[polyval_poly; RING_SUM]);;

let RING_POLYNOMIAL_POLYVAL_POLY = prove
 (`ring_polynomial bool_ring polyval_poly`,
  REWRITE_TAC[RING_POLYNOMIAL; GSYM bool_poly; POLYVAL_BOOL_POLY]);;

let POLYVAL_POLY_OF_WORD = prove
 (`128 < dimindex(:N)
   ==> polyval_poly =
       poly_of_word(word 0x1C2000000000000000000000000000001:N word)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[polyval_poly] THEN
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

let POLY_DEG_POLYVAL_POLY = prove
 (`poly_deg bool_ring polyval_poly = 128`,
  MP_TAC(INST_TYPE [`:129`,`:N`] POLYVAL_POLY_OF_WORD) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[POLY_DEG_POLY_OF_WORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Equivalence modulo Q(x) and basic congruence properties.                  *)
(* ------------------------------------------------------------------------- *)

let mod_polyval = define
 `mod_polyval p q <=>
  p IN ring_carrier bool_poly /\ q IN ring_carrier bool_poly /\
  ring_sub bool_poly p q IN ideal_generated bool_poly {polyval_poly}`;;

let MOD_POLYVAL_REFL = prove
 (`!p. (p == p) (mod_polyval) <=> p IN ring_carrier bool_poly`,
  GEN_TAC THEN REWRITE_TAC[cong; mod_polyval] THEN
  ASM_CASES_TAC `p IN ring_carrier bool_poly` THEN
  ASM_SIMP_TAC[RING_SUB_REFL; IN_RING_IDEAL_0; RING_IDEAL_IDEAL_GENERATED]);;

let MOD_POLYVAL_REFL_GEN = prove
 (`!p q. p IN ring_carrier bool_poly /\ q = p ==> (p == q) (mod_polyval)`,
  MESON_TAC[MOD_POLYVAL_REFL]);;

let MOD_POLYVAL_SYM = prove
 (`!p q. (p == q) (mod_polyval) <=> (q == p) (mod_polyval)`,
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`p IN ring_carrier bool_poly`; `q IN ring_carrier bool_poly`] THEN
  ASM_REWRITE_TAC[cong; mod_polyval] THEN
  ASM_MESON_TAC[IN_RING_IDEAL_NEG; RING_IDEAL_IDEAL_GENERATED;
                RING_RULE `ring_neg r (ring_sub r a b) = ring_sub r b a`]);;

let MOD_POLYVAL_TRANS = prove
 (`!p q r.
      (p == q) (mod_polyval) /\ (q == r) (mod_polyval) ==> (p == r) (mod_polyval)`,
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`p IN ring_carrier bool_poly`; `q IN ring_carrier bool_poly`;
    `r IN ring_carrier bool_poly`] THEN
  ASM_REWRITE_TAC[cong; mod_polyval] THEN
  ASM_MESON_TAC[IN_RING_IDEAL_ADD; RING_IDEAL_IDEAL_GENERATED; RING_RULE
   `ring_add r (ring_sub r a b) (ring_sub r b c) = ring_sub r a c`]);;

let MOD_POLYVAL_ADD = prove
 (`!p p' q q'.
      (p == p') (mod_polyval) /\ (q == q') (mod_polyval)
      ==> (ring_add bool_poly p q == ring_add bool_poly p' q') (mod_polyval)`,
 REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`p IN ring_carrier bool_poly`; `p' IN ring_carrier bool_poly`;
    `q IN ring_carrier bool_poly`; `q' IN ring_carrier bool_poly`] THEN
  ASM_SIMP_TAC[cong; mod_polyval; RING_ADD] THEN
  ASM_MESON_TAC[IN_RING_IDEAL_ADD; RING_IDEAL_IDEAL_GENERATED; RING_RULE
   `ring_add r (ring_sub r p p') (ring_sub r q q') =
    ring_sub r (ring_add r p q) (ring_add r p' q')`]);;

let MOD_POLYVAL_MUL = prove
 (`!p p' q q'.
      (p == p') (mod_polyval) /\ (q == q') (mod_polyval)
      ==> (ring_mul bool_poly p q == ring_mul bool_poly p' q') (mod_polyval)`,
 REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`p IN ring_carrier bool_poly`; `p' IN ring_carrier bool_poly`;
    `q IN ring_carrier bool_poly`; `q' IN ring_carrier bool_poly`] THEN
  ASM_SIMP_TAC[cong; mod_polyval; RING_MUL] THEN
  ASM_MESON_TAC[IN_RING_IDEAL_ADD; IN_RING_IDEAL_LMUL;
                RING_IDEAL_IDEAL_GENERATED; RING_RULE
   `ring_add r (ring_mul r q (ring_sub r p p'))
               (ring_mul r p' (ring_sub r q q')) =
    ring_sub r (ring_mul r p q) (ring_mul r p' q')`]);;

(* ------------------------------------------------------------------------- *)
(* One-step reduction modulo Q(x): subtract a multiple of Q(x) to clear     *)
(* bits >= 128. Uses Q(x) mod x^128 = x^127 + x^126 + x^121 + 1           *)
(* = 0xC2000000000000000000000000000001.                                     *)
(* ------------------------------------------------------------------------- *)

let polyval_reduce_step = new_definition
 `polyval_reduce_step (x:N word) =
  word_xor (word_subword x (0,128):N word)
           (word_pmul (word_ushr x 128)
                      (word 0xC2000000000000000000000000000001:N word))`;;

let POLY_EQUIV_POLYVAL_REDUCE_STEP = prove
 (`!x:N word.
        (poly_of_word(polyval_reduce_step x) == poly_of_word x) (mod_polyval)`,
  let lemma = prove
   (`!x:N word.
          word_subword x (0,128) =
          word_xor x (word_shl (word_ushr x 128) 128)`,
    GEN_TAC THEN ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
    SIMP_TAC[BIT_WORD_SUBWORD; BIT_WORD_XOR; BIT_WORD_SHL; BIT_WORD_USHR] THEN
    SIMP_TAC[ADD_CLAUSES; ARITH_RULE `i < MIN a b <=> i < a /\ i < b`] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `128 <= i` THEN ASM_SIMP_TAC[GSYM NOT_LE; SUB_ADD]) in
  GEN_TAC THEN REWRITE_TAC[cong; mod_polyval; BOOL_POLY_OF_WORD] THEN
  SIMP_TAC[IDEAL_GENERATED_SING; POLYVAL_BOOL_POLY; IN_ELIM_THM] THEN
  REWRITE_TAC[ring_divides; POLYVAL_BOOL_POLY] THEN
  SIMP_TAC[RING_SUB; BOOL_POLY_OF_WORD] THEN
  EXISTS_TAC `poly_of_word(word_ushr x 128:N word)` THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD] THEN
  REWRITE_TAC[polyval_reduce_step; lemma] THEN
  REWRITE_TAC[BOOL_POLY_SUB; GSYM POLY_OF_WORD_XOR] THEN
  REWRITE_TAC[WORD_BITWISE_RULE
   `word_xor (word_xor (word_xor x a) b) x = word_xor a b`] THEN
  ASM_CASES_TAC `word_ushr x 128:N word = word 0` THENL
   [ASM_REWRITE_TAC[POLY_OF_WORD_0; WORD_PMUL_0; WORD_SHL_0; WORD_XOR_0] THEN
    SIMP_TAC[RING_MUL_RZERO; POLYVAL_BOOL_POLY];
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
  MP_TAC(ISPECL [`word(2 EXP 128):N word`;
                  `word 0xC2000000000000000000000000000001:N word`]
    WORD_ADD_XOR) THEN
  REWRITE_TAC[WORD_AND_POW2; BIT_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_PMUL_POLY] THEN
  ASM_SIMP_TAC[GSYM POLYVAL_POLY_OF_WORD] THEN
  MATCH_MP_TAC POLY_OF_WORD_OF_POLY THEN
  SIMP_TAC[RING_MUL; POLYVAL_BOOL_POLY; BOOL_POLY_OF_WORD] THEN
  REWRITE_TAC[bool_poly; POLY_RING] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_MUL_LE o lhand o snd) THEN
  REWRITE_TAC[RING_POLYNOMIAL_POLYVAL_POLY; POLY_DEG_POLYVAL_POLY;
              POLY_DEG_POLY_OF_WORD; RING_POLYNOMIAL_OF_WORD] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS) THEN
  MATCH_MP_TAC(ARITH_RULE `128 < n /\ 128 <= c ==> 128 + n - 1 - c < n`) THEN
  ASM_SIMP_TAC[WORD_LE_CLZ; LT_IMP_LE; BIT_WORD_USHR] THEN
  MESON_TAC[BIT_GUARD]);;

(* ------------------------------------------------------------------------- *)
(* Gueron's Proposition 3: two-phase reduction using W(x) = 0xC2...0.       *)
(* Given a 256-bit product T(x), computes T(x) * x^{-128} mod Q(x)         *)
(* using only two 64x64 polynomial multiplications by W(x).                 *)
(*                                                                           *)
(* Q(x) = x^128 + W(x)*x^64 + 1 where W(x) = x^63 + x^62 + x^57.         *)
(*                                                                           *)
(* Input T = D*x^192 + C*x^128 + B*x^64 + A (each limb 64 bits).           *)
(* Phase 1: fold A using W*A, producing 192-bit T1.                          *)
(* Phase 2: fold V (low 64 of T1) using W*V, producing 128-bit T2.          *)
(* Result: T2 = T * x^{-128} mod Q(x).                                      *)
(* ------------------------------------------------------------------------- *)

let polyval_reduce_prop3 = define
 `(polyval_reduce_prop3 : 256 word -> 128 word) t =
  let a:64 word = word_subword t (0,64) in
  let b:64 word = word_subword t (64,64) in
  let c:64 word = word_subword t (128,64) in
  let d:64 word = word_subword t (192,64) in
  let w:64 word = word 0xC200000000000000 in
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
  word_join g f : 128 word`;;

(* ------------------------------------------------------------------------- *)
(* Main theorem: Proposition 3 computes T * x^{-128} mod Q(x).              *)
(* Equivalently: result * x^128 ≡ T (mod Q(x)).                             *)
(*                                                                           *)
(* Proof idea (from Gueron):                                                 *)
(*   T2 * x^128 = T + A*Q(x) + V*Q(x)*x^64                                 *)
(* where A = low 64 bits of T, V = B XOR low64(W*A).                        *)
(* Since A*Q + V*Q*x^64 is a multiple of Q(x), we have                      *)
(*   T2 * x^128 ≡ T (mod Q(x)).                                             *)
(* ------------------------------------------------------------------------- *)

(* TODO: Formal proof of POLYVAL_REDUCE_PROP3_CORRECT:
   `!t. (ring_mul bool_poly
           (poly_of_word (polyval_reduce_prop3 t))
           (ring_pow bool_poly (poly_var bool_ring one) 128)
         == poly_of_word t) (mod_polyval)`

   i.e., polyval_reduce_prop3(T) * x^128 ≡ T (mod Q(x)),
   meaning polyval_reduce_prop3 computes T * x^{-128} mod Q(x).

   Proof sketch (verified computationally on multiple test cases):
   The quotient witnessing divisibility by Q(x) is
     poly_of_word(A) + poly_of_word(V) * x^64
   where A = low 64 bits of T, V = B XOR low64(W*A), B = bits 64..127 of T.
   Then: result * x^128 + T = (A + V*x^64) * Q(x)
   which can be verified by expanding both sides limb-by-limb.

   Detailed algebraic verification (all in char 2, so + = XOR):
   Let T = D*x^192 + C*x^128 + B*x^64 + A (each limb 64 bits).
   Let wa = A*W = wa_hi*x^64 + wa_lo, wv = V*W = wv_hi*x^64 + wv_lo.
   Then V = B+wa_lo, U = C+A+wa_hi, f = U+wv_lo, g = D+V+wv_hi.

   LHS = (g*x^64+f)*x^128 + T
       = (V+wv_hi)*x^192 + (A+wa_hi+wv_lo)*x^128 + B*x^64 + A

   RHS = (A+V*x^64) * (x^128+W*x^64+1)
       = (V+wv_hi)*x^192 + (A+wa_hi+wv_lo)*x^128 + (wa_lo+V)*x^64 + A
       = (V+wv_hi)*x^192 + (A+wa_hi+wv_lo)*x^128 + B*x^64 + A
   (using wa_lo+V = wa_lo+B+wa_lo = B in char 2)

   LHS = RHS. QED.

   Formalization blocker: HOL Light's RING_TAC does not support
   characteristic 2 rings. The identity holds only in char 2 (where
   a+a=0), not in a general commutative ring. A manual proof would
   require ~50 ring manipulation steps. *)
