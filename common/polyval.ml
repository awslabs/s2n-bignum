(* ========================================================================= *)
(* POLYVAL: The POLYVAL polynomial Q(x) from RFC 8452 (AES-GCM-SIV).         *)
(* Q(x) = x^128 + x^127 + x^126 + x^121 + 1.                                 *)
(* Also used for GHASH via Gueron's reinterpretation (CSCML 2023).           *)
(*                                                                           *)
(* Contents (top-level sections):                                            *)
(*   1. Q(x) definition, mod_polyval congruence, one-step reduction.         *)
(*   2. Gueron's Proposition 3: two-phase reduction using W(x), and its      *)
(*      word-level correctness (POLYVAL_REDUCE_PROP3_CORRECT).               *)
(*   3. Generic poly_of_word / pmul plumbing used by the Q(x) structural     *)
(*      proofs below (and re-used by karatsuba_pmul_proof.ml).               *)
(*   4. Q(x) structural facts: integral-domain structure, congruence         *)
(*      linchpin (MOD_POLYVAL_WORD_EQ), irreducibility via Rabin test        *)
(*      (RING_IRREDUCIBLE_POLYVAL_POLYNOMIAL), and x^n cancellation          *)
(*      (MOD_POLYVAL_CANCEL_VARPOW{,_GEN}).                                  *)
(*                                                                           *)
(* See: RFC 8452, Section 3 and Appendix A.                                  *)
(* See: Gueron, "A New Interpretation for the GHASH Authenticator of         *)
(* AES-GCM", CSCML 2023, LNCS 13914, pp. 424-438.                            *)
(* ========================================================================= *)

needs "common/ghash.ml";;

(* ------------------------------------------------------------------------- *)
(* The Q(x) polynomial: x^128 + x^127 + x^126 + x^121 + 1                    *)
(* This has the special form x^128 + W(x)*x^64 + 1 where                     *)
(* W(x) = x^63 + x^62 + x^57 = 0xC200000000000000.                           *)
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
(* One-step reduction modulo Q(x): subtract a multiple of Q(x) to clear      *)
(* bits >= 128. Uses Q(x) mod x^128 = x^127 + x^126 + x^121 + 1              *)
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
(* Gueron's Proposition 3: two-phase reduction using W(x) = 0xC2...0.        *)
(* Given a 256-bit product T(x), computes T(x) * x^{-128} mod Q(x)           *)
(* using only two 64x64 polynomial multiplications by W(x).                  *)
(*                                                                           *)
(* Q(x) = x^128 + W(x)*x^64 + 1 where W(x) = x^63 + x^62 + x^57.             *)
(*                                                                           *)
(* Input T = D*x^192 + C*x^128 + B*x^64 + A (each limb 64 bits).             *)
(* Phase 1: fold A using W*A, producing 192-bit T1.                          *)
(* Phase 2: fold V (low 64 of T1) using W*V, producing 128-bit T2.           *)
(* Result: T2 = T * x^{-128} mod Q(x).                                       *)
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
(* Main theorem: Proposition 3 computes T * x^{-128} mod Q(x).               *)
(* Equivalently: result * x^128 == T (mod Q(x)).                             *)
(*                                                                           *)
(* Proof idea (from Gueron):                                                 *)
(*   T2 * x^128 = T + A*Q(x) + V*Q(x)*x^64                                   *)
(* where A = low 64 bits of T, V = B XOR low64(W*A).                         *)
(* Since A*Q + V*Q*x^64 is a multiple of Q(x), we have                       *)
(*   T2 * x^128 == T (mod Q(x)).                                             *)
(*                                                                           *)
(* Strategy:                                                                 *)
(* 1. Define the quotient witness: A + V*x^64                                *)
(* 2. Show (prop3(T)*x^128 + T) = quotient(T) * Q(x) in bool_poly            *)
(* 3. The identity is verified lane-by-lane (4 x 64-bit lanes)               *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* The quotient witness for ideal membership.                                *)
(* For T = D*x^192 + C*x^128 + B*x^64 + A, the quotient is A + V*x^64        *)
(* where V = B XOR low64(W*A).                                               *)
(* ------------------------------------------------------------------------- *)

let polyval_quotient = new_definition
 `polyval_quotient (t:256 word) =
  let a:64 word = word_subword t (0,64) in
  let b:64 word = word_subword t (64,64) in
  let w:64 word = word 0xC200000000000000 in
  let wa:128 word = word_pmul a w in
  let wa_lo:64 word = word_subword wa (0,64) in
  let v:64 word = word_xor b wa_lo in
  word_xor (word_zx a : 256 word) (word_shl (word_zx v : 256 word) 64)`;;

(* ------------------------------------------------------------------------- *)
(* Helper: x^k = poly_of_word(word(2^k)) when k < dimindex.                  *)
(* ------------------------------------------------------------------------- *)

let POLY_VAR_POW_OF_WORD = prove
 (`!k. k < dimindex(:N)
       ==> ring_pow bool_poly (poly_var bool_ring one) k =
           poly_of_word(word(2 EXP k):N word)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[POLY_RING_VAR_POW_1; bool_poly; POLY_RING; poly_of_word] THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  REWRITE_TAC[FORALL_FUN_FROM_1] THEN
  X_GEN_TAC `i:num` THEN
  REWRITE_TAC[MESON[] `(\x:1. a) = (\x. b) <=> a = b`] THEN
  REWRITE_TAC[BOOL_RING; MESON[] `(if p then T else F) <=> p`] THEN
  REWRITE_TAC[BIT_WORD_POW2] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let POLY_VAR_POW_OF_WORD_256 = INST_TYPE [`:256`,`:N`] POLY_VAR_POW_OF_WORD;;

(* ------------------------------------------------------------------------- *)
(* Helper: char 2 self-inverse property.                                     *)
(* ------------------------------------------------------------------------- *)

let BOOL_POLY_ADD_SELF = prove
 (`!x. x IN ring_carrier bool_poly
       ==> ring_add bool_poly x x = ring_0 bool_poly`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`bool_poly`; `x:((1->num)->bool)`] RING_ADD_RNEG) THEN
  ASM_REWRITE_TAC[BOOL_POLY_NEG; I_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Expand word_pmul by W = 0xC200000000000000 into shifts + XORs.            *)
(* W = 2^63 + 2^62 + 2^57, so pmul by W = shl 63 XOR shl 62 XOR shl 57.      *)
(* ------------------------------------------------------------------------- *)

let W_EXPAND = prove
 (`word 0xC200000000000000 : 64 word =
   word_xor (word_xor (word(2 EXP 63)) (word(2 EXP 62))) (word(2 EXP 57))`,
  CONV_TAC(DEPTH_CONV(NUM_EXP_CONV ORELSEC WORD_RED_CONV)));;

let W128_EXPAND = prove
 (`word 0xC200000000000000 : 128 word =
   word_xor (word_xor (word(2 EXP 63)) (word(2 EXP 62))) (word(2 EXP 57))`,
  CONV_TAC(DEPTH_CONV(NUM_EXP_CONV ORELSEC WORD_RED_CONV)));;

let PMUL_W_64_128 = prove
 (`!(x:64 word). (word_pmul x (word 0xC200000000000000 : 64 word) : 128 word) =
   word_xor (word_xor (word_shl (word_zx x : 128 word) 63)
                       (word_shl (word_zx x : 128 word) 62))
            (word_shl (word_zx x : 128 word) 57)`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM(CONJUNCT1 WORD_PMUL_ZX)] THEN
  ONCE_REWRITE_TAC[GSYM(CONJUNCT2 WORD_PMUL_ZX)] THEN
  CONV_TAC(LAND_CONV(RAND_CONV WORD_ZX_CONV)) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [W128_EXPAND] THEN
  REWRITE_TAC[WORD_PMUL_XOR; WORD_PMUL_POW2]);;

(* ------------------------------------------------------------------------- *)
(* Expand word_pmul by Q(x) = 0x1C2...01 into shifts + XORs.                 *)
(* Q = 2^128 + 2^127 + 2^126 + 2^121 + 1.                                    *)
(* ------------------------------------------------------------------------- *)

let Q256_EXPAND = prove
 (`word 0x1C2000000000000000000000000000001 : 256 word =
   word_xor (word_xor (word_xor (word_xor (word(2 EXP 128)) (word(2 EXP 127)))
                                 (word(2 EXP 126)))
                       (word(2 EXP 121)))
            (word 1)`,
  CONV_TAC(DEPTH_CONV(NUM_EXP_CONV ORELSEC WORD_RED_CONV)));;

let PMUL_Q_256 = prove
 (`!(x:256 word).
     (word_pmul x (word 0x1C2000000000000000000000000000001 : 256 word) : 256 word) =
     word_xor (word_xor (word_xor (word_xor (word_shl x 128) (word_shl x 127))
                                   (word_shl x 126))
                         (word_shl x 121))
              x`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [Q256_EXPAND] THEN
  REWRITE_TAC[WORD_PMUL_XOR; WORD_PMUL_POW2] THEN
  REWRITE_TAC[ARITH_RULE `1 = 2 EXP 0`; WORD_PMUL_POW2; WORD_SHL_ZERO]);;

let PMUL_Q_256_SYM = prove
 (`!(x:256 word).
     (word_pmul (word 0x1C2000000000000000000000000000001 : 256 word) x : 256 word) =
     word_xor (word_xor (word_xor (word_xor (word_shl x 128) (word_shl x 127))
                                   (word_shl x 126))
                         (word_shl x 121))
              x`,
  GEN_TAC THEN ONCE_REWRITE_TAC[WORD_PMUL_SYM] THEN REWRITE_TAC[PMUL_Q_256]);;

(* ------------------------------------------------------------------------- *)
(* Decompose 256-bit word equality into 4 x 64-bit lane equalities.          *)
(* ------------------------------------------------------------------------- *)

let WORD_EQ_LANES_256 = prove
 (`!x y : 256 word.
    x = y <=>
    (word_subword x (0,64) : 64 word) = word_subword y (0,64) /\
    (word_subword x (64,64) : 64 word) = word_subword y (64,64) /\
    (word_subword x (128,64) : 64 word) = word_subword y (128,64) /\
    (word_subword x (192,64) : 64 word) = word_subword y (192,64)`,
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* The 256-bit word identity: result*x^128 + T = quotient * Q(x).            *)
(* Proved lane-by-lane using BITBLAST_TAC (BDD-based bit-blasting).          *)
(* ------------------------------------------------------------------------- *)

let WORD_IDENTITY_PROP3 = prove
 (`!t:256 word.
   word_xor (word_shl (word_zx(polyval_reduce_prop3 t) : 256 word) 128) t =
   word_pmul (word 0x1C2000000000000000000000000000001 : 256 word)
             (polyval_quotient t : 256 word)`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_LANES_256] THEN
  REWRITE_TAC[polyval_reduce_prop3; polyval_quotient; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[PMUL_Q_256_SYM; PMUL_W_64_128] THEN
  REPEAT CONJ_TAC THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Quotient has degree < 128 (high 128 bits are zero).                       *)
(* ------------------------------------------------------------------------- *)

let QUOTIENT_HIGH_ZERO = prove
 (`!t:256 word. word_ushr (polyval_quotient t : 256 word) 128 = word 0`,
  GEN_TAC THEN
  REWRITE_TAC[polyval_quotient; LET_DEF; LET_END_DEF; PMUL_W_64_128] THEN
  BITBLAST_TAC);;

let QUOTIENT_CLZ = prove
 (`!t:256 word. 128 <= word_clz(polyval_quotient t : 256 word)`,
  GEN_TAC THEN REWRITE_TAC[WORD_LE_CLZ_VAL_DIV] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `340282366920938463463374607431768211456 = 2 EXP 128`
    SUBST1_TAC THENL
  [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_WORD_USHR; QUOTIENT_HIGH_ZERO; VAL_WORD_0]);;

(* ------------------------------------------------------------------------- *)
(* Polynomial-level conversion lemmas.                                       *)
(* LHS: result*x^128 + T = poly_of_word(word_xor(shl(zx result)128) t)       *)
(* RHS: Q*quotient = poly_of_word(word_pmul Q quotient)                      *)
(* ------------------------------------------------------------------------- *)

let LHS_POLY_LEMMA = prove
 (`!r:128 word t:256 word.
    ring_add bool_poly
      (ring_mul bool_poly (poly_of_word r)
         (ring_pow bool_poly (poly_var bool_ring one) 128))
      (poly_of_word t) =
    poly_of_word(word_xor (word_shl (word_zx r : 256 word) 128) t)`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[POLY_OF_WORD_XOR] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `poly_of_word(word_zx r : 256 word) = poly_of_word (r:128 word)`
    (fun th -> REWRITE_TAC[GSYM th]) THENL
  [MATCH_MP_TAC POLY_OF_WORD_ZX THEN
   CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 WORD_PMUL_POW2); WORD_PMUL_POLY] THEN
  MP_TAC(SPEC `128` POLY_VAR_POW_OF_WORD_256) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(INST_TYPE [`:256`,`:N`] POLY_OF_WORD_OF_POLY) THEN
  SIMP_TAC[RING_MUL; BOOL_POLY_OF_WORD; RING_POW; POLY_VAR_BOOL_POLY] THEN
  REWRITE_TAC[bool_poly; POLY_RING] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_MUL_LE o lhand o snd) THEN
  REWRITE_TAC[RING_POLYNOMIAL_OF_WORD; RING_POLYNOMIAL;
              GSYM bool_poly; POLY_VARPOW_BOOL_POLY] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS) THEN
  SUBGOAL_THEN `poly_deg bool_ring
    (ring_pow bool_poly (poly_var bool_ring one) 128) = 128`
    (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[bool_poly; POLY_DEG_VAR_POW; BOOL_RING] THEN
   CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `poly_of_word(word_zx (r:128 word) : 256 word) = poly_of_word r`
    SUBST1_TAC THENL
  [MATCH_MP_TAC POLY_OF_WORD_ZX THEN
   CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `r:128 word` POLY_DEG_POLY_OF_WORD_BOUND) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC);;

let RHS_POLY_LEMMA = prove
 (`!t:256 word.
    ring_mul bool_poly polyval_poly (poly_of_word (polyval_quotient t)) =
    poly_of_word(word_pmul (word 0x1C2000000000000000000000000000001 : 256 word)
                           (polyval_quotient t) : 256 word)`,
  GEN_TAC THEN
  SUBGOAL_THEN `128 < dimindex(:256)` ASSUME_TAC THENL
  [CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[POLYVAL_POLY_OF_WORD] THEN
  REWRITE_TAC[WORD_PMUL_POLY] THEN
  ASM_SIMP_TAC[GSYM POLYVAL_POLY_OF_WORD] THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC(INST_TYPE [`:256`,`:N`] POLY_OF_WORD_OF_POLY) THEN
  SIMP_TAC[RING_MUL; POLYVAL_BOOL_POLY; BOOL_POLY_OF_WORD] THEN
  REWRITE_TAC[bool_poly; POLY_RING] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_MUL_LE o lhand o snd) THEN
  REWRITE_TAC[RING_POLYNOMIAL_POLYVAL_POLY; RING_POLYNOMIAL_OF_WORD;
              POLY_DEG_POLYVAL_POLY; POLY_DEG_POLY_OF_WORD] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS) THEN
  MP_TAC(SPEC `t:256 word` QUOTIENT_CLZ) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Main theorem: Proposition 3 computes T * x^{-128} mod Q(x).               *)
(* Equivalently: result * x^128 == T (mod Q(x)).                             *)
(* ------------------------------------------------------------------------- *)

let POLYVAL_REDUCE_PROP3_CORRECT = prove
 (`!t:256 word.
   (ring_mul bool_poly
     (poly_of_word (polyval_reduce_prop3 t))
     (ring_pow bool_poly (poly_var bool_ring one) 128)
    == poly_of_word t) (mod_polyval)`,
  GEN_TAC THEN REWRITE_TAC[cong; mod_polyval; BOOL_POLY_OF_WORD] THEN
  SIMP_TAC[IDEAL_GENERATED_SING; POLYVAL_BOOL_POLY; IN_ELIM_THM] THEN
  REWRITE_TAC[ring_divides; POLYVAL_BOOL_POLY] THEN
  SIMP_TAC[RING_SUB; RING_MUL; BOOL_POLY_OF_WORD;
           RING_POW; POLY_VAR_BOOL_POLY] THEN
  EXISTS_TAC `poly_of_word(polyval_quotient t : 256 word)` THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD; BOOL_POLY_SUB] THEN
  REWRITE_TAC[LHS_POLY_LEMMA; RHS_POLY_LEMMA; WORD_IDENTITY_PROP3]);;

(* ========================================================================= *)
(* Generic poly_of_word / pmul plumbing used by the Q(x) structural proofs   *)
(* below (and by common/karatsuba_pmul_proof.ml, which loads after this      *)
(* file). None of this material depends on Q(x).                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* poly_of_word is injective.                                                *)
(* ------------------------------------------------------------------------- *)

let POLY_OF_WORD_INJ = prove
 (`!(x:N word) (y:N word). poly_of_word x = poly_of_word y ==> x = y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM WORD_OF_POLY_OF_WORD] THEN
  AP_TERM_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* poly_of_word of a pmul (with a degree precondition) is the polynomial     *)
(* product. Generic over input/output word sizes.                            *)
(* ------------------------------------------------------------------------- *)

let POLY_OF_WORD_PMUL_GEN = prove
 (`!(x:M word) (y:N word).
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

(* ------------------------------------------------------------------------- *)
(* Zero-extending a 128-bit word to 256 bits is transparent to poly_of_word. *)
(* ------------------------------------------------------------------------- *)

let zx_128_256 = prove
 (`!w:128 word. poly_of_word(word_zx w : 256 word) = poly_of_word w`,
  GEN_TAC THEN MATCH_MP_TAC POLY_OF_WORD_ZX THEN
  REWRITE_TAC[DIMINDEX_128; DIMINDEX_256] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Degree-bound discharge tactic for pmul, parametrized over output and      *)
(* input dimensions. Used to satisfy POLY_OF_WORD_PMUL_GEN's precondition.   *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* 128 x 128 -> 256 pmul case of POLY_OF_WORD_PMUL_GEN.                      *)
(* ------------------------------------------------------------------------- *)

let pmul_128_256 = prove
 (`!x:128 word y:128 word.
     poly_of_word(word_pmul x y : 256 word) =
     ring_mul bool_poly (poly_of_word x) (poly_of_word y)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC POLY_OF_WORD_PMUL_GEN THEN PMUL_DEG_TAC);;

(* ========================================================================= *)
(* Q(x) structural facts: integral-domain structure, congruence linchpin,    *)
(* irreducibility (Rabin test), and x^n cancellation.                        *)
(*                                                                           *)
(* This material extends the primitive POLYVAL algebra above (Q(x),          *)
(* mod_polyval, polyval_reduce_prop3, POLYVAL_REDUCE_PROP3_CORRECT) with     *)
(* the structural theorems needed by downstream GHASH proofs:                *)
(*                                                                           *)
(*   INTEGRAL_DOMAIN_BOOL_POLY    GF(2)[x] is an integral domain             *)
(*   POLYVAL_POLY_NONZERO         Q(x) != 0                                  *)
(*   POLYVAL_DIVIDES_LOW_DEG      Q | p /\ deg p < 128  ==>  p = 0           *)
(*   MOD_POLYVAL_WORD_EQ          Congruent 128-bit words are equal          *)
(*   RING_IRREDUCIBLE_POLYVAL_POLYNOMIAL   Q(x) is irreducible               *)
(*   MOD_POLYVAL_CANCEL_VARPOW{,_GEN}      Cancel x^n from congruences       *)
(*                                                                           *)
(* The irreducibility proof follows John Harrison's Rabin-test approach for  *)
(* P(x) in common/ghash.ml. It differs in that Q(x)'s reduction constant     *)
(* has degree 127 (vs P(x)'s degree 7), so naive iterated reduction is       *)
(* infeasible; instead a 128-step squaring chain with precomputed OCaml      *)
(* quotient witnesses is verified step-by-step inside HOL Light.             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Helper: ring_mul/ring_0 in bool_poly = poly_mul/poly_0 in bool_ring.      *)
(* ------------------------------------------------------------------------- *)

let BOOL_POLY_MUL = prove
 (`ring_mul bool_poly = poly_mul bool_ring`,
  REWRITE_TAC[bool_poly; POLY_RING]);;

let BOOL_POLY_ZERO = prove
 (`ring_0 bool_poly = poly_0 bool_ring`,
  REWRITE_TAC[bool_poly; POLY_RING]);;

let INTEGRAL_DOMAIN_BOOL_POLY = prove
 (`integral_domain bool_poly`,
  REWRITE_TAC[bool_poly; INTEGRAL_DOMAIN_POLY_RING; INTEGRAL_DOMAIN_BOOL_RING]);;

(* ------------------------------------------------------------------------- *)
(* Q(x) is nonzero (degree 128 <> degree 0).                                 *)
(* ------------------------------------------------------------------------- *)

let POLYVAL_POLY_NONZERO = prove
 (`~(polyval_poly = ring_0 bool_poly)`,
  REWRITE_TAC[BOOL_POLY_ZERO] THEN
  DISCH_THEN(MP_TAC o AP_TERM `poly_deg bool_ring:((1->num)->bool)->num`) THEN
  REWRITE_TAC[POLY_DEG_POLYVAL_POLY; bool_poly; POLY_RING; POLY_DEG_0] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* If Q(x) divides p and deg(p) < 128, then p = 0.                           *)
(* (Degree argument in the integral domain GF(2)[x].)                        *)
(* ------------------------------------------------------------------------- *)

let POLYVAL_DIVIDES_LOW_DEG = prove
 (`!p. p IN ring_carrier bool_poly /\
       ring_divides bool_poly polyval_poly p /\
       poly_deg bool_ring p < 128
       ==> p = ring_0 bool_poly`,
  GEN_TAC THEN ASM_CASES_TAC `p = ring_0 bool_poly` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_divides]) THEN
  ASM_REWRITE_TAC[POLYVAL_BOOL_POLY] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(1->num)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(q = ring_0 bool_poly)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(p = ring_0 bool_poly)` THEN
    ASM_SIMP_TAC[RING_MUL_RZERO; POLYVAL_BOOL_POLY]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN
  UNDISCH_TAC `poly_deg bool_ring (ring_mul bool_poly polyval_poly q) < 128` THEN
  REWRITE_TAC[NOT_LT; BOOL_POLY_MUL] THEN
  SUBGOAL_THEN
    `poly_deg bool_ring (poly_mul bool_ring polyval_poly q) =
     128 + poly_deg bool_ring q`
    (fun th -> REWRITE_TAC[th] THEN ARITH_TAC) THEN
  REWRITE_TAC[GSYM POLY_DEG_POLYVAL_POLY] THEN
  MATCH_MP_TAC POLY_DEG_MUL THEN
  REWRITE_TAC[INTEGRAL_DOMAIN_BOOL_RING; RING_POLYNOMIAL_POLYVAL_POLY] THEN
  ASM_REWRITE_TAC[RING_POLYNOMIAL; GSYM bool_poly; BOOL_POLY_ZERO] THEN
  MP_TAC POLYVAL_POLY_NONZERO THEN REWRITE_TAC[BOOL_POLY_ZERO] THEN
  DISCH_TAC THEN EQ_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(q = ring_0 bool_poly)` THEN
  ASM_REWRITE_TAC[BOOL_POLY_ZERO]);;

(* ------------------------------------------------------------------------- *)
(* Congruent 128-bit words mod Q(x) are equal.                               *)
(* (Unique representative: both have degree < 128 = deg Q.)                  *)
(* ------------------------------------------------------------------------- *)

let MOD_POLYVAL_WORD_EQ = prove
 (`!(x:128 word) (y:128 word).
   (poly_of_word x == poly_of_word y) (mod_polyval) ==> x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cong; mod_polyval; BOOL_POLY_OF_WORD] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `word_xor (x:128 word) y = word 0` MP_TAC THENL
   [MATCH_MP_TAC POLY_OF_WORD_INJ THEN
    REWRITE_TAC[POLY_OF_WORD_XOR; POLY_OF_WORD_0; GSYM BOOL_POLY_SUB] THEN
    MATCH_MP_TAC POLYVAL_DIVIDES_LOW_DEG THEN
    SIMP_TAC[RING_SUB; BOOL_POLY_OF_WORD] THEN CONJ_TAC THENL
     [REWRITE_TAC[POLY_OF_WORD_XOR; GSYM BOOL_POLY_SUB] THEN
      FIRST_X_ASSUM(MP_TAC o
        REWRITE_RULE[SIMP_RULE[POLYVAL_BOOL_POLY]
          (SPECL [`bool_poly`; `polyval_poly`]
            (INST_TYPE [`:((1->num)->bool)`,`:A`]
              IN_IDEAL_GENERATED_SING_EQ))]) THEN
      REWRITE_TAC[];
      REWRITE_TAC[BOOL_POLY_SUB; GSYM POLY_OF_WORD_XOR] THEN
      MP_TAC(ISPEC `word_xor (x:128 word) y`
        POLY_DEG_POLY_OF_WORD_BOUND) THEN
      CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC];
    REWRITE_TAC[WORD_XOR_EQ_0]]);;

(* ========================================================================= *)
(* Q(x) is irreducible -- proved via Rabin test.                             *)
(*                                                                           *)
(* 128 = 2^7 has only prime factor 2, so we check:                           *)
(*   1. Q | (x^(2^128) - x)          [Fermat check]                          *)
(*   2. gcd(Q, x^(2^64) - x) = 1     [coprimality via Bezout coefficients]   *)
(*                                                                           *)
(* Each of the 128 squaring steps x^(2^k) mod Q(x) is verified using a       *)
(* precomputed OCaml quotient witness: at step k, verify                     *)
(*   word_xor(w_k^2, w_{k+1}) = pmul(Q, q_k)                                 *)
(* inside HOL Light via PMUL_Q_256_SYM and WORD_RED_CONV (~1s/step).         *)
(* The OCaml precomputation is an untrusted oracle; the proof is in the      *)
(* HOL Light verification.                                                   *)
(* ========================================================================= *)


let MOD_POLYVAL_SUB = prove
 (`!p p' q q'.
      (p == p') (mod_polyval) /\ (q == q') (mod_polyval)
      ==> (ring_sub bool_poly p q == ring_sub bool_poly p' q') (mod_polyval)`,
 REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`p IN ring_carrier bool_poly`; `p' IN ring_carrier bool_poly`;
    `q IN ring_carrier bool_poly`; `q' IN ring_carrier bool_poly`] THEN
  ASM_SIMP_TAC[cong; mod_polyval; RING_SUB] THEN
  ASM_MESON_TAC[IN_RING_IDEAL_ADD; IN_RING_IDEAL_NEG;
                RING_IDEAL_IDEAL_GENERATED; RING_RULE
   `ring_add r (ring_sub r p p') (ring_neg r (ring_sub r q q')) =
    ring_sub r (ring_sub r p q) (ring_sub r p' q')`]);;

let MOD_POLYVAL_0 = prove
 (`(ring_0 bool_poly == ring_0 bool_poly) (mod_polyval)`,
  REWRITE_TAC[MOD_POLYVAL_REFL; RING_0]);;

let POLYVAL_CONG_FROM_QUOTIENT = prove
 (`!y z q. y IN ring_carrier bool_poly /\ z IN ring_carrier bool_poly /\
           q IN ring_carrier bool_poly /\
           ring_add bool_poly y z = ring_mul bool_poly polyval_poly q
           ==> (z == y) (mod_polyval)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cong; mod_polyval] THEN
  ASM_REWRITE_TAC[BOOL_POLY_SUB] THEN
  SUBGOAL_THEN `ring_add bool_poly z y = ring_mul bool_poly polyval_poly q`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `ring_add bool_poly z y = ring_add bool_poly y z` SUBST1_TAC THENL
     [MATCH_MP_TAC RING_ADD_SYM THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
    MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN
    REWRITE_TAC[IN_SING; POLYVAL_BOOL_POLY]]);;

let RHS_POLY_GENERAL = prove
 (`!q:256 word. 128 <= word_clz q ==>
   poly_of_word(word_pmul (word 0x1C2000000000000000000000000000001 : 256 word) q : 256 word) =
   ring_mul bool_poly polyval_poly (poly_of_word q)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(INST_TYPE [`:256`,`:N`] POLYVAL_POLY_OF_WORD) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC(INST_TYPE [`:256`,`:P`; `:256`,`:M`] POLY_OF_WORD_PMUL_GEN) THEN
  REWRITE_TAC[GSYM(INST_TYPE [`:256`,`:N`] POLYVAL_POLY_OF_WORD |>
    CONV_RULE(ONCE_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) |>
    REWRITE_RULE[ARITH])] THEN
  REWRITE_TAC[bool_poly; POLY_RING] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_MUL_LE o lhand o snd) THEN
  REWRITE_TAC[RING_POLYNOMIAL_POLYVAL_POLY; RING_POLYNOMIAL_OF_WORD] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS) THEN
  REWRITE_TAC[POLY_DEG_POLYVAL_POLY; POLY_DEG_POLY_OF_WORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  UNDISCH_TAC `128 <= word_clz (q:256 word)` THEN
  MP_TAC(ISPEC `q:256 word` WORD_CLZ_LE) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Squaring chain: x^(2^k) mod Q(x) for k = 0..128.                          *)
(* Built by repeated squaring with quotient-based reduction verification.    *)
(* Each step verifies word_xor(y_k, w_{k+1}) = pmul(Q, q_k) at word level.   *)
(* Total computation time: ~2 minutes.                                       *)
(* ------------------------------------------------------------------------- *)

let POLYVAL_SQUARE_STEP = prove
 (`!(x:int128) n.
   (ring_pow bool_poly (poly_var bool_ring one) (2 EXP n) ==
    poly_of_word x) (mod_polyval)
   ==> (ring_pow bool_poly (poly_var bool_ring one) (2 EXP SUC n) ==
        ring_mul bool_poly (poly_of_word x) (poly_of_word x)) (mod_polyval)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOD_POLYVAL_MUL o W CONJ) THEN
  SIMP_TAC[GSYM RING_POW_2; POLY_VARPOW_BOOL_POLY] THEN
  SIMP_TAC[RING_POW_POW; POLY_VAR_BOOL_POLY] THEN
  REWRITE_TAC[EXP; MULT_SYM]);;

let PMUL_128_256_BRIDGE = prove
 (`!x:int128. ring_mul bool_poly (poly_of_word x) (poly_of_word x) =
              poly_of_word(word_pmul x x : 256 word)`,
  GEN_TAC THEN REWRITE_TAC[GSYM pmul_128_256]);;

(* OCaml computation of the squaring chain and Rabin test data.              *)
(* This is an untrusted oracle: it proposes, for each step k, candidate      *)
(* values w_{k+1} and a claimed quotient q_k such that                       *)
(*   word_xor(pmul(w_k, w_k), w_{k+1}) = pmul(Q, q_k)                        *)
(* holds at the 256-bit word level. POLYVAL_CONG_STEP_CONV below verifies    *)
(* that identity independently inside HOL Light; if the OCaml code had a     *)
(* bug, the verification would fail.                                         *)
let n0 = Num.num_of_int 0 and n1 = Num.num_of_int 1 and n2 = Num.num_of_int 2;;

let poly_xor a b =
  let rec xor_aux a b =
    if a =/ n0 && b =/ n0 then n0
    else
      let a_bit = mod_num a n2 and b_bit = mod_num b n2 in
      (if a_bit =/ b_bit then n0 else n1) +/
      n2 */ (xor_aux (quo_num a n2) (quo_num b n2))
  in xor_aux a b;;

let poly_degree n =
  if n =/ n0 then -1
  else let rec d n k = if n =/ n0 then k-1 else d (quo_num n n2) (k+1) in d n 0;;

let poly_mod_q n =
  let rec reduce n =
    let d = poly_degree n in
    if d < 128 then n
    else
      let shift = Num.num_of_int (d - 128) in
      let n' = List.fold_left poly_xor n
        (List.map (fun b -> power_num n2 (Num.num_of_int b +/ shift))
          [0; 121; 126; 127; 128]) in
      reduce n'
  in reduce n;;

let poly_mul_gf2 a b =
  let rec mul_aux a b acc =
    if a =/ n0 then acc
    else
      let acc' = if mod_num a n2 =/ n1 then poly_xor acc b else acc in
      mul_aux (quo_num a n2) (b */ n2) acc'
  in mul_aux a b n0;;

let x_powpow = Array.make 129 n0;;
x_powpow.(0) <- n2;;
for k = 1 to 128 do x_powpow.(k) <- poly_mod_q (poly_mul_gf2 x_powpow.(k-1) x_powpow.(k-1)) done;;

let q_num = n1 +/ power_num n2 (Num.num_of_int 121) +/
            power_num n2 (Num.num_of_int 126) +/
            power_num n2 (Num.num_of_int 127) +/
            power_num n2 (Num.num_of_int 128);;

let poly_div_q_general a b =
  let rec div_loop a b q =
    let da = poly_degree a and db = poly_degree b in
    if da < db then (q, a)
    else
      let shift = da - db in
      let coeff = power_num n2 (Num.num_of_int shift) in
      div_loop (poly_xor a (poly_mul_gf2 b coeff)) b (poly_xor q coeff)
  in div_loop a b n0;;

let quotients = Array.init 128 (fun k ->
  let y_k = poly_mul_gf2 x_powpow.(k) x_powpow.(k) in
  let diff = poly_xor y_k x_powpow.(k+1) in
  fst(poly_div_q_general diff q_num));;

(* Build the HOL Light squaring chain using quotient verification            *)
let POLYVAL_CONG_STEP_CONV y_num z_num q_num =
  let y_tm = mk_comb(inst [`:256`,`:N`] `word:num->N word`, mk_numeral y_num) in
  let z_tm = mk_comb(inst [`:256`,`:N`] `word:num->N word`, mk_numeral z_num) in
  if q_num =/ n0 then
    SPEC y_tm (INST_TYPE [`:256`,`:N`] (prove(
      `!x:N word. (poly_of_word x == poly_of_word x) (mod_polyval)`,
      GEN_TAC THEN REWRITE_TAC[MOD_POLYVAL_REFL; BOOL_POLY_OF_WORD])))
  else
  let q_tm = mk_comb(inst [`:256`,`:N`] `word:num->N word`, mk_numeral q_num) in
  let xor_th = WORD_RED_CONV (mk_comb(mk_comb(`word_xor:256 word->256 word->256 word`, y_tm), z_tm)) in
  let pmul_expanded = SPEC q_tm PMUL_Q_256_SYM in
  let pmul_th = CONV_RULE(RAND_CONV(DEPTH_CONV WORD_RED_CONV)) pmul_expanded in
  if rand(concl xor_th) <> rand(concl pmul_th) then failwith "Quotient verification failed!" else
  let eq_th = TRANS xor_th (SYM pmul_th) in
  let xor_poly = ISPECL [y_tm; z_tm] (INST_TYPE [`:256`,`:N`] POLY_OF_WORD_XOR) in
  let clz_th = WORD_RED_CONV (mk_comb(`word_clz:256 word->num`, q_tm)) in
  let clz_ge = EQT_ELIM(NUM_REDUCE_CONV(mk_comb(mk_comb(`(<=):num->num->bool`, `128`), rand(concl clz_th)))) in
  let clz_ge' = CONV_RULE(RAND_CONV(REWR_CONV(SYM clz_th))) clz_ge in
  let rhs_poly = MATCH_MP RHS_POLY_GENERAL clz_ge' in
  let combined = TRANS (SYM xor_poly) (TRANS (AP_TERM `poly_of_word:256 word->((1->num)->bool)` eq_th) rhs_poly) in
  MATCH_MP POLYVAL_CONG_FROM_QUOTIENT
    (CONJ (SPEC y_tm (INST_TYPE [`:256`,`:N`] BOOL_POLY_OF_WORD))
    (CONJ (SPEC z_tm (INST_TYPE [`:256`,`:N`] BOOL_POLY_OF_WORD))
    (CONJ (SPEC q_tm (INST_TYPE [`:256`,`:N`] BOOL_POLY_OF_WORD))
    combined)));;

let polyval_base = prove
 (`(ring_pow bool_poly (poly_var bool_ring one) (2 EXP 0) ==
    poly_of_word(word 0x2:int128)) (mod_polyval)`,
  MATCH_MP_TAC MOD_POLYVAL_REFL_GEN THEN
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
  CONV_TAC NUM_REDUCE_CONV);;

let polyval_chain =
  let get_rhs_word th = rand(rand(rator(concl th))) in
  let rhs_conv c = RATOR_CONV(RAND_CONV c) in
  let suc_conv = RATOR_CONV(RATOR_CONV(RAND_CONV(RAND_CONV(RAND_CONV NUM_SUC_CONV)))) in
  let downcast tm =
    let (_,n_tm) = dest_comb tm in
    let w128 = mk_comb(inst [`:128`,`:N`] `word:num->N word`, n_tm) in
    CONV_RULE(LAND_CONV(RAND_CONV WORD_ZX_CONV)) (SPEC w128 zx_128_256) in
  let rec build k prev =
    if k > 128 then List.rev prev
    else if k = 0 then build 1 [polyval_base]
    else
      let prev_th = List.hd prev in
      let w_tm = get_rhs_word prev_th in
      let w_num = dest_numeral(rand w_tm) in
      let sq_th = MATCH_MP POLYVAL_SQUARE_STEP prev_th in
      let sq_th' = CONV_RULE(rhs_conv(REWR_CONV(SPEC w_tm PMUL_128_256_BRIDGE))) sq_th in
      let sq_th'' = CONV_RULE(rhs_conv(RAND_CONV WORD_PMUL_CONV)) sq_th' in
      let y_num = poly_mul_gf2 w_num w_num in
      let z_num = x_powpow.(k) in
      let q_num = quotients.(k-1) in
      let cong_th = POLYVAL_CONG_STEP_CONV y_num z_num q_num in
      let cong_sym = ONCE_REWRITE_RULE[MOD_POLYVAL_SYM] cong_th in
      let combined = MATCH_MP MOD_POLYVAL_TRANS (CONJ sq_th'' cong_sym) in
      let z_tm_256 = rand(rand(rator(concl combined))) in
      let dc_th = downcast z_tm_256 in
      let combined' = CONV_RULE(rhs_conv(REWR_CONV dc_th)) combined in
      let combined'' = CONV_RULE suc_conv combined' in
      build (k+1) (combined'' :: prev)
  in
  time (build 0) [];;

let [X_POWPOW_POLYVAL_128; X_POWPOW_POLYVAL_64] =
  let th_0 = SIMP_RULE[EXP; RING_POW_1; POLY_VAR_BOOL_POLY] (List.nth polyval_chain 0) in
  let th_64 = List.nth polyval_chain 64 in
  let th_128 = List.nth polyval_chain 128 in
  map
   (REWRITE_RULE[GSYM BOOL_POLY_SUB; POLY_OF_WORD_0] o
    CONV_RULE WORD_REDUCE_CONV o
    REWRITE_RULE[GSYM POLY_OF_WORD_XOR; BOOL_POLY_SUB])
   [MATCH_MP MOD_POLYVAL_SUB (CONJ th_128 th_0);
    MATCH_MP MOD_POLYVAL_SUB (CONJ th_64 th_0)];;

(* ------------------------------------------------------------------------- *)
(* Q(x) is irreducible (Rabin test).                                         *)
(* 128 = 2^7, only prime factor is 2, so we check:                           *)
(*   1. Q | (x^(2^128) - x)  [Fermat check]                                  *)
(*   2. gcd(Q, x^(2^64) - x) = 1  [coprimality via Bezout coefficients]      *)
(* ------------------------------------------------------------------------- *)

let BEZOUT_BOOL_POLY_Q = prove
 (`bezout_ring bool_poly`,
  REWRITE_TAC[bool_poly] THEN
  MESON_TAC[PID_EQ_UFD_BEZOUT_RING; PID_POLY_RING; FIELD_BOOL_RING]);;

let RING_IRREDUCIBLE_POLYVAL_POLYNOMIAL =
  let lemma = prove
   (`!s t. s IN ring_carrier bool_poly /\
           t IN ring_carrier bool_poly /\
           ring_add bool_poly (ring_mul bool_poly s polyval_poly)
                              (ring_mul bool_poly t p') =
           ring_1 bool_poly
           ==> (p == p') (mod_polyval) ==> ring_coprime bool_poly (polyval_poly,p)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SIMP_TAC[cong; mod_polyval; IN_IDEAL_GENERATED_SING_EQ; POLYVAL_BOOL_POLY] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_divides]) THEN
    ASM_SIMP_TAC[RING_SUB; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `d:(1->num)->bool` THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[BEZOUT_RING_COPRIME; BEZOUT_BOOL_POLY_Q] THEN
    EXISTS_TAC `ring_sub bool_poly s (ring_mul bool_poly t d)` THEN
    EXISTS_TAC `t:(1->num)->bool` THEN
    ASM_SIMP_TAC[RING_SUB; RING_MUL] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    SPEC_TAC(`bool_poly`,`r:((1->num)->bool)ring`) THEN
    RING_TAC) in
  prove
   (`ring_irreducible bool_poly polyval_poly`,
    REWRITE_TAC[bool_poly] THEN MATCH_MP_TAC RABIN_IRREDUCIBILITY_SUFFICIENT THEN
    EXISTS_TAC `128` THEN REWRITE_TAC[POLY_DEG_POLYVAL_POLY] THEN
    REWRITE_TAC[FIELD_BOOL_RING; FINITE_BOOL_RING; CARD_BOOL_RING] THEN
    REWRITE_TAC[GSYM bool_poly; POLYVAL_BOOL_POLY] THEN CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM
       `poly_deg bool_ring:((1->num)->bool)->num`) THEN
      REWRITE_TAC[POLY_DEG_POLYVAL_POLY] THEN
      REWRITE_TAC[bool_poly; POLY_RING; POLY_DEG_0; ARITH_EQ];
      REWRITE_TAC[ARITH_EQ] THEN
      REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 7`)]] THEN
    SIMP_TAC[IMP_CONJ; PRIME_DIVEXP_EQ] THEN
    SIMP_TAC[DIVIDES_PRIME_PRIME; PRIME_2; ARITH_EQ] THEN
    ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`] THEN
    REWRITE_TAC[FORALL_UNWIND_THM2; PRIME_2] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
    CONJ_TAC THENL
     [MP_TAC X_POWPOW_POLYVAL_128 THEN
      REWRITE_TAC[cong; mod_polyval; BOOL_POLY_SUB] THEN
      SIMP_TAC[RING_ADD; POLY_VARPOW_BOOL_POLY; POLY_VAR_BOOL_POLY; RING_0;
               RING_ADD_RZERO] THEN
      SIMP_TAC[IDEAL_GENERATED_SING; POLYVAL_BOOL_POLY; IN_ELIM_THM] THEN
      REWRITE_TAC[ring_divides; POLYVAL_BOOL_POLY] THEN
      SIMP_TAC[RING_ADD; POLY_VARPOW_BOOL_POLY; POLY_VAR_BOOL_POLY] THEN
      MESON_TAC[];
      MP_TAC X_POWPOW_POLYVAL_64 THEN MATCH_MP_TAC lemma THEN
      MAP_EVERY EXISTS_TAC
       [`poly_of_word(word 5531881272956166784419046509281262267:129 word)`;
        `poly_of_word(word 35795823274625314041854535045156374719:129 word)`] THEN
      REWRITE_TAC[BOOL_POLY_OF_WORD] THEN
      MP_TAC(INST_TYPE [`:129`,`:N`] POLYVAL_POLY_OF_WORD) THEN
      MP_TAC(INST_TYPE [`:128`,`:M`; `:129`,`:N`] POLY_OF_WORD_ZX) THEN
      CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
      DISCH_THEN SUBST1_TAC THEN CONV_TAC(ONCE_DEPTH_CONV WORD_ZX_CONV) THEN
      REWRITE_TAC[GSYM POLY_OF_WORD_PMUL_2N; GSYM POLY_OF_WORD_XOR] THEN
      CONV_TAC(DEPTH_CONV(WORD_PMUL_CONV ORELSEC WORD_RED_CONV)) THEN
      REWRITE_TAC[POLY_OF_WORD_1]]);;

(* ========================================================================= *)
(* Cancellation lemma: x^n can be cancelled in congruences mod Q(x).         *)
(* This does NOT require irreducibility -- only gcd(Q, x) = 1 (Q(0) = 1).    *)
(* ========================================================================= *)

let POLYVAL_COPRIME_VAR = prove
 (`ring_coprime bool_poly (polyval_poly, poly_var bool_ring one)`,
  ASM_SIMP_TAC[BEZOUT_RING_COPRIME; BEZOUT_BOOL_POLY_Q] THEN
  REWRITE_TAC[POLYVAL_BOOL_POLY; POLY_VAR_BOOL_POLY] THEN
  MAP_EVERY EXISTS_TAC
   [`poly_of_word(word 1:129 word)`;
    `poly_of_word(word 299076299051606071403356588563077529600:129 word)`] THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD] THEN
  MP_TAC(INST_TYPE [`:129`,`:N`] POLYVAL_POLY_OF_WORD) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `poly_var bool_ring one = poly_of_word(word 2:129 word)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`1`] (INST_TYPE [`:129`,`:N`] POLY_VAR_POW_OF_WORD)) THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[RING_POW_1; POLY_VAR_BOOL_POLY];
    REWRITE_TAC[GSYM POLY_OF_WORD_PMUL_2N; GSYM POLY_OF_WORD_XOR] THEN
    CONV_TAC(DEPTH_CONV(WORD_PMUL_CONV ORELSEC WORD_RED_CONV)) THEN
    REWRITE_TAC[POLY_OF_WORD_1]]);;

let POLYVAL_COPRIME_VARPOW = prove
 (`!n. ring_coprime bool_poly (polyval_poly, ring_pow bool_poly (poly_var bool_ring one) n)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[ring_pow; ring_coprime; POLYVAL_BOOL_POLY; RING_1] THEN
    MESON_TAC[RING_DIVIDES_ONE; RING_UNIT_1];
    REWRITE_TAC[ring_pow] THEN
    MP_TAC(ISPECL [`bool_poly`; `polyval_poly`;
                    `poly_var bool_ring one`;
                    `ring_pow bool_poly (poly_var bool_ring one) n`]
      RING_COPRIME_RMUL) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INTEGRAL_DOMAIN_BOOL_POLY; BEZOUT_BOOL_POLY_Q] THEN
      REWRITE_TAC[POLYVAL_BOOL_POLY; POLY_VAR_BOOL_POLY; POLY_VARPOW_BOOL_POLY];
      ASM_REWRITE_TAC[POLYVAL_COPRIME_VAR]]]);;

let MOD_POLYVAL_CANCEL_VARPOW = prove
 (`!n (x:int128) (y:int128).
   (ring_mul bool_poly (poly_of_word x) (ring_pow bool_poly (poly_var bool_ring one) n) ==
    ring_mul bool_poly (poly_of_word y) (ring_pow bool_poly (poly_var bool_ring one) n))
   (mod_polyval)
   ==> x = y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_POLYVAL_WORD_EQ THEN
  REWRITE_TAC[cong; mod_polyval; BOOL_POLY_SUB; BOOL_POLY_OF_WORD;
              MATCH_MP IN_IDEAL_GENERATED_SING_EQ POLYVAL_BOOL_POLY] THEN
  MATCH_MP_TAC(ISPEC `bool_poly` RING_COPRIME_DIVPROD_RIGHT) THEN
  EXISTS_TAC `ring_pow bool_poly (poly_var bool_ring one) n` THEN
  REWRITE_TAC[INTEGRAL_DOMAIN_BOOL_POLY; BEZOUT_BOOL_POLY_Q;
              RING_ADD; BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY] THEN
  ONCE_REWRITE_TAC[RING_COPRIME_SYM] THEN
  REWRITE_TAC[POLYVAL_COPRIME_VARPOW] THEN
  SUBGOAL_THEN
    `ring_mul bool_poly
      (ring_add bool_poly (poly_of_word (x:int128)) (poly_of_word (y:int128)))
      (ring_pow bool_poly (poly_var bool_ring one) n) =
     ring_add bool_poly
      (ring_mul bool_poly (poly_of_word x) (ring_pow bool_poly (poly_var bool_ring one) n))
      (ring_mul bool_poly (poly_of_word y) (ring_pow bool_poly (poly_var bool_ring one) n))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC RING_ADD_RDISTRIB THEN
    REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[cong; mod_polyval; BOOL_POLY_SUB;
      RING_MUL; BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY;
      MATCH_MP IN_IDEAL_GENERATED_SING_EQ POLYVAL_BOOL_POLY;
      RING_ADD]) THEN
    SIMP_TAC[RING_MUL; RING_ADD; BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY]]);;

(* General cancellation for arbitrary polynomials (not just poly_of_word)    *)
let MOD_POLYVAL_CANCEL_VARPOW_GEN = prove
 (`!n p q. p IN ring_carrier bool_poly /\
           q IN ring_carrier bool_poly /\
           (ring_mul bool_poly p (ring_pow bool_poly (poly_var bool_ring one) n) ==
            ring_mul bool_poly q (ring_pow bool_poly (poly_var bool_ring one) n))
           mod_polyval
           ==> (p == q) mod_polyval`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `ring_divides bool_poly polyval_poly
      (ring_mul bool_poly (ring_sub bool_poly p q)
        (ring_pow bool_poly (poly_var bool_ring one) n))`
  MP_TAC THENL
   [SUBGOAL_THEN `ring_mul bool_poly (ring_sub bool_poly p q)
        (ring_pow bool_poly (poly_var bool_ring one) n) =
      ring_sub bool_poly
        (ring_mul bool_poly p (ring_pow bool_poly (poly_var bool_ring one) n))
        (ring_mul bool_poly q (ring_pow bool_poly (poly_var bool_ring one) n))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RING_SUB_RDISTRIB THEN
      ASM_REWRITE_TAC[POLY_VARPOW_BOOL_POLY];
      UNDISCH_TAC `(ring_mul bool_poly p
        (ring_pow bool_poly (poly_var bool_ring one) n) ==
        ring_mul bool_poly q
        (ring_pow bool_poly (poly_var bool_ring one) n)) mod_polyval` THEN
      REWRITE_TAC[cong; mod_polyval; MATCH_MP IN_IDEAL_GENERATED_SING_EQ
        POLYVAL_BOOL_POLY] THEN
      ASM_SIMP_TAC[RING_MUL; POLY_VARPOW_BOOL_POLY; BOOL_POLY_SUB] THEN
      REWRITE_TAC[ring_divides] THEN
      ASM_SIMP_TAC[POLYVAL_BOOL_POLY; RING_MUL; RING_ADD; RING_SUB;
                   POLY_VARPOW_BOOL_POLY]];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`bool_poly`; `ring_sub bool_poly (p:(1->num)->bool) q`;
      `ring_pow bool_poly (poly_var bool_ring one) n`;
      `polyval_poly`] RING_COPRIME_DIVPROD_RIGHT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[RING_SUB; POLY_VARPOW_BOOL_POLY] THEN
      ONCE_REWRITE_TAC[RING_COPRIME_SYM] THEN
      REWRITE_TAC[POLYVAL_COPRIME_VARPOW] THEN
      DISJ2_TAC THEN REWRITE_TAC[INTEGRAL_DOMAIN_BOOL_POLY; BEZOUT_BOOL_POLY_Q];
      DISCH_TAC THEN
      REWRITE_TAC[cong; mod_polyval; BOOL_POLY_SUB;
        MATCH_MP IN_IDEAL_GENERATED_SING_EQ POLYVAL_BOOL_POLY] THEN
      ASM_SIMP_TAC[RING_ADD; POLYVAL_BOOL_POLY] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[BOOL_POLY_SUB]) THEN
      ASM_REWRITE_TAC[]]]);;
