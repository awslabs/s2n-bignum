(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

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
(*      proofs below (and re-used by karatsuba_pmul.ml).                     *)
(*   4. Q(x) structural facts: integral-domain structure, congruence         *)
(*      linchpin (MOD_POLYVAL_WORD_EQ), and x^n cancellation                 *)
(*      (MOD_POLYVAL_CANCEL_VARPOW{,_GEN}).                                  *)
(* The irreducibility of Q(x), which nothing here depends on, is proved in  *)
(* common/gf128_irreducible.ml.                                             *)
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
(* Expand word_pmul by W = 0xC200000000000000 into shifts + XORs.            *)
(* W = 2^63 + 2^62 + 2^57, so pmul by W = shl 63 XOR shl 62 XOR shl 57.      *)
(* ------------------------------------------------------------------------- *)

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
(* below (and by common/karatsuba_pmul.ml, which loads after this           *)
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
(* and x^n cancellation.                                                     *)
(*                                                                           *)
(* This material extends the primitive POLYVAL algebra above (Q(x),          *)
(* mod_polyval, polyval_reduce_prop3, POLYVAL_REDUCE_PROP3_CORRECT) with     *)
(* the structural theorems needed by downstream GHASH proofs:                *)
(*                                                                           *)
(*   INTEGRAL_DOMAIN_BOOL_POLY    GF(2)[x] is an integral domain             *)
(*   POLYVAL_POLY_NONZERO         Q(x) != 0                                  *)
(*   POLYVAL_DIVIDES_LOW_DEG      Q | p /\ deg p < 128  ==>  p = 0           *)
(*   MOD_POLYVAL_WORD_EQ          Congruent 128-bit words are equal          *)
(*   MOD_POLYVAL_CANCEL_VARPOW{,_GEN}      Cancel x^n from congruences       *)
(*                                                                           *)
(* The irreducibility of Q(x) is proved in common/gf128_irreducible.ml.      *)
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
(* Cancellation lemma: x^n can be cancelled in congruences mod Q(x).         *)
(* This does NOT require irreducibility -- only gcd(Q, x) = 1 (Q(0) = 1).    *)
(* ========================================================================= *)

let POLYVAL_COPRIME_VAR = prove
 (`ring_coprime bool_poly (polyval_poly, poly_var bool_ring one)`,
  ASM_SIMP_TAC[BEZOUT_RING_COPRIME; BEZOUT_BOOL_POLY] THEN
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
     [REWRITE_TAC[INTEGRAL_DOMAIN_BOOL_POLY; BEZOUT_BOOL_POLY] THEN
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
  REWRITE_TAC[INTEGRAL_DOMAIN_BOOL_POLY; BEZOUT_BOOL_POLY;
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
      DISJ2_TAC THEN REWRITE_TAC[INTEGRAL_DOMAIN_BOOL_POLY; BEZOUT_BOOL_POLY];
      DISCH_TAC THEN
      REWRITE_TAC[cong; mod_polyval; BOOL_POLY_SUB;
        MATCH_MP IN_IDEAL_GENERATED_SING_EQ POLYVAL_BOOL_POLY] THEN
      ASM_SIMP_TAC[RING_ADD; POLYVAL_BOOL_POLY] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[BOOL_POLY_SUB]) THEN
      ASM_REWRITE_TAC[]]]);;
