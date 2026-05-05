(* ========================================================================= *)
(* POLYVAL: The POLYVAL polynomial Q(x) from RFC 8452 (AES-GCM-SIV).         *)
(* Q(x) = x^128 + x^127 + x^126 + x^121 + 1.                                 *)
(* Also used for GHASH via Gueron's reinterpretation (CSCML 2023).           *)
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
