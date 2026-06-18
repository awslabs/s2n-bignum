(* ========================================================================= *)
(* Proof of POLYVAL_REDUCE_PROP3_CORRECT: Gueron's Proposition 3.             *)
(* Shows: polyval_reduce_prop3(T) * x^128 ≡ T (mod Q(x))                     *)
(*                                                                           *)
(* Strategy:                                                                 *)
(* 1. Define the quotient witness: A + V*x^64                               *)
(* 2. Show (prop3(T)*x^128 + T) = quotient(T) * Q(x) in bool_poly          *)
(* 3. The identity is verified lane-by-lane (4 x 64-bit lanes)              *)
(*                                                                           *)
(* Key helper lemmas:                                                        *)
(* - PMUL_W_64_128: expands pmul by W into shifts+XORs                      *)
(* - PMUL_Q_256: expands pmul by Q(x) into shifts+XORs                      *)
(* - POLY_VAR_POW_OF_WORD: x^k = poly_of_word(word(2^k))                    *)
(* - BOOL_POLY_ADD_SELF: char 2 property (a+a=0)                            *)
(* ========================================================================= *)

needs "common/polyval.ml";;

(* ------------------------------------------------------------------------- *)
(* The quotient witness for ideal membership.                                *)
(* For T = D*x^192 + C*x^128 + B*x^64 + A, the quotient is A + V*x^64     *)
(* where V = B XOR low64(W*A).                                              *)
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
(* Helper: x^k = poly_of_word(word(2^k)) when k < dimindex.                 *)
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
(* W = 2^63 + 2^62 + 2^57, so pmul by W = shl 63 XOR shl 62 XOR shl 57.   *)
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
(* Expand word_pmul by Q(x) = 0x1C2...01 into shifts + XORs.                *)
(* Q = 2^128 + 2^127 + 2^126 + 2^121 + 1.                                  *)
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
(* Decompose 256-bit word equality into 4 x 64-bit lane equalities.         *)
(* ------------------------------------------------------------------------- *)

let WORD_EQ_LANES_256 = prove
 (`!x y : 256 word.
    x = y <=>
    (word_subword x (0,64) : 64 word) = word_subword y (0,64) /\
    (word_subword x (64,64) : 64 word) = word_subword y (64,64) /\
    (word_subword x (128,64) : 64 word) = word_subword y (128,64) /\
    (word_subword x (192,64) : 64 word) = word_subword y (192,64)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  SIMP_TAC[BIT_WORD_SUBWORD; DIMINDEX_64; DIMINDEX_256;
           ARITH_RULE `MIN 64 256 = 64`; ADD_CLAUSES;
           ARITH_RULE `MIN 64 64 = 64`] THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < 64 \/ (64 <= i /\ i < 128) \/
                (128 <= i /\ i < 192) \/ (192 <= i /\ i < 256)` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o CONJUNCT1) THEN
   DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[];
   FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
   DISCH_THEN(MP_TAC o SPEC `i - 64`) THEN
   SUBGOAL_THEN `i - 64 < 64 /\ 64 + (i - 64) = i` MP_TAC THENL
    [ASM_ARITH_TAC; SIMP_TAC[]];
   FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
   DISCH_THEN(MP_TAC o SPEC `i - 128`) THEN
   SUBGOAL_THEN `i - 128 < 64 /\ 128 + (i - 128) = i` MP_TAC THENL
    [ASM_ARITH_TAC; SIMP_TAC[]];
   FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
   DISCH_THEN(MP_TAC o SPEC `i - 192`) THEN
   SUBGOAL_THEN `i - 192 < 64 /\ 192 + (i - 192) = i` MP_TAC THENL
    [ASM_ARITH_TAC; SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The 256-bit word identity: result*x^128 + T = quotient * Q(x).           *)
(* Proved lane-by-lane using BITBLAST_TAC (BDD-based bit-blasting).         *)
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
(* LHS: result*x^128 + T = poly_of_word(word_xor(shl(zx result)128) t)      *)
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
(* Main theorem: Proposition 3 computes T * x^{-128} mod Q(x).              *)
(* Equivalently: result * x^128 ≡ T (mod Q(x)).                             *)
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
