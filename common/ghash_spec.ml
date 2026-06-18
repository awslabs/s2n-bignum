(* ========================================================================= *)
(* GHASH specification extras: 3- and 4-block Horner unrolling lemmas.       *)
(*                                                                           *)
(* The core POLYVAL/GHASH algebra (polyval_dot, ghash_polyval_acc, h_power,  *)
(* karatsuba_mid, INNER_CONG_GEN, GHASH_POLYVAL_ACC_2, the irreducibility    *)
(* machinery, MOD_POLYVAL_CANCEL_VARPOW, ...) now lives upstream in          *)
(* common/polyval_ghash.ml and common/polyval.ml.  This file adds only the   *)
(* extra unrolling lemmas the AES-256-GCM N-block proofs consume that are    *)
(* not (yet) upstream:                                                       *)
(*   BOOL_POLY_MUL_ASSOC, BOOL_POLY_MUL_ASSOC_REV  (ring-algebra helpers)    *)
(*   HELPER_3            polyval_dot(a⊕p,h)·h² ≡ a·h³ + p·h³ (mod Q)         *)
(*   GHASH_POLYVAL_ACC_3 3-block Horner unrolling specialization             *)
(*   GHASH_POLYVAL_ACC_4 4-block Horner unrolling specialization             *)
(* ========================================================================= *)

needs "common/karatsuba_pmul_proof.ml";;
needs "common/polyval_ghash.ml";;

(* Ring algebra helpers for bool_poly *)
let BOOL_POLY_MUL_ASSOC = prove
 (`!a b c. a IN ring_carrier bool_poly /\
           b IN ring_carrier bool_poly /\
           c IN ring_carrier bool_poly
           ==> ring_mul bool_poly (ring_mul bool_poly a b) c =
               ring_mul bool_poly a (ring_mul bool_poly b c)`,
  SIMP_TAC[RING_MUL_ASSOC]);;

let BOOL_POLY_MUL_ASSOC_REV = prove
 (`!a b c. a IN ring_carrier bool_poly /\
           b IN ring_carrier bool_poly /\
           c IN ring_carrier bool_poly
           ==> ring_mul bool_poly a (ring_mul bool_poly b c) =
               ring_mul bool_poly (ring_mul bool_poly a b) c`,
  SIMP_TAC[RING_MUL_ASSOC]);;

(* Helper: polyval_dot(a⊕p, h)·h² ≡ a·h³ + p·h³ (mod Q), where               *)
(* h³ = polyval_dot h (polyval_dot h h).  Bridges via INNER_CONG_GEN,         *)
(* after first commuting polyval_dot h h² = polyval_dot h² h (via pmul_sym). *)

let HELPER_3 = prove
 (`!(a:int128) (p:int128) (h:int128).
    (ring_mul bool_poly (poly_of_word (polyval_dot (word_xor a p) h))
       (poly_of_word (polyval_dot h h)) ==
     ring_add bool_poly
       (ring_mul bool_poly (poly_of_word a) (poly_of_word (polyval_dot h (polyval_dot h h))))
       (ring_mul bool_poly (poly_of_word p) (poly_of_word (polyval_dot h (polyval_dot h h)))))
    mod_polyval`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
    `ring_mul bool_poly
      (ring_add bool_poly (poly_of_word (a:int128)) (poly_of_word (p:int128)))
      (poly_of_word (polyval_dot (h:int128) (polyval_dot h h)))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `polyval_dot (h:int128) (polyval_dot h h) = polyval_dot (polyval_dot (h:int128) h) h`
      SUBST1_TAC THENL
     [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:int128`; `word_xor (a:int128) (p:int128)`; `1`] INNER_CONG_GEN) THEN
    REWRITE_TAC[TWO; ONE; h_power; POLY_OF_WORD_XOR];
    MATCH_MP_TAC MOD_POLYVAL_REFL_GEN THEN
    SIMP_TAC[RING_MUL; RING_ADD; BOOL_POLY_OF_WORD] THEN
    MATCH_MP_TAC(GSYM RING_ADD_RDISTRIB) THEN REWRITE_TAC[BOOL_POLY_OF_WORD]]);;

let GHASH_POLYVAL_ACC_3 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128).
    ghash_polyval_acc h a [p:int128; q; r] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot h (polyval_dot h h)) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot h h) : 256 word)
        (word_pmul r h : 256 word)))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ghash_polyval_acc] THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_2] THEN
  REWRITE_TAC[WORD_PMUL_XOR] THEN
  MATCH_MP_TAC(ISPEC `128` MOD_POLYVAL_CANCEL_VARPOW) THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
    `poly_of_word (word_xor
      (word_xor (word_pmul (polyval_dot (word_xor (a:int128) (p:int128)) (h:int128)) (polyval_dot h h))
                (word_pmul (q:int128) (polyval_dot h h)))
      (word_pmul (r:int128) (h:int128)) : 256 word)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[POLYVAL_REDUCE_PROP3_CORRECT];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
    `poly_of_word (word_xor
      (word_xor (word_pmul (a:int128) (polyval_dot h (polyval_dot h h)))
                (word_pmul (p:int128) (polyval_dot h (polyval_dot h h))))
      (word_xor (word_pmul (q:int128) (polyval_dot h h))
                (word_pmul (r:int128) (h:int128))) : 256 word)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[POLYVAL_REDUCE_PROP3_CORRECT];
    ALL_TAC] THEN
  REWRITE_TAC[POLY_OF_WORD_XOR; POLY_OF_WORD_PMUL_2N] THEN
  MP_TAC(SPECL [`a:int128`; `p:int128`; `h:int128`] HELPER_3) THEN
  REWRITE_TAC[mod_polyval] THEN DISCH_TAC THEN
  ABBREV_TAC `pX = ring_mul bool_poly (poly_of_word (polyval_dot (word_xor (a:int128) (p:int128)) (h:int128))) (poly_of_word (polyval_dot (h:int128) h))` THEN
  ABBREV_TAC `pY = ring_add bool_poly
    (ring_mul bool_poly (poly_of_word (a:int128)) (poly_of_word (polyval_dot (h:int128) (polyval_dot h h))))
    (ring_mul bool_poly (poly_of_word (p:int128)) (poly_of_word (polyval_dot (h:int128) (polyval_dot h h))))` THEN
  ABBREV_TAC `pQ = ring_mul bool_poly (poly_of_word (q:int128)) (poly_of_word (polyval_dot (h:int128) h))` THEN
  ABBREV_TAC `pR = ring_mul bool_poly (poly_of_word (r:int128)) (poly_of_word (h:int128))` THEN
  SUBGOAL_THEN
    `pX IN ring_carrier bool_poly /\ pY IN ring_carrier bool_poly /\ pQ IN ring_carrier bool_poly /\ pR IN ring_carrier bool_poly`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["pX"; "pY"; "pQ"; "pR"] THEN
    SIMP_TAC[RING_MUL; RING_ADD; BOOL_POLY_OF_WORD];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `ring_add bool_poly (ring_add bool_poly pX pQ) pR =
     ring_add bool_poly pX (ring_add bool_poly pQ pR)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM RING_ADD_ASSOC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOD_POLYVAL_ADD THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOD_POLYVAL_REFL_GEN THEN ASM_SIMP_TAC[RING_ADD]]);;

(* ========================================================================= *)
(* GHASH_POLYVAL_ACC_4: 4-block Horner unrolling specialization.            *)
(* Derived directly from GHASH_POLYVAL_ACC_BATCHED for list [p;q;r;s].      *)
(* Unfolds h_power 0..3 to the polyval_dot chain (h, h^2, h^3, h^4).         *)
(* ========================================================================= *)

let GHASH_POLYVAL_ACC_4 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128).
    ghash_polyval_acc h a [p:int128; q; r; s] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot h h) : 256 word)
        (word_pmul s h : 256 word))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;
