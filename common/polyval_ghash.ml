(* ========================================================================= *)
(* GHASH specification and Horner unrolling lemma.                           *)
(*                                                                           *)
(* Defines the POLYVAL dot operation and GHASH Horner iteration in terms     *)
(* of polynomial arithmetic mod Q(x), then proves GHASH_POLYVAL_ACC_2:       *)
(* the 2-block Horner-to-batched equality.                                   *)
(*                                                                           *)
(* Key definitions:                                                          *)
(*   polyval_dot a b    = prop3(pmul(a,b)) = a*b*x^{-128} mod Q(x)          *)
(*   ghash_polyval_acc h acc xs = Horner iteration (left fold)               *)
(*                                                                           *)
(* Key theorems:                                                             *)
(*   POLYVAL_DOT_CORRECT: dot(a,b)*x^128 == a*b (mod Q)                      *)
(*   GHASH_ACC_APPEND: left fold splits over APPEND                          *)
(*   INNER_CONG: (a+b) * dot(h,h) == dot(a XOR b, h) * h  (mod Q)            *)
(*   GHASH_POLYVAL_ACC_2: 2-block Horner equals batched form                 *)
(*                                                                           *)
(* Q(x) structural facts (integral-domain/irreducibility, cancellation,      *)
(* congruence-to-word-equality) live in common/polyval.ml.                   *)
(* ========================================================================= *)

needs "common/polyval.ml";;

(* ------------------------------------------------------------------------- *)
(* The POLYVAL "dot" operation: dot(a,b) = a * b * x^{-128} mod Q(x).       *)
(* Defined computationally as prop3(pmul(a,b)).                              *)
(* ------------------------------------------------------------------------- *)

let polyval_dot = new_definition
 `polyval_dot (a:128 word) (b:128 word) : 128 word =
  polyval_reduce_prop3 (word_pmul a b : 256 word)`;;

(* dot(a,b) * x^128 == a * b (mod Q(x))                                      *)
let POLYVAL_DOT_CORRECT = prove
 (`!a b : 128 word.
   (ring_mul bool_poly
     (poly_of_word (polyval_dot a b))
     (ring_pow bool_poly (poly_var bool_ring one) 128)
    == ring_mul bool_poly (poly_of_word a) (poly_of_word b))
   (mod_polyval)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polyval_dot] THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
    `poly_of_word (word_pmul (a:128 word) (b:128 word) : 256 word)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[POLYVAL_REDUCE_PROP3_CORRECT];
    REWRITE_TAC[GSYM pmul_128_256; MOD_POLYVAL_REFL;
                RING_MUL; BOOL_POLY_OF_WORD]]);;

(* ------------------------------------------------------------------------- *)
(* GHASH Horner iteration (left fold over block list).                       *)
(* ghash_polyval_acc h acc [X1;X2;...;Xn] processes X1 first, Xn last.      *)
(* This matches the NIST GHASH specification order.                          *)
(* ------------------------------------------------------------------------- *)

let ghash_polyval_acc = define
 `ghash_polyval_acc (h:128 word) (acc:128 word) [] = acc /\
  ghash_polyval_acc h acc (CONS x xs) =
    ghash_polyval_acc h (polyval_dot (word_xor acc x) h) xs`;;

(* APPEND splits the fold *)
let GHASH_ACC_APPEND = prove
 (`!h xs ys acc. ghash_polyval_acc h acc (APPEND xs ys) =
                 ghash_polyval_acc h (ghash_polyval_acc h acc xs) ys`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; ghash_polyval_acc]);;

(* Step congruence: result * x^128 == (acc + x) * H (mod Q)                  *)
let GHASH_ACC_STEP_CONG = prove
 (`!h acc x.
   (ring_mul bool_poly
     (poly_of_word (ghash_polyval_acc h acc [x]))
     (ring_pow bool_poly (poly_var bool_ring one) 128)
    == ring_mul bool_poly
         (ring_add bool_poly (poly_of_word acc) (poly_of_word x))
         (poly_of_word h))
   (mod_polyval)`,
  REWRITE_TAC[ghash_polyval_acc; GSYM POLY_OF_WORD_XOR;
              POLYVAL_DOT_CORRECT]);;

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

let BOOL_POLY_MUL_COMM23 = prove
 (`!a b c. a IN ring_carrier bool_poly /\
           b IN ring_carrier bool_poly /\
           c IN ring_carrier bool_poly
           ==> ring_mul bool_poly (ring_mul bool_poly a b) c =
               ring_mul bool_poly (ring_mul bool_poly a c) b`,
  MESON_TAC[RING_MUL_ASSOC; RING_MUL_SYM; RING_MUL]);;

(* Specific ring equalities for the 2-block Horner proof *)
let COMM23_SPEC = prove
 (`ring_mul bool_poly
    (ring_mul bool_poly (poly_of_word (polyval_dot (word_xor (a:int128) (b:int128)) (h:int128))) (poly_of_word h))
    (ring_pow bool_poly (poly_var bool_ring one) 128) =
   ring_mul bool_poly
    (ring_mul bool_poly (poly_of_word (polyval_dot (word_xor a b) h)) (ring_pow bool_poly (poly_var bool_ring one) 128))
    (poly_of_word h)`,
  MATCH_MP_TAC BOOL_POLY_MUL_COMM23 THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY]);;

let ASSOC_SPEC = prove
 (`ring_mul bool_poly
    (ring_mul bool_poly (ring_add bool_poly (poly_of_word (a:int128)) (poly_of_word (b:int128))) (poly_of_word (polyval_dot (h:int128) h)))
    (ring_pow bool_poly (poly_var bool_ring one) 128) =
   ring_mul bool_poly
    (ring_add bool_poly (poly_of_word a) (poly_of_word b))
    (ring_mul bool_poly (poly_of_word (polyval_dot h h)) (ring_pow bool_poly (poly_var bool_ring one) 128))`,
  MATCH_MP_TAC BOOL_POLY_MUL_ASSOC THEN
  SIMP_TAC[RING_ADD; BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY]);;

let ASSOC_REV_SPEC = prove
 (`ring_mul bool_poly
    (ring_add bool_poly (poly_of_word (a:int128)) (poly_of_word (b:int128)))
    (ring_mul bool_poly (poly_of_word (h:int128)) (poly_of_word h)) =
   ring_mul bool_poly
    (ring_mul bool_poly (ring_add bool_poly (poly_of_word a) (poly_of_word b)) (poly_of_word h))
    (poly_of_word h)`,
  MATCH_MP_TAC BOOL_POLY_MUL_ASSOC_REV THEN
  SIMP_TAC[RING_ADD; BOOL_POLY_OF_WORD]);;

(* Inner congruence: (a+b)*dot(h,h) == dot(a XOR b,h)*h (mod Q)              *)
let INNER_CONG = prove
 (`!(h:int128) (a:int128) (b:int128).
    (ring_mul bool_poly
      (ring_add bool_poly (poly_of_word a) (poly_of_word b))
      (poly_of_word (polyval_dot h h)) ==
     ring_mul bool_poly
      (poly_of_word (polyval_dot (word_xor a b) h))
      (poly_of_word h)) mod_polyval`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
  MATCH_MP_TAC(ISPEC `128` MOD_POLYVAL_CANCEL_VARPOW_GEN) THEN
  SIMP_TAC[RING_MUL; RING_ADD; BOOL_POLY_OF_WORD] THEN
  ONCE_REWRITE_TAC[COMM23_SPEC] THEN ONCE_REWRITE_TAC[ASSOC_SPEC] THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
    `ring_mul bool_poly
      (ring_add bool_poly (poly_of_word (a:int128)) (poly_of_word (b:int128)))
      (ring_mul bool_poly (poly_of_word (h:int128)) (poly_of_word h))` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ASSOC_REV_SPEC] THEN
    MP_TAC(ISPECL
      [`ring_mul bool_poly (poly_of_word (polyval_dot (word_xor (a:int128) (b:int128)) (h:int128))) (ring_pow bool_poly (poly_var bool_ring one) 128)`;
       `ring_mul bool_poly (ring_add bool_poly (poly_of_word (a:int128)) (poly_of_word (b:int128))) (poly_of_word (h:int128))`;
       `poly_of_word (h:int128)`; `poly_of_word (h:int128)`] MOD_POLYVAL_MUL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`word_xor (a:int128) (b:int128)`; `h:int128`] POLYVAL_DOT_CORRECT) THEN REWRITE_TAC[POLY_OF_WORD_XOR];
        REWRITE_TAC[MOD_POLYVAL_REFL; BOOL_POLY_OF_WORD]]; REWRITE_TAC[]];
    ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
    MP_TAC(ISPECL
      [`ring_add bool_poly (poly_of_word (a:int128)) (poly_of_word (b:int128))`;
       `ring_add bool_poly (poly_of_word (a:int128)) (poly_of_word (b:int128))`;
       `ring_mul bool_poly (poly_of_word (polyval_dot (h:int128) h)) (ring_pow bool_poly (poly_var bool_ring one) 128)`;
       `ring_mul bool_poly (poly_of_word (h:int128)) (poly_of_word h)`] MOD_POLYVAL_MUL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[MOD_POLYVAL_REFL; RING_ADD; BOOL_POLY_OF_WORD];
        REWRITE_TAC[POLYVAL_DOT_CORRECT]]; REWRITE_TAC[]] THEN
    SIMP_TAC[RING_ADD; BOOL_POLY_OF_WORD]]);;

(* ========================================================================= *)
(* 2-block Horner unrolling: ghash_polyval_acc h a [b;c] = prop3(...)        *)
(* Processing 2 GHASH blocks iteratively equals a batched computation:       *)
(* XOR of 256-bit polynomial multiplications followed by Prop 3 reduction    *)
(* This matches the Loop_mod2x_v8 loop in ghashv8-armx.S                    *)
(* ========================================================================= *)

let GHASH_POLYVAL_ACC_2 = prove
 (`!(h:int128) (a:int128) (b:int128) (c:int128).
    ghash_polyval_acc h a [b; c] =
    polyval_reduce_prop3
      (word_xor (word_pmul (word_xor a b) (polyval_dot h h) : 256 word)
                (word_pmul c h : 256 word))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ghash_polyval_acc] THEN
  MATCH_MP_TAC(ISPEC `128` MOD_POLYVAL_CANCEL_VARPOW) THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC
    `ring_add bool_poly
      (ring_mul bool_poly (poly_of_word (polyval_dot (word_xor (a:int128) (b:int128)) (h:int128))) (poly_of_word h))
      (ring_mul bool_poly (poly_of_word (c:int128)) (poly_of_word h))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
    EXISTS_TAC
      `ring_mul bool_poly
        (ring_add bool_poly (poly_of_word (polyval_dot (word_xor (a:int128) (b:int128)) (h:int128))) (poly_of_word (c:int128)))
        (poly_of_word h)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`word_xor (polyval_dot (word_xor (a:int128) (b:int128)) (h:int128)) (c:int128)`; `h:int128`] POLYVAL_DOT_CORRECT) THEN REWRITE_TAC[POLY_OF_WORD_XOR];
      MATCH_MP_TAC MOD_POLYVAL_REFL_GEN THEN
      SIMP_TAC[RING_MUL; RING_ADD; BOOL_POLY_OF_WORD] THEN
      MATCH_MP_TAC(GSYM RING_ADD_RDISTRIB) THEN REWRITE_TAC[BOOL_POLY_OF_WORD]];
    ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
    MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
    EXISTS_TAC
      `ring_add bool_poly
        (ring_mul bool_poly (ring_add bool_poly (poly_of_word (a:int128)) (poly_of_word (b:int128))) (poly_of_word (polyval_dot (h:int128) h)))
        (ring_mul bool_poly (poly_of_word (c:int128)) (poly_of_word h))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`word_xor (word_pmul (word_xor (a:int128) (b:int128)) (polyval_dot (h:int128) h) : 256 word) (word_pmul (c:int128) h : 256 word)`] POLYVAL_REDUCE_PROP3_CORRECT) THEN REWRITE_TAC[POLY_OF_WORD_XOR; POLY_OF_WORD_PMUL_2N];
      MP_TAC(ISPECL
        [`ring_mul bool_poly (ring_add bool_poly (poly_of_word (a:int128)) (poly_of_word (b:int128))) (poly_of_word (polyval_dot (h:int128) h))`;
         `ring_mul bool_poly (poly_of_word (polyval_dot (word_xor (a:int128) (b:int128)) (h:int128))) (poly_of_word h)`;
         `ring_mul bool_poly (poly_of_word (c:int128)) (poly_of_word (h:int128))`;
         `ring_mul bool_poly (poly_of_word (c:int128)) (poly_of_word (h:int128))`] MOD_POLYVAL_ADD) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [REWRITE_TAC[INNER_CONG];
          REWRITE_TAC[MOD_POLYVAL_REFL; RING_MUL; BOOL_POLY_OF_WORD]];
        REWRITE_TAC[]] THEN
      SIMP_TAC[RING_MUL; BOOL_POLY_OF_WORD]]]);;

(* ========================================================================= *)
(* Proof strategy: coprimality route (no irreducibility needed).             *)
(*   gcd(Q,x)=1 from Q(0)=1, then gcd(Q,x^n)=1 by induction.              *)
(*   Cancel x^128 from both sides of congruences.                            *)
(*   Control associativity of intermediate expressions so MOD_POLYVAL_MUL    *)
(*   matches the right subterms (use left-associated ((a+b)*h)*h).           *)
(*   Use ISPECL+MP_TAC instead of MATCH_MP_TAC for (==) congruences          *)
(*   (MATCH_MP_TAC fails on higher-order matching with (==)).                *)

(* ========================================================================= *)
(* Iterated H power and batched wide sum definitions                         *)
(* ========================================================================= *)

let h_power = define
  `h_power (h:int128) 0 = h /\
   h_power h (SUC n) = polyval_dot (h_power h n) h`;;

let ghash_wide = define
  `(ghash_wide (h:int128) (n:num) ([]:(int128)list) = (word 0 : 256 word)) /\
   (ghash_wide h n (CONS (b:int128) rest) =
     word_xor (word_pmul b (h_power h n) : 256 word)
              (ghash_wide h (n - 1) rest))`;;

let WORD_XOR_0 = WORD_RULE `word_xor (x:N word) (word 0) = x`;;

(* ========================================================================= *)
(* Generalized inner congruence: dot(a,h) * H^k == a * H^{k+1} (mod Q)      *)
(* ========================================================================= *)

let LHS_ASSOC = prove(
  `!a h k. ring_mul bool_poly
    (ring_mul bool_poly (poly_of_word (polyval_dot (a:int128) (h:int128)))
                        (poly_of_word (h_power h k)))
    (ring_pow bool_poly (poly_var bool_ring one) 128) =
   ring_mul bool_poly
    (ring_mul bool_poly (poly_of_word (polyval_dot a h))
                        (ring_pow bool_poly (poly_var bool_ring one) 128))
    (poly_of_word (h_power h k))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC BOOL_POLY_MUL_COMM23 THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY]);;

let RHS_ASSOC = prove(
  `!a h k. ring_mul bool_poly
    (ring_mul bool_poly (poly_of_word (a:int128))
                        (poly_of_word (polyval_dot (h_power (h:int128) k) h)))
    (ring_pow bool_poly (poly_var bool_ring one) 128) =
   ring_mul bool_poly
    (poly_of_word a)
    (ring_mul bool_poly (poly_of_word (polyval_dot (h_power h k) h))
                        (ring_pow bool_poly (poly_var bool_ring one) 128))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC BOOL_POLY_MUL_ASSOC THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY; RING_MUL]);;

let MID_COMM = prove(
  `!(a:(1->num)->bool) b c.
    a IN ring_carrier bool_poly /\
    b IN ring_carrier bool_poly /\
    c IN ring_carrier bool_poly
    ==> ring_mul bool_poly a (ring_mul bool_poly b c) =
        ring_mul bool_poly (ring_mul bool_poly a c) b`,
  MESON_TAC[RING_MUL_ASSOC; RING_MUL_SYM; RING_MUL]);;

let INNER_CONG_GEN = prove(
  `!(h:int128) (a:int128) (k:num).
    (ring_mul bool_poly (poly_of_word(polyval_dot a h)) (poly_of_word(h_power h k)) ==
     ring_mul bool_poly (poly_of_word a) (poly_of_word(h_power h (SUC k))))
    mod_polyval`,
  REPEAT GEN_TAC THEN REWRITE_TAC[h_power] THEN
  MATCH_MP_TAC(ISPEC `128` MOD_POLYVAL_CANCEL_VARPOW_GEN) THEN
  SIMP_TAC[RING_MUL; BOOL_POLY_OF_WORD] THEN
  ONCE_REWRITE_TAC[LHS_ASSOC] THEN ONCE_REWRITE_TAC[RHS_ASSOC] THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC `ring_mul bool_poly
    (ring_mul bool_poly (poly_of_word (a:int128)) (poly_of_word (h:int128)))
    (poly_of_word (h_power h k))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`ring_mul bool_poly (poly_of_word (polyval_dot (a:int128) (h:int128))) (ring_pow bool_poly (poly_var bool_ring one) 128)`;
      `ring_mul bool_poly (poly_of_word (a:int128)) (poly_of_word (h:int128))`;
      `poly_of_word (h_power (h:int128) k)`;
      `poly_of_word (h_power (h:int128) k)`] MOD_POLYVAL_MUL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[POLYVAL_DOT_CORRECT];
        REWRITE_TAC[MOD_POLYVAL_REFL; BOOL_POLY_OF_WORD]];
      REWRITE_TAC[]];
    ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
    MP_TAC(ISPECL
     [`poly_of_word (a:int128)`;
      `poly_of_word (a:int128)`;
      `ring_mul bool_poly (poly_of_word (polyval_dot (h_power (h:int128) k) h)) (ring_pow bool_poly (poly_var bool_ring one) 128)`;
      `ring_mul bool_poly (poly_of_word (h_power (h:int128) k)) (poly_of_word h)`] MOD_POLYVAL_MUL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[MOD_POLYVAL_REFL; BOOL_POLY_OF_WORD];
        REWRITE_TAC[POLYVAL_DOT_CORRECT]];
      REWRITE_TAC[]] THEN
    SIMP_TAC[MID_COMM; BOOL_POLY_OF_WORD; RING_MUL]]);;

(* ========================================================================= *)
(* General n-block batched GHASH theorem (by list induction)                 *)
(* For any non-empty list bs:                                                *)
(*   ghash_polyval_acc h a (CONS b bs) =                                     *)
(*     prop3(pmul(a XOR b, h_power h (LENGTH bs))  XOR  ghash_wide h ... bs)        *)
(* This covers 2/4/8-block as special cases.                                 *)
(* ========================================================================= *)

let GHASH_POLYVAL_ACC_BATCHED = prove(
  `!(h:int128) (bs:(int128)list) (a:int128) (b:int128).
    ghash_polyval_acc h a (CONS b bs) =
    polyval_reduce_prop3(
      word_xor (word_pmul (word_xor a b) (h_power h (LENGTH bs)) : 256 word)
               (ghash_wide h (LENGTH bs - 1) bs))`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[ghash_polyval_acc; ghash_wide; LENGTH; h_power; WORD_XOR_0; polyval_dot; SUB_0];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[ghash_polyval_acc; LENGTH; ghash_wide; SUC_SUB1] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`polyval_dot (word_xor (a:int128) (b:int128)) (h:int128)`; `h':int128`]) THEN
    REWRITE_TAC[ghash_polyval_acc] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(ISPEC `128` MOD_POLYVAL_CANCEL_VARPOW) THEN
    MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
    EXISTS_TAC `poly_of_word(word_xor
      (word_pmul (word_xor (polyval_dot (word_xor (a:int128) (b:int128)) (h:int128)) (h':int128))
                 (h_power h (LENGTH (t:(int128)list))))
      (ghash_wide h (LENGTH t - 1) t) : 256 word)` THEN
    CONJ_TAC THENL [REWRITE_TAC[POLYVAL_REDUCE_PROP3_CORRECT]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
    MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
    EXISTS_TAC `poly_of_word(word_xor
      (word_pmul (word_xor (a:int128) (b:int128)) (h_power (h:int128) (SUC (LENGTH (t:(int128)list)))))
      (word_xor (word_pmul (h':int128) (h_power h (LENGTH t)))
                (ghash_wide h (LENGTH t - 1) t)) : 256 word)` THEN
    CONJ_TAC THENL [REWRITE_TAC[POLYVAL_REDUCE_PROP3_CORRECT]; ALL_TAC] THEN
    REWRITE_TAC[POLY_OF_WORD_XOR; POLY_OF_WORD_PMUL_2N] THEN
    MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
    EXISTS_TAC `ring_add bool_poly
      (ring_mul bool_poly (poly_of_word (polyval_dot (word_xor (a:int128) (b:int128)) (h:int128)))
                          (poly_of_word (h_power h (LENGTH (t:(int128)list)))))
      (ring_add bool_poly
        (ring_mul bool_poly (poly_of_word (h':int128)) (poly_of_word (h_power h (LENGTH t))))
        (poly_of_word (ghash_wide h (LENGTH t - 1) t)))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`ring_mul bool_poly (ring_add bool_poly (poly_of_word (a:int128)) (poly_of_word (b:int128))) (poly_of_word (h_power (h:int128) (SUC (LENGTH (t:(int128)list)))))`;
        `ring_mul bool_poly (poly_of_word (polyval_dot (word_xor (a:int128) (b:int128)) (h:int128))) (poly_of_word (h_power h (LENGTH (t:(int128)list))))`;
        `ring_add bool_poly (ring_mul bool_poly (poly_of_word (h':int128)) (poly_of_word (h_power (h:int128) (LENGTH (t:(int128)list))))) (poly_of_word (ghash_wide h (LENGTH t - 1) t))`;
        `ring_add bool_poly (ring_mul bool_poly (poly_of_word (h':int128)) (poly_of_word (h_power (h:int128) (LENGTH (t:(int128)list))))) (poly_of_word (ghash_wide h (LENGTH t - 1) t))`] MOD_POLYVAL_ADD) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
          REWRITE_TAC[GSYM POLY_OF_WORD_XOR; GSYM h_power; INNER_CONG_GEN];
          REWRITE_TAC[MOD_POLYVAL_REFL; RING_ADD; RING_MUL; BOOL_POLY_OF_WORD]];
        REWRITE_TAC[]] THEN
      SIMP_TAC[RING_ADD; RING_MUL; BOOL_POLY_OF_WORD];
      MATCH_MP_TAC MOD_POLYVAL_REFL_GEN THEN
      SIMP_TAC[RING_ADD; RING_MUL; BOOL_POLY_OF_WORD] THEN
      SUBGOAL_THEN
        `ring_mul bool_poly
          (ring_add bool_poly (poly_of_word (polyval_dot (word_xor (a:int128) (b:int128)) (h:int128)))
                              (poly_of_word (h':int128)))
          (poly_of_word (h_power h (LENGTH (t:(int128)list)))) =
         ring_add bool_poly
          (ring_mul bool_poly (poly_of_word (polyval_dot (word_xor a b) h))
                              (poly_of_word (h_power h (LENGTH t))))
          (ring_mul bool_poly (poly_of_word h')
                              (poly_of_word (h_power h (LENGTH t))))`
      SUBST1_TAC THENL
       [MP_TAC(ISPECL [`bool_poly`; `poly_of_word (polyval_dot (word_xor (a:int128) (b:int128)) (h:int128))`; `poly_of_word (h':int128)`; `poly_of_word (h_power (h:int128) (LENGTH (t:(int128)list)))`] RING_ADD_RDISTRIB) THEN
        SIMP_TAC[BOOL_POLY_OF_WORD];
        MESON_TAC[RING_ADD_ASSOC; RING_ADD; RING_MUL; BOOL_POLY_OF_WORD]]]]);;

(* ========================================================================= *)
(* Htable precondition and Karatsuba middle term                             *)
(* ========================================================================= *)

let karatsuba_mid = new_definition
  `karatsuba_mid (h:int128) : 64 word =
   word_xor (word_subword h (0,64) : 64 word)
            (word_subword h (64,64) : 64 word)`;;

let htable_powers = new_definition
  `htable_powers (h:int128) (powers:(int128)list) (n:num) <=>
   LENGTH powers = n /\
   !k. k < n ==> EL k powers = h_power h k`;;

let GHASH_BATCHED_FROM_HTABLE = prove(
  `!(h:int128) (a:int128) (b:int128) (bs:(int128)list) (powers:(int128)list).
    htable_powers h powers (SUC(LENGTH bs))
    ==> ghash_polyval_acc h a (CONS b bs) =
        polyval_reduce_prop3(
          word_xor (word_pmul (word_xor a b) (EL (LENGTH bs) powers) : 256 word)
                   (ghash_wide h (LENGTH bs - 1) bs))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[htable_powers]) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `EL (LENGTH (bs:(int128)list)) powers = h_power (h:int128) (LENGTH bs)` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    REWRITE_TAC[GHASH_POLYVAL_ACC_BATCHED]]);;

(* ========================================================================= *)
(* Memory-level Htable predicate matching H table initialization output layout          *)
(* 12 x 128-bit entries (192 bytes) for H^1..H^8 with Karatsuba middle terms*)
(* Layout: groups of 3 entries [H^{2k+1}, pack(mid,mid), H^{2k+2}]          *)
(* ========================================================================= *)

let byteswap128 = new_definition
  `byteswap128 (x:int128) : int128 =
   word_join (word_subword x (0,64) : 64 word)
             (word_subword x (64,64) : 64 word)`;;

let htable_mem = new_definition
  `htable_mem (h:int128) (ptr:int64) (s:armstate) <=>
   read (memory :> bytes128 ptr) s = byteswap128(h_power h 0) /\
   read (memory :> bytes128 (word_add ptr (word 16))) s =
     word_join (karatsuba_mid(h_power h 0) : 64 word)
               (karatsuba_mid(h_power h 1) : 64 word) /\
   read (memory :> bytes128 (word_add ptr (word 32))) s = byteswap128(h_power h 1) /\
   read (memory :> bytes128 (word_add ptr (word 48))) s = byteswap128(h_power h 2) /\
   read (memory :> bytes128 (word_add ptr (word 64))) s =
     word_join (karatsuba_mid(h_power h 2) : 64 word)
               (karatsuba_mid(h_power h 3) : 64 word) /\
   read (memory :> bytes128 (word_add ptr (word 80))) s = byteswap128(h_power h 3) /\
   read (memory :> bytes128 (word_add ptr (word 96))) s = byteswap128(h_power h 4) /\
   read (memory :> bytes128 (word_add ptr (word 112))) s =
     word_join (karatsuba_mid(h_power h 4) : 64 word)
               (karatsuba_mid(h_power h 5) : 64 word) /\
   read (memory :> bytes128 (word_add ptr (word 128))) s = byteswap128(h_power h 5) /\
   read (memory :> bytes128 (word_add ptr (word 144))) s = byteswap128(h_power h 6) /\
   read (memory :> bytes128 (word_add ptr (word 160))) s =
     word_join (karatsuba_mid(h_power h 6) : 64 word)
               (karatsuba_mid(h_power h 7) : 64 word) /\
   read (memory :> bytes128 (word_add ptr (word 176))) s = byteswap128(h_power h 7)`;;

(* ========================================================================= *)
(* The x-shift / twist: multiplication by x mod Q(x)                        *)
(* H table initialization computes H_twisted = x * H mod Q(x) via shift-left-by-1      *)
(* with conditional reduction by Q(x) - x^128 = 0xC2...01.                  *)
(* ========================================================================= *)

let POLYVAL_TWIST_CONST = new_definition
  `POLYVAL_TWIST_CONST : int128 = word 0xC2000000000000000000000000000001`;;

let ghash_twist = new_definition
  `ghash_twist (h:int128) : int128 =
   if bit 127 h
   then word_xor (word_shl h 1) POLYVAL_TWIST_CONST
   else word_shl h 1`;;

(* poly_of_word(word 2) = x (the polynomial variable) *)
let BIT_WORD_2_128 = prove(
  `!i. bit i (word 2 : int128) <=> i = 1`,
  GEN_TAC THEN
  ASM_CASES_TAC `i = 1` THEN ASM_REWRITE_TAC[] THENL
   [CONV_TAC(ONCE_DEPTH_CONV BIT_WORD_CONV) THEN REWRITE_TAC[];
    REWRITE_TAC[BIT_WORD] THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    ASM_CASES_TAC `i < 128` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `i = 0` THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      SUBGOAL_THEN `~ODD(2 DIV 2 EXP i)` (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `2 DIV 2 EXP i = 0` (fun th -> REWRITE_TAC[th; ODD]) THEN
      MP_TAC(SPECL [`2`; `2 EXP i`] DIV_LT) THEN ANTS_TAC THENL
       [TRANS_TAC LTE_TRANS `2 EXP 2` THEN CONJ_TAC THENL
         [CONV_TAC NUM_REDUCE_CONV;
          REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
        SIMP_TAC[]]]]);;

let POLY_OF_WORD_2 = prove(
  `poly_of_word(word 2 : int128) = poly_var bool_ring (one:1)`,
  SUBGOAL_THEN `word 2 : int128 = word_of_poly(poly_var bool_ring (one:1))`
    SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[word_of_poly; BIT_WORD_OF_BITS; IN_ELIM_THM; BIT_WORD_2_128] THEN
    REWRITE_TAC[poly_var; bool_poly; POLY_RING; BOOL_RING;
                monomial_1; monomial_var; coeff] THEN
    REWRITE_TAC[FUN_EQ_THM; FORALL_ONE_THM] THEN
    ASM_CASES_TAC `i = 1` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC POLY_OF_WORD_OF_POLY THEN
    REWRITE_TAC[POLY_VAR_BOOL_POLY] THEN
    REWRITE_TAC[POLY_DEG_VAR; BOOL_RING] THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    ARITH_TAC]);;

(* Q(x) = x^128 + TWIST_CONST (at 256 bits) *)
let POLYVAL_DECOMP = prove(
  `polyval_poly = ring_add bool_poly
    (poly_of_word(word(2 EXP 128) : 256 word))
    (poly_of_word(word 0xC2000000000000000000000000000001 : 256 word))`,
  MP_TAC(INST_TYPE [`:256`,`:N`] POLYVAL_POLY_OF_WORD) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM POLY_OF_WORD_XOR] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_REDUCE_CONV);;

(* GHASH_TWIST_CORRECT: the twist computes x * H mod Q(x).                  *)
(* Proof: decompose word_pmul h (word 2) = word_shl (word_zx h) 1 at 256    *)
(* bits, show ghash_twist = polyval_reduce_step of that via bit-level        *)
(* reasoning, then use POLY_EQUIV_POLYVAL_REDUCE_STEP for the congruence.    *)

let WORD_PMUL_1 = REWRITE_RULE[WORD_SHL_ZERO; ARITH_RULE `2 EXP 0 = 1`]
  (ISPECL [`x:N word`; `0`] (CONJUNCT1 WORD_PMUL_POW2));;

let PMUL_2_AS_SHL = prove(
  `!h:int128. word_pmul h (word 2:int128) : 256 word =
              word_shl (word_zx h : 256 word) 1`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM(CONJUNCT2 WORD_PMUL_ZX)] THEN
  ONCE_REWRITE_TAC[GSYM(CONJUNCT1 WORD_PMUL_ZX)] THEN
  CONV_TAC(LAND_CONV(RAND_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
    (ISPECL [`word_zx(h:int128):256 word`; `1`] (CONJUNCT2 WORD_PMUL_POW2))]);;

let SUBWORD_SHL_ZX = prove(
  `!h:int128. word_zx(word_shl h 1) : 256 word =
              word_subword (word_shl (word_zx h : 256 word) 1) (0,128)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_ZX; BIT_WORD_SHL; BIT_WORD_SUBWORD; ADD_0; SUB_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let USHR_SHL_ZX_T = prove(
  `!h:int128. bit 127 h ==>
    word_ushr (word_shl (word_zx h : 256 word) 1) 128 : 256 word = word 1`,
  GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_SHL; BIT_WORD_ZX; BIT_WORD_1] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `bit ((k + 128) - 1) (h:int128) <=> F` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM(TAUT `~p <=> (p <=> F)`)] THEN
    ONCE_REWRITE_TAC[BIT_GUARD] THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    REWRITE_TAC[TAUT `~(p /\ q) <=> ~p \/ ~q`] THEN
    DISJ1_TAC THEN REWRITE_TAC[NOT_LT] THEN
    UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC]);;

let USHR_SHL_ZX_F = prove(
  `!h:int128. ~bit 127 h ==>
    word_ushr (word_shl (word_zx h : 256 word) 1) 128 : 256 word = word 0`,
  GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_SHL; BIT_WORD_ZX; BIT_WORD_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `bit ((k + 128) - 1) (h:int128) <=> F` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM(TAUT `~p <=> (p <=> F)`)] THEN
    ONCE_REWRITE_TAC[BIT_GUARD] THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    REWRITE_TAC[TAUT `~(p /\ q) <=> ~p \/ ~q`] THEN
    DISJ1_TAC THEN REWRITE_TAC[NOT_LT] THEN
    UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC]);;

let TWIST_WORD_IDENTITY = prove(
  `!h:int128.
    word_zx(ghash_twist h) : 256 word =
    polyval_reduce_step(word_shl (word_zx h : 256 word) 1)`,
  GEN_TAC THEN
  REWRITE_TAC[ghash_twist; POLYVAL_TWIST_CONST; polyval_reduce_step] THEN
  ASM_CASES_TAC `bit 127 (h:int128)` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPEC `h:int128` USHR_SHL_ZX_T) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[WORD_PMUL_1; WORD_ZX_XOR; SUBWORD_SHL_ZX] THEN
    CONV_TAC WORD_REDUCE_CONV;
    MP_TAC(SPEC `h:int128` USHR_SHL_ZX_F) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[CONJUNCT1 WORD_PMUL_0; WORD_XOR_0; SUBWORD_SHL_ZX]]);;

let GHASH_TWIST_CORRECT = prove(
  `!h:int128.
    (poly_of_word(ghash_twist h) ==
     ring_mul bool_poly (poly_var bool_ring one) (poly_of_word h)) (mod_polyval)`,
  GEN_TAC THEN
  SUBGOAL_THEN
    `poly_of_word(ghash_twist (h:int128)) =
     poly_of_word(polyval_reduce_step(word_pmul h (word 2:int128) : 256 word) : 256 word)`
    SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS `poly_of_word(word_zx(ghash_twist (h:int128)) : 256 word)` THEN
    CONJ_TAC THENL
     [SIMP_TAC[POLY_OF_WORD_ZX; DIMINDEX_128; DIMINDEX_256; ARITH_RULE `128 <= 256`];
      AP_TERM_TAC THEN REWRITE_TAC[TWIST_WORD_IDENTITY; PMUL_2_AS_SHL]];
    MP_TAC(ISPEC `word_pmul (h:int128) (word 2:int128) : 256 word`
                 POLY_EQUIV_POLYVAL_REDUCE_STEP) THEN
    REWRITE_TAC[POLY_OF_WORD_PMUL_2N] THEN
    SIMP_TAC[POLY_OF_WORD_ZX; DIMINDEX_128; DIMINDEX_256;
             ARITH_RULE `128 <= 256`] THEN
    REWRITE_TAC[POLY_OF_WORD_2] THEN
    ONCE_REWRITE_TAC[MESON[RING_MUL_SYM; BOOL_POLY_OF_WORD; POLY_VAR_BOOL_POLY]
      `ring_mul bool_poly (poly_of_word h) (poly_var bool_ring one) =
       ring_mul bool_poly (poly_var bool_ring one) (poly_of_word h)`] THEN
    REWRITE_TAC[]]);;
