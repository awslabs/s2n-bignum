(* ========================================================================= *)
(* GHASH specification and Horner unrolling lemma.                           *)
(*                                                                           *)
(* Defines the POLYVAL dot operation and GHASH Horner iteration in terms     *)
(* of polynomial arithmetic mod Q(x), then proves key algebraic lemmas       *)
(* needed for verifying the batched GHASH assembly (gcm_ghash_v8).           *)
(*                                                                           *)
(* Key definitions:                                                          *)
(*   polyval_dot a b    = prop3(pmul(a,b)) = a*b*x^{-128} mod Q(x)          *)
(*   ghash_polyval_acc h acc xs = Horner iteration (left fold)               *)
(*                                                                           *)
(* Key theorems:                                                             *)
(*   POLYVAL_DOT_CORRECT: dot(a,b)*x^128 ≡ a*b (mod Q)                      *)
(*   MOD_POLYVAL_WORD_EQ: congruent 128-bit words are equal                  *)
(*   GHASH_ACC_APPEND: left fold splits over APPEND                          *)
(* ========================================================================= *)

needs "common/karatsuba_pmul_proof.ml";;

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
(* Q(x) is nonzero (degree 128 ≠ degree 0).                                 *)
(* ------------------------------------------------------------------------- *)

let POLYVAL_POLY_NONZERO = prove
 (`~(polyval_poly = ring_0 bool_poly)`,
  REWRITE_TAC[BOOL_POLY_ZERO] THEN
  DISCH_THEN(MP_TAC o AP_TERM `poly_deg bool_ring:((1->num)->bool)->num`) THEN
  REWRITE_TAC[POLY_DEG_POLYVAL_POLY; bool_poly; POLY_RING; POLY_DEG_0] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* If Q(x) divides p and deg(p) < 128, then p = 0.                          *)
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

(* ------------------------------------------------------------------------- *)
(* The POLYVAL "dot" operation: dot(a,b) = a * b * x^{-128} mod Q(x).       *)
(* Defined computationally as prop3(pmul(a,b)).                              *)
(* ------------------------------------------------------------------------- *)

let polyval_dot = new_definition
 `polyval_dot (a:128 word) (b:128 word) : 128 word =
  polyval_reduce_prop3 (word_pmul a b : 256 word)`;;

(* dot(a,b) * x^128 ≡ a * b (mod Q(x)) *)
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

(* Step congruence: result * x^128 ≡ (acc + x) * H (mod Q) *)
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

(* ========================================================================= *)
(* Q(x) is irreducible — proved via Rabin test (session 3, 2026-03-31).      *)
(* The squaring chain x^(2^k) mod Q(x) for k=0..128 is computed using       *)
(* quotient-based verification: at each step, verify                          *)
(*   word_xor(y_k, w_{k+1}) = pmul(Q, q_k)                                  *)
(* using PMUL_Q_256_SYM. Quotients are precomputed in OCaml.                 *)
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
(* Squaring chain: x^(2^k) mod Q(x) for k = 0..128.                         *)
(* Built by repeated squaring with quotient-based reduction verification.    *)
(* Each step verifies word_xor(y_k, w_{k+1}) = pmul(Q, q_k) at word level.  *)
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

(* OCaml computation of the squaring chain and Rabin test data *)
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

(* Build the HOL Light squaring chain using quotient verification *)
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
(*   1. Q | (x^(2^128) - x)  [Fermat check]                                 *)
(*   2. gcd(Q, x^(2^64) - x) = 1  [coprimality via Bezout coefficients]     *)
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
(* This does NOT require irreducibility — only gcd(Q, x) = 1 (Q(0) = 1).   *)
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

(* General cancellation for arbitrary polynomials (not just poly_of_word) *)
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

(* Inner congruence: (a+b)*dot(h,h) ≡ dot(a⊕b,h)*h (mod Q) *)
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
(*   XOR of 256-bit polynomial multiplications followed by Prop 3 reduction  *)
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
(* PROGRESS (session 4, 2026-03-31):                                         *)
(*                                                                           *)
(* PROVEN (in addition to sessions 2-3):                                     *)
(*   MOD_POLYVAL_CANCEL_VARPOW_GEN (general cancellation for arbitrary polys)*)
(*   BOOL_POLY_MUL_ASSOC, BOOL_POLY_MUL_ASSOC_REV, BOOL_POLY_MUL_COMM23    *)
(*   COMM23_SPEC, ASSOC_SPEC, ASSOC_REV_SPEC (specific ring equalities)     *)
(*   INNER_CONG: (a+b)*dot(h,h) ≡ dot(a⊕b,h)*h (mod Q)                     *)
(*   *** GHASH_POLYVAL_ACC_2: 2-block Horner unrolling ***                   *)
(*                                                                           *)
(* KEY TECHNIQUE: coprimality route (no irreducibility needed).              *)
(*   gcd(Q,x)=1 from Q(0)=1, then gcd(Q,x^n)=1 by induction.              *)
(*   Cancel x^128 from both sides of congruences.                            *)
(*   Control associativity of intermediate expressions so MOD_POLYVAL_MUL    *)
(*   matches the right subterms (use left-associated ((a+b)*h)*h).           *)
(*   Use ISPECL+MP_TAC instead of MATCH_MP_TAC for (==) congruences          *)
(*   (MATCH_MP_TAC fails on higher-order matching with (==)).                *)
(*                                                                           *)
(* NEXT STEPS:                                                               *)
(*   1. Define Htable precondition and connect to ARM simulation             *)
(*   2. Start ARM simulation of gcm_ghash_v8                                 *)
(* ========================================================================= *)

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
(* Generalized inner congruence: dot(a,h) * H^k ≡ a * H^{k+1} (mod Q)      *)
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
(*     prop3(pmul(a⊕b, h_power h (LENGTH bs)) ⊕ ghash_wide h ... bs)        *)
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
(* PROGRESS (session 5):                                                     *)
(*   PROVEN: h_power, ghash_wide (defs), INNER_CONG_GEN, WORD_XOR_0,        *)
(*           LHS_ASSOC, RHS_ASSOC, MID_COMM,                                *)
(*           *** GHASH_POLYVAL_ACC_BATCHED: general n-block theorem ***       *)
(* ========================================================================= *)

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
(* Memory-level Htable predicate matching gcm_init_v8 output layout          *)
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
(* NEXT STEPS:                                                               *)
(*   1. Start ARM simulation of gcm_ghash_v8                                 *)
(*   2. Verify gcm_init_v8 establishes htable_mem (optional)                 *)
(* ========================================================================= *)

(* ========================================================================= *)
(* The x-shift / twist: multiplication by x mod Q(x)                        *)
(* gcm_init_v8 computes H_twisted = x * H mod Q(x) via shift-left-by-1      *)
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

(* ========================================================================= *)
(* PROGRESS (session 6):                                                     *)
(*   PROVEN: POLY_OF_WORD_2, BIT_WORD_2_128, POLYVAL_DECOMP,                *)
(*           PMUL_2_AS_SHL, SUBWORD_SHL_ZX, USHR_SHL_ZX_T/F,               *)
(*           TWIST_WORD_IDENTITY, GHASH_TWIST_CORRECT (no gaps!)             *)
(*   DEFINED: ghash_twist, POLYVAL_TWIST_CONST                               *)
(*                                                                           *)
(* NEXT STEPS:                                                               *)
(*   1. Start ARM simulation of gcm_ghash_v8                                 *)
(*   2. Verify gcm_init_v8 establishes htable_mem (optional)                 *)
(* ========================================================================= *)
