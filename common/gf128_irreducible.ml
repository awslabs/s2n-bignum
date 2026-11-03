(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Irreducibility over GF(2) of the GHASH polynomial                         *)
(*   P(x) = x^128 + x^7 + x^2 + x + 1                                        *)
(* (common/ghash.ml) and of the POLYVAL polynomial                           *)
(*   Q(x) = x^128 + x^127 + x^126 + x^121 + 1                                *)
(* (common/polyval.ml), by the Rabin test, so that the GHASH and POLYVAL     *)
(* arithmetic is that of the field GF(2^128).  No proof depends on these     *)
(* facts, so they are checked once, by arm/proofs/aes_gcm_spec_checks.ml,    *)
(* and not at every load of the GHASH and POLYVAL theories.                  *)
(* ========================================================================= *)

needs "Library/rabin_test.ml";;
needs "common/polyval.ml";;

(* ------------------------------------------------------------------------- *)
(* A faster numeral conversion for word_pmul than Library/words.ml's         *)
(* WORD_PMUL_CONV, used by the two squaring chains below.                    *)
(*                                                                           *)
(* WORD_PMUL_CONV consumes the first operand with word_ushr, but its only    *)
(* base case tests whether the second operand is zero. In these chains the   *)
(* first operand is a 128-bit word and the second is zero-extended to 256    *)
(* bits, so the first can become zero well before the second has been        *)
(* shifted out. Testing both zero cases avoids the remaining recursive       *)
(* steps, and simplifying a zero xor avoids an unnecessary numeral           *)
(* conversion.                                                               *)
(* ------------------------------------------------------------------------- *)

let WORD_PMUL_NUM_CONV =
  let in_conv =
    GEN_REWRITE_CONV I [GSYM(CONJUNCT2 WORD_PMUL_ZX)] THENC
    RAND_CONV WORD_ZX_CONV
  and base_conv =
    GEN_REWRITE_CONV I [CONJUNCT1 WORD_PMUL_0; CONJUNCT2 WORD_PMUL_0]
  and step_conv =
    GEN_REWRITE_CONV I [WORD_PMUL_STEP] THENC
    BINOP2_CONV
     (RATOR_CONV(LAND_CONV BIT_WORD_CONV) THENC
      GEN_REWRITE_CONV I [COND_CLAUSES])
     (BINOP2_CONV WORD_USHR_CONV WORD_SHL_CONV)
  and xor_conv =
    GEN_REWRITE_CONV I [WORD_XOR_0] ORELSEC WORD_XOR_CONV in
  let rec conv tm =
    try base_conv tm with Failure _ ->
    (step_conv THENC RAND_CONV conv THENC xor_conv) tm in
  let fullconv = in_conv THENC conv in
  fun tm ->
    match tm with
      Comb(Comb(Const("word_pmul",_),
                Comb(Const("word",_),m)),
            Comb(Const("word",_),n))
      when is_numeral m && is_numeral n -> fullconv tm
  | _ -> failwith "WORD_PMUL_NUM_CONV";;

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
               (ONCE_DEPTH_CONV WORD_PMUL_NUM_CONV THENC
                (* GHASH_REDUCE1, not the ghash_reduce1 definition: the defn
                   leaves a `word_pmul _ (word 0x87)`, while GHASH_REDUCE1
                   states the same reduction as shifts and xors. *)
                REWRITE_CONV[ghash_reduce; GHASH_REDUCE1] THENC
                DEPTH_CONV(WORD_PMUL_NUM_CONV ORELSEC WORD_RED_CONV)))) th1 in
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

let RING_IRREDUCIBLE_GHASH_POLYNOMIAL = prove
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
      (* WORD_PMUL_NUM_CONV stops when the 128-bit first operand becomes zero,
         instead of continuing until the widened second operand shifts out. *)
      let sq_th'' = CONV_RULE(rhs_conv(RAND_CONV WORD_PMUL_NUM_CONV)) sq_th' in
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
    ASM_SIMP_TAC[BEZOUT_RING_COPRIME; BEZOUT_BOOL_POLY] THEN
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
