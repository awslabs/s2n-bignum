(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Equivalence of the NTT part of the generated FIPS 204 specification       *)
(* (common/fips204/generated/fips204_generated.ml) with                      *)
(* common/fips204/fips204.ml: BitRev8, NTT and NTTInv (FIPS 204 Algorithms   *)
(* 41 and 42) and the NTT-domain arithmetic on one polynomial. The vector    *)
(* and matrix functions are in ntt_vec.ml.                                   *)
(*                                                                           *)
(* Proved: EQ_BITREV8, EQ_NTT, EQ_NTT_RQ, EQ_NTTINV (NTTInv_hol of a reduced *)
(* array a is the handwritten mldsa_ntt_inv a), EQ_ADDNTT, EQ_MULTIPLYNTT,   *)
(* EQ_INTPOLYTORQ.                                                           *)
(*                                                                           *)
(* Load after base.ml and common.ml.                                   *)
(* ========================================================================= *)

needs "common/fips204/generated/core/common.ml";;
needs "common/fips204/generated/core/core.ml";;

(* ------------------------------------------------------------------------- *)
(* Generic facts about the generated monad (local versions).                 *)
(* ------------------------------------------------------------------------- *)


let NTT_MAP_OPTION_SOME = prove
 (`!(f:A->B) x. isa_map_option f (SOME x) = SOME (f x)`,
  REWRITE_TAC[isa_map_option]);;

let NTT_CONTINUE_BIND_CONTINUE = prove
 (`!(s:S) (rest:S->((S,R)statement_outcome)native_result).
     native_continue_bind (Value (Continue s)) rest = rest s`,
  REWRITE_TAC[native_continue_bind_DEF; case_native_result_DEF;
              case_statement_outcome_DEF]);;

let NTT_FINISH_CONTINUE = prove
 (`!(s:S) (rd:S->(R)native_result).
     native_finish (Value (Continue s)) rd = rd s`,
  REWRITE_TAC[native_finish_DEF; case_native_result_DEF;
              case_statement_outcome_DEF]);;

let NTT_ISA_INT_MOD_Q = prove
 (`!x. isa_int_mod x (&8380417) = x rem &8380417`,
  REWRITE_TAC[isa_int_mod] THEN CONV_TAC INT_REDUCE_CONV);;

let NTT_POW_MOD_NUM = prove
 (`!a n. typed_hol_pow_mod a (&n) (&8380417) =
         Value ((a pow n) rem &8380417)`,
  REWRITE_TAC[typed_hol_pow_mod_DEF; NTT_ISA_INT_MOD_Q; ISA_NAT_NUM] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[INT_ARITH `~(&n:int < &0)`]);;

(* The rewrites of the monad on values, used for evaluating loop bodies.     *)

let NTT_MONAD_RULES =
  [NATIVE_BIND_VALUE; TYPED_HOL_READ_SOME; TYPED_HOL_SLOT_READ_ASSIGNED; ISA_NAT_NUM;
   TYPED_HOL_NONNEGATIVE_NUM; NTT_MAP_OPTION_SOME; NTT_CONTINUE_BIND_CONTINUE;
   NTT_FINISH_CONTINUE; TYPED_HOL_INT_POW_NUM; NTT_POW_MOD_NUM; NTT_ISA_INT_MOD_Q;
   typed_hol_nominal_update_DEF; typed_hol_bit_value_DEF;
   case_native_result_DEF; map_native_result_DEF; map_statement_outcome_DEF;
   native_seq_DEF; UNCURRY_DEF; I_THM;
   fips204_poly_SEL_CTR; common_vec_SEL_CTR; fips204_intpoly_coefficients_DEF;
   fips204_zq_residue_DEF; common_mat_entries_DEF; fips_matrix_SEL_CTR];;

(* ------------------------------------------------------------------------- *)
(* Residues mod q and the lifts lift_zq and lift_poly of common.ml.          *)
(* ------------------------------------------------------------------------- *)


let NTT_RESIDUE_REP = prove
 (`!x. &(residue_rep (residue_of_int_mod x:(8380417)residue)) =
       x rem &8380417`,
  GEN_TAC THEN
  REWRITE_TAC[residue_of_int_mod_DEF; residue_SEL_CTR; DIMINDEX_Q;
              NTT_ISA_INT_MOD_Q] THEN
  MATCH_MP_TAC(CONJUNCT1 ISA_NAT) THEN
  REWRITE_TAC[INT_REM_POS_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let NTT_RESIDUE_EQ = prove
 (`!x y. (residue_of_int_mod x:(8380417)residue) = residue_of_int_mod y <=>
         (x == y) (mod &8380417)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_REM_EQ; GSYM NTT_RESIDUE_REP] THEN
  REWRITE_TAC[INT_OF_NUM_EQ] THEN
  MESON_TAC[residue_SEL_CTR; residue_CTR_SEL]);;

let NTT_LIFT_ZQ_EQ = prove
 (`!x y. lift_zq x = lift_zq y <=> (x == y) (mod &8380417)`,
  REWRITE_TAC[lift_zq; injectivity "fips204_zq"; NTT_RESIDUE_EQ]);;

let NTT_FIPS204_ZQ = prove
 (`!x. FIPS204_Zq (residue_of_int_mod x) = lift_zq x`,
  REWRITE_TAC[lift_zq]);;

(* Normalize lift_zq e: the remainders mod q inside e are dropped.           *)

let NTT_LIFT_ZQ_CONV tm =
  match tm with
    Comb(Const("lift_zq",_),_) ->
      (REWR_CONV (GSYM LIFT_ZQ_REM) THENC
       RAND_CONV INT_REM_DOWN_CONV THENC
       TRY_CONV (REWR_CONV LIFT_ZQ_REM)) tm
  | _ -> failwith "NTT_LIFT_ZQ_CONV";;

let NTT_LIFT_POLY_EQ = prove
 (`!a b. (lift_poly a:(A)fips204_poly) = lift_poly b <=>
         !i. i < 256 ==> (a i == b i) (mod &8380417)`,
  REWRITE_TAC[lift_poly; fips204_poly_INJECT; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; NTT_LIFT_ZQ_EQ]);;

let NTT_LIFT_POLY_EQ_ALT = prove
 (`!a b. (!i. i < 256 ==> (a i == b i) (mod &8380417))
         ==> (lift_poly a:(A)fips204_poly) = lift_poly b`,
  REWRITE_TAC[NTT_LIFT_POLY_EQ]);;

let NTT_LIFT_POLY_REM = prove
 (`!a. (lift_poly (\i. a i rem &8380417):(A)fips204_poly) = lift_poly a`,
  REWRITE_TAC[NTT_LIFT_POLY_EQ; GSYM INT_REM_EQ; INT_REM_REM]);;
(* ------------------------------------------------------------------------- *)
(* The layers of FIPS 204 Algorithms 41 and 42 on integer arrays, without    *)
(* reduction mod q (the generated code reduces after each operation, which   *)
(* gives the same residues). Layer l = 0, ..., 7 of the NTT consists of 2^l  *)
(* blocks of 2 * len coefficients, len = 2^(7 - l); block b starts at        *)
(* 2 * len * b and uses zeta^BitRev8(2^l + b) (Algorithm 41, m = 2^l + b).   *)
(* Layer u = 0, ..., 7 of the inverse has len = 2^u and 2^(7 - u) blocks;    *)
(* block b uses -zeta^BitRev8(2^(8 - u) - 1 - b) (Algorithm 42).             *)
(* ------------------------------------------------------------------------- *)

let ntt_fwd_block = new_definition
 `ntt_fwd_block (z:int) start len (a:num->int) i =
    if start <= i /\ i < start + len then a i + z * a(i + len)
    else if start + len <= i /\ i < start + 2 * len then a(i - len) - z * a i
    else a i`;;

let ntt_fwd_blocks = define
 `ntt_fwd_blocks l 0 (a:num->int) = a /\
  ntt_fwd_blocks l (SUC b) a =
    ntt_fwd_block ((&1753 pow bitreverse8 (2 EXP l + b)) rem &8380417)
                  (2 * 2 EXP (7 - l) * b) (2 EXP (7 - l))
                  (ntt_fwd_blocks l b a)`;;

let ntt_fwd_layers = define
 `ntt_fwd_layers 0 (a:num->int) = a /\
  ntt_fwd_layers (SUC l) a = ntt_fwd_blocks l (2 EXP l) (ntt_fwd_layers l a)`;;

let ntt_inv_block = new_definition
 `ntt_inv_block (z:int) start len (a:num->int) i =
    if start <= i /\ i < start + len then a i + a(i + len)
    else if start + len <= i /\ i < start + 2 * len
    then z * (a(i - len) - a i)
    else a i`;;

let ntt_inv_blocks = define
 `ntt_inv_blocks u 0 (a:num->int) = a /\
  ntt_inv_blocks u (SUC b) a =
    ntt_inv_block ((--(&1753 pow bitreverse8 (2 EXP (8 - u) - 1 - b)))
                   rem &8380417)
                  (2 * 2 EXP u * b) (2 EXP u)
                  (ntt_inv_blocks u b a)`;;

let ntt_inv_layers = define
 `ntt_inv_layers 0 (a:num->int) = a /\
  ntt_inv_layers (SUC u) a =
    ntt_inv_blocks u (2 EXP (7 - u)) (ntt_inv_layers u a)`;;

(* ------------------------------------------------------------------------- *)
(* In each layer, coefficient i only depends on the block containing it.     *)
(* ------------------------------------------------------------------------- *)

let NTT_FWD_BLOCKS_LOCAL = prove
 (`!l b (a:num->int) i.
        ntt_fwd_blocks l b a i =
        if i < 2 * 2 EXP (7 - l) * b
        then ntt_fwd_block
               ((&1753 pow bitreverse8 (2 EXP l + i DIV (2 * 2 EXP (7 - l))))
                rem &8380417)
               (2 * 2 EXP (7 - l) * (i DIV (2 * 2 EXP (7 - l))))
               (2 EXP (7 - l)) a i
        else a i`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ntt_fwd_blocks; MULT_CLAUSES; CONJUNCT1 LT] THEN
  MAP_EVERY X_GEN_TAC [`a:num->int`; `i:num`] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SPEC `a:num->int`) THEN
  ABBREV_TAC `L = 2 EXP (7 - l)` THEN
  SUBGOAL_THEN `~(L = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  ASM_CASES_TAC `i < 2 * L * b` THENL
   [GEN_REWRITE_TAC LAND_CONV [ntt_fwd_block] THEN
    SUBGOAL_THEN `~(2 * L * b <= i)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(2 * L * b + L <= i)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `i < 2 * (L + L * b)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `i < 2 * (L + L * b)` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `i DIV (2 * L) = b` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i - 2 * L * b` THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ntt_fwd_block] THEN
    SUBGOAL_THEN `2 * L * b <= i` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `i < 2 * L * b + L` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `~(i + L < 2 * L * b)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      SUBGOAL_THEN `2 * L * b + L <= i /\ i < 2 * L * b + 2 * L`
       (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(i - L < 2 * L * b)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC];
    GEN_REWRITE_TAC LAND_CONV [ntt_fwd_block] THEN
    SUBGOAL_THEN `~(2 * L * b <= i /\ i < 2 * L * b + L) /\
                  ~(2 * L * b + L <= i /\ i < 2 * L * b + 2 * L)`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

let NTT_INV_BLOCKS_LOCAL = prove
 (`!m b (a:num->int) i.
        ntt_inv_blocks m b a i =
        if i < 2 * 2 EXP m * b
        then ntt_inv_block
               ((--(&1753 pow
                    bitreverse8 (2 EXP (8 - m) - 1 - i DIV (2 * 2 EXP m))))
                rem &8380417)
               (2 * 2 EXP m * (i DIV (2 * 2 EXP m)))
               (2 EXP m) a i
        else a i`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ntt_inv_blocks; MULT_CLAUSES; CONJUNCT1 LT] THEN
  MAP_EVERY X_GEN_TAC [`a:num->int`; `i:num`] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SPEC `a:num->int`) THEN
  ABBREV_TAC `L = 2 EXP m` THEN
  SUBGOAL_THEN `~(L = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  ASM_CASES_TAC `i < 2 * L * b` THENL
   [GEN_REWRITE_TAC LAND_CONV [ntt_inv_block] THEN
    SUBGOAL_THEN `~(2 * L * b <= i)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(2 * L * b + L <= i)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `i < 2 * (L + L * b)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `i < 2 * (L + L * b)` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `i DIV (2 * L) = b` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i - 2 * L * b` THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ntt_inv_block] THEN
    SUBGOAL_THEN `2 * L * b <= i` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `i < 2 * L * b + L` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `~(i + L < 2 * L * b)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      SUBGOAL_THEN `2 * L * b + L <= i /\ i < 2 * L * b + 2 * L`
       (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(i - L < 2 * L * b)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC];
    GEN_REWRITE_TAC LAND_CONV [ntt_inv_block] THEN
    SUBGOAL_THEN `~(2 * L * b <= i /\ i < 2 * L * b + L) /\
                  ~(2 * L * b + L <= i /\ i < 2 * L * b + 2 * L)`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Powers of zeta = 1753 mod q: zeta^512 = 1 and zeta^256 = -1, and the      *)
(* exponent facts about BitRev8 used in the layers, checked for all layers   *)
(* and blocks.                                                               *)
(* ------------------------------------------------------------------------- *)

let NTT_ZETA_512 = prove
 (`(&1753 pow 512 == &1:int) (mod &8380417)`,
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let NTT_ZETA_256 = prove
 (`(&1753 pow 256 == -- &1:int) (mod &8380417)`,
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let NTT_ZETA_EXP_MOD = prove
 (`!e1 e2. e1 MOD 512 = e2 MOD 512
           ==> ((&1753:int) pow e1 == &1753 pow e2) (mod &8380417)`,
  SUBGOAL_THEN
   `!e. (&1753:int) pow e = (&1753 pow 512) pow (e DIV 512) *
                            &1753 pow (e MOD 512)`
   (fun th -> ONCE_REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[INT_POW_POW; GSYM INT_POW_ADD] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(x:int == &1) (mod n) /\ (y == &1) (mod n)
    ==> (x * z == y * z) (mod n)`) THEN
  REWRITE_TAC[REWRITE_RULE[INT_POW_ONE]
               (MATCH_MP INT_CONG_POW NTT_ZETA_512)]);;

let NTT_ZETA_EXP_NEG = prove
 (`!e1 e2. e1 MOD 512 = (e2 + 256) MOD 512
           ==> ((&1753:int) pow e1 == --(&1753 pow e2)) (mod &8380417)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP NTT_ZETA_EXP_MOD) THEN
  REWRITE_TAC[INT_POW_ADD] THEN MP_TAC NTT_ZETA_256 THEN
  MATCH_ACCEPT_TAC(INTEGER_RULE
   `!a b c n:int. (c == -- &1) (mod n) ==> (a == b * c) (mod n)
                  ==> (a == --b) (mod n)`));;

let NTT_EXPAND_LAYERS_CONV =
  let eval = NUM_REDUCE_CONV THENC REWRITE_CONV[bitreverse8] THENC
             DEPTH_CONV BITMAP_CONV THENC NUM_REDUCE_CONV in
  EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
  DEPTH_CONV EXPAND_CASES_CONV THENC eval;;

let NTT_EXP_FACTS = prove
 (`!t. t < 8 ==> !c. c < 2 EXP t
         ==> ((2 * bitreverse8 ((2 * c) * 2 EXP (7 - t)) + 1) * 2 EXP (7 - t))
             MOD 512 = bitreverse8 (2 EXP t + c) MOD 512 /\
             ((2 * bitreverse8 ((2 * c + 1) * 2 EXP (7 - t)) + 1) *
              2 EXP (7 - t)) MOD 512 =
             (bitreverse8 (2 EXP t + c) + 256) MOD 512 /\
             (2 * bitreverse8 (2 EXP t + c)) MOD 512 =
             ((2 * bitreverse8 (c * 2 EXP (8 - t)) + 1) * 2 EXP (8 - t))
             MOD 512 /\
             bitreverse8 (2 EXP t + c) + bitreverse8 (2 EXP (t + 1) - 1 - c) =
             256`,
  CONV_TAC NTT_EXPAND_LAYERS_CONV);;
(* ------------------------------------------------------------------------- *)
(* The forward layers as sums. After t layers, in block b (of size           *)
(* N = 2^(8 - t)) the coefficient r is the sum over s < 2^t of               *)
(* a(r + N * s) * W^s, where W = zeta^((2 * BitRev8(b * N) + 1) * N), i.e.   *)
(* the coefficient r of a mod (X^N - W). After 8 layers this is the NTT.     *)
(* ------------------------------------------------------------------------- *)

let NTT_ISUM_PAIR = prove
 (`!(f:num->int) m n.
        isum(2 * m..2 * n + 1) f = isum(m..n) (\i. f(2 * i) + f(2 * i + 1))`,
  REWRITE_TAC[INT_OF_REAL_THM SUM_PAIR]);;

let NTT_FWD_STEP_ALG = prove
 (`!K L (a:num->int) x y c W V r.
        1 <= K /\
        (x == isum (0..K - 1) (\s. a(r + 2 * L * s) * W pow s))
        (mod &8380417) /\
        (y == isum (0..K - 1) (\s. a((r + L) + 2 * L * s) * W pow s))
        (mod &8380417) /\
        (V == c) (mod &8380417) /\ (V pow 2 == W) (mod &8380417)
        ==> (x + c * y == isum (0..2 * K - 1) (\s. a(r + L * s) * V pow s))
            (mod &8380417)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 * K - 1 = 2 * (K - 1) + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM(SPEC `0` (CONJUNCT1 MULT_CLAUSES))] THEN
  SUBST1_TAC(ARITH_RULE `0 = 2 * 0`) THEN
  REWRITE_TAC[NTT_ISUM_PAIR] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!s1 s2. (x:int == s1) (mod n) /\ (y == s2) (mod n) /\
            (s == s1 + c * s2) (mod n)
            ==> (x + c * y == s) (mod n)`) THEN
  MAP_EVERY EXISTS_TAC
   [`isum (0..K - 1) (\s. (a:num->int)(r + 2 * L * s) * W pow s)`;
    `isum (0..K - 1) (\s. (a:num->int)((r + L) + 2 * L * s) * W pow s)`] THEN
  ASM_REWRITE_TAC[GSYM ISUM_LMUL; GSYM ISUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC INT_CONG_ISUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `r + L * 2 * i = r + 2 * L * i`;
              ARITH_RULE `r + L * (2 * i + 1) = (r + L) + 2 * L * i`] THEN
  REWRITE_TAC[INT_POW_ADD; INT_POW_1; GSYM INT_POW_POW] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP INT_CONG_POW) THEN
  UNDISCH_TAC `(V:int == c) (mod &8380417)` THEN
  MATCH_ACCEPT_TAC(INTEGER_RULE
   `!V c P Q a1 a2 n:int.
        (V == c) (mod n) ==> (P == Q) (mod n)
        ==> (a1 * P + a2 * P * V == a1 * Q + c * a2 * Q) (mod n)`));;

let NTT_MOD512_DOUBLE = prove
 (`!x y z. x MOD 512 = y MOD 512 /\ (2 * y) MOD 512 = z MOD 512
           ==> (x * 2) MOD 512 = z MOD 512`,
  REWRITE_TAC[GSYM CONG] THEN
  MP_TAC(SPEC `512` (NUMBER_RULE
   `!n x y z. (x == y) (mod n) /\ (2 * y == z) (mod n)
              ==> (x * 2 == z) (mod n)`)) THEN
  REWRITE_TAC[]);;

let NTT_MOD512_DOUBLE_NEG = prove
 (`!x y z. x MOD 512 = (y + 256) MOD 512 /\ (2 * y) MOD 512 = z MOD 512
           ==> (x * 2) MOD 512 = z MOD 512`,
  REWRITE_TAC[GSYM CONG] THEN
  MP_TAC(SPECL [`256`; `512`] (NUMBER_RULE
   `!k n x y z. 2 * k = n /\ (x == y + k) (mod n) /\ (2 * y == z) (mod n)
                ==> (x * 2 == z) (mod n)`)) THEN
  REWRITE_TAC[ARITH]);;

let NTT_CONG_NEG_REM = prove
 (`!x y n. (x == --(y rem n)) (mod n) <=> (x == --y) (mod n)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(INTEGER_RULE
   `!u y x n:int. (u == y) (mod n)
                  ==> ((x == --u) (mod n) <=> (x == --y) (mod n))`) THEN
  REWRITE_TAC[INT_CONG_LREM; INTEGER_RULE `(x:int == x) (mod n)`]);;

let NTT_FWD_SUM = prove
 (`!a t. t <= 8
         ==> !b r. b < 2 EXP t /\ r < 2 EXP (8 - t)
                   ==> (ntt_fwd_layers t a (2 EXP (8 - t) * b + r) ==
                        isum (0..2 EXP t - 1)
                         (\s. a (r + 2 EXP (8 - t) * s) *
                              (&1753 pow ((2 * bitreverse8 (b * 2 EXP (8 - t))
                                           + 1) * 2 EXP (8 - t))) pow s))
                       (mod &8380417)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ntt_fwd_layers; ARITH_RULE `b < 1 <=> b = 0`] THEN
    SIMP_TAC[ISUM_SING_NUMSEG; INT_POW; MULT_CLAUSES; ADD_CLAUSES;
             INT_MUL_RID] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[INTEGER_RULE `(x:int == x) (mod n)`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `t < 8` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `L = 2 EXP (7 - t)` THEN
  SUBGOAL_THEN `2 EXP (8 - SUC t) = L /\ 2 EXP (8 - t) = 2 * L /\
                2 EXP (SUC t) = 2 * 2 EXP t /\ 1 <= 2 EXP t /\
                2 * L * 2 EXP t = 256`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    SUBGOAL_THEN `8 - SUC t = 7 - t /\ 8 - t = SUC(7 - t)`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXP; ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; GSYM EXP_ADD] THEN
    SUBGOAL_THEN `7 - t + t = 7` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`b:num`; `r:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[ntt_fwd_layers] THEN
  ONCE_REWRITE_TAC[NTT_FWD_BLOCKS_LOCAL] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `L * b + r < 256` (fun th -> REWRITE_TAC[th]) THENL
   [SUBGOAL_THEN `L * b + r < L * (2 * 2 EXP t)` MP_TAC THENL
     [TRANS_TAC LTE_TRANS `L * (b + 1)` THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[ARITH_RULE `L * 2 * k = 2 * L * k`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(L = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  DISJ_CASES_THEN (X_CHOOSE_THEN `c:num` SUBST_ALL_TAC)
   (SPEC `b:num` (REWRITE_RULE[EVEN_EXISTS; ODD_EXISTS; ADD1] EVEN_OR_ODD))
  THENL
   [SUBGOAL_THEN `(L * 2 * c + r) DIV (2 * L) = c` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r:num` THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ntt_fwd_block] THEN
    SUBGOAL_THEN `2 * L * c <= L * 2 * c + r /\ L * 2 * c + r < 2 * L * c + L`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `c < 2 EXP t` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`t:num`] NTT_EXP_FACTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `c:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC NTT_FWD_STEP_ALG THEN
    EXISTS_TAC `(&1753:int) pow ((2 * bitreverse8 (c * 2 * L) + 1) * 2 * L)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`c:num`; `r:num`] o
                  check (is_forall o concl)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM MULT_ASSOC; ARITH_RULE `L * 2 * c = 2 * L * c`];
      FIRST_ASSUM(MP_TAC o SPECL [`c:num`; `r + L:num`] o
                  check (is_forall o concl)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM MULT_ASSOC;
                  ARITH_RULE `(L * 2 * c + r) + L = 2 * L * c + r + L`];
      REWRITE_TAC[INT_CONG_RREM] THEN MATCH_MP_TAC NTT_ZETA_EXP_MOD THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[INT_POW_POW] THEN MATCH_MP_TAC NTT_ZETA_EXP_MOD THEN
      MATCH_MP_TAC NTT_MOD512_DOUBLE THEN
      EXISTS_TAC `bitreverse8 (2 EXP t + c)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(L * (2 * c + 1) + r) DIV (2 * L) = c` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `L + r:num` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ntt_fwd_block] THEN
  SUBGOAL_THEN `~(2 * L * c <= L * (2 * c + 1) + r /\
                  L * (2 * c + 1) + r < 2 * L * c + L) /\
                2 * L * c + L <= L * (2 * c + 1) + r /\
                L * (2 * c + 1) + r < 2 * L * c + 2 * L`
   (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c < 2 EXP t` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`t:num`] NTT_EXP_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `c:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REWRITE_TAC[INT_ARITH `x - z * y:int = x + --z * y`] THEN
  MATCH_MP_TAC NTT_FWD_STEP_ALG THEN
  EXISTS_TAC `(&1753:int) pow ((2 * bitreverse8 (c * 2 * L) + 1) * 2 * L)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`c:num`; `r:num`] o
                check (is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM MULT_ASSOC;
                ARITH_RULE `(L * (2 * c + 1) + r) - L = 2 * L * c + r`];
    FIRST_ASSUM(MP_TAC o SPECL [`c:num`; `r + L:num`] o
                check (is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM MULT_ASSOC;
                ARITH_RULE `L * (2 * c + 1) + r = 2 * L * c + r + L`];
    REWRITE_TAC[NTT_CONG_NEG_REM] THEN MATCH_MP_TAC NTT_ZETA_EXP_NEG THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[INT_POW_POW] THEN MATCH_MP_TAC NTT_ZETA_EXP_MOD THEN
    MATCH_MP_TAC NTT_MOD512_DOUBLE_NEG THEN
    EXISTS_TAC `bitreverse8 (2 EXP t + c)` THEN ASM_REWRITE_TAC[]]);;
(* ------------------------------------------------------------------------- *)
(* The forward layers compute mldsa_ntt (on the residues of the input).      *)
(* ------------------------------------------------------------------------- *)

let NTT_FWD_LAYERS_SUM = prove
 (`!a k. k < 256
         ==> (ntt_fwd_layers 8 a k ==
              isum (0..255)
               (\j. a j * &1753 pow ((2 * bitreverse8 k + 1) * j)))
             (mod &8380417)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num->int`; `8`] NTT_FWD_SUM) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(MP_TAC o SPECL [`k:num`; `0`]) THEN
  ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; INT_POW_POW]);;

let NTT_FWD_LAYERS_MLDSA_NTT = prove
 (`!a k. k < 256
         ==> (ntt_fwd_layers 8 a k == mldsa_ntt (mldsa_poly a) k)
             (mod &8380417)`,
  SIMP_TAC[MLDSA_NTT_MLDSA_POLY; INT_CONG_RREM; NTT_FWD_LAYERS_SUM]);;

let NTT_LIFT_FWD_LAYERS = prove
 (`!a. (lift_poly (ntt_fwd_layers 8 a):(A)fips204_poly) =
       lift_poly (mldsa_ntt (mldsa_poly a))`,
  SIMP_TAC[NTT_LIFT_POLY_EQ; NTT_FWD_LAYERS_MLDSA_NTT]);;

(* ------------------------------------------------------------------------- *)
(* Each inverse layer u undoes the forward layer 7 - u up to a factor 2,     *)
(* since the zetas of corresponding blocks are inverse mod q. So the         *)
(* inverse layers applied to the NTT give 256 times the input.               *)
(* ------------------------------------------------------------------------- *)

let NTT_INV_FWD_BLOCK = prove
 (`!z z' s L (x:num->int) i.
        (z * z' == &1) (mod &8380417) /\ s <= i /\ i < s + 2 * L
        ==> (ntt_inv_block z' s L (ntt_fwd_block z s L x) i == &2 * x i)
            (mod &8380417)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ntt_inv_block] THEN
  ASM_CASES_TAC `i < s + L` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ntt_fwd_block] THENL
   [SUBGOAL_THEN `~(i + L < s + L) /\ s + L <= i + L /\ i + L < s + 2 * L /\
                  (i + L) - L = i`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_ACCEPT_TAC(INTEGER_RULE
     `!a b z n:int. ((a + z * b) + (a - z * b) == &2 * a) (mod n)`);
    SUBGOAL_THEN `s + L <= i /\ s <= i - L /\ i - L < s + L /\
                  i - L + L = i`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z * z' == &1:int) (mod &8380417)` THEN
    MATCH_ACCEPT_TAC(INTEGER_RULE
     `!a b z z' n:int. (z * z' == &1) (mod n)
                       ==> (z' * ((a + z * b) - (a - z * b)) == &2 * b)
                           (mod n)`)]);;

let NTT_INV_BLOCK_LOCAL = prove
 (`!z s L (x:num->int) y i.
        (!j. s <= j /\ j < s + 2 * L ==> x j = y j) /\
        s <= i /\ i < s + 2 * L
        ==> ntt_inv_block z s L x i = ntt_inv_block z s L y i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ntt_inv_block] THEN
  SUBGOAL_THEN `(x:num->int) i = y i` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY(AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC) THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* Basic facts about the layer parameters.                                   *)

let NTT_LAYER_PARAMS = prove
 (`!u. u < 8
       ==> 7 - (7 - u) = u /\ 2 EXP (8 - u) = 2 * 2 EXP (7 - u) /\
           2 * 2 EXP u * 2 EXP (7 - u) = 256 /\ ~(2 EXP u = 0)`,
  REWRITE_TAC[IMP_CONJ] THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV);;

let NTT_LAYER_BLOCK = prove
 (`!u i. u < 8 /\ i < 256
         ==> i DIV (2 * 2 EXP u) < 2 EXP (7 - u) /\
             2 * 2 EXP u * i DIV (2 * 2 EXP u) <= i /\
             i < 2 * 2 EXP u * i DIV (2 * 2 EXP u) + 2 * 2 EXP u /\
             2 * 2 EXP u * i DIV (2 * 2 EXP u) + 2 * 2 EXP u <= 256`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NTT_LAYER_PARAMS) THEN
  ABBREV_TAC `L = 2 EXP u` THEN ABBREV_TAC `K = 2 EXP (7 - u)` THEN
  MP_TAC(SPECL [`i:num`; `2 * L`] DIVISION) THEN
  ASM_REWRITE_TAC[MULT_EQ_0; ARITH_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i DIV (2 * L) < K` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; MULT_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC LE_TRANS `2 * L * K` THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * L * q + 2 * L = 2 * L * (q + 1)`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let NTT_INV_FWD_LAYER = prove
 (`!u (x:num->int) i.
        u < 8 /\ i < 256
        ==> (ntt_inv_blocks u (2 EXP (7 - u))
              (ntt_fwd_blocks (7 - u) (2 EXP (7 - u)) x) i ==
             &2 * x i) (mod &8380417)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NTT_LAYER_PARAMS) THEN
  MP_TAC(SPECL [`u:num`; `i:num`] NTT_LAYER_BLOCK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[NTT_INV_BLOCKS_LOCAL] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = i DIV (2 * 2 EXP u)` THEN
  ABBREV_TAC `L = 2 EXP u` THEN
  MP_TAC(ISPECL
   [`(--(&1753 pow bitreverse8 (2 * 2 EXP (7 - u) - 1 - c))) rem &8380417`;
    `2 * L * c`; `L:num`;
    `ntt_fwd_blocks (7 - u) (2 EXP (7 - u)) (x:num->int)`;
    `ntt_fwd_block ((&1753 pow bitreverse8 (2 EXP (7 - u) + c)) rem &8380417)
                   (2 * L * c) L (x:num->int)`;
    `i:num`] NTT_INV_BLOCK_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[NTT_FWD_BLOCKS_LOCAL] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `j DIV (2 * L) = c` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `j - 2 * L * c` THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `j < 256` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC NTT_INV_FWD_BLOCK THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!a b z z' n:int. (z == a) (mod n) /\ (z' == --b) (mod n) /\
                     (a * b == -- &1) (mod n)
                     ==> (z * z' == &1) (mod n)`) THEN
  MAP_EVERY EXISTS_TAC
   [`(&1753:int) pow bitreverse8 (2 EXP (7 - u) + c)`;
    `(&1753:int) pow bitreverse8 (2 * 2 EXP (7 - u) - 1 - c)`] THEN
  REWRITE_TAC[INT_CONG_LREM; INTEGER_RULE `(x:int == x) (mod n)`] THEN
  REWRITE_TAC[GSYM INT_POW_ADD] THEN
  MP_TAC(SPEC `7 - u` NTT_EXP_FACTS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `c:num`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ADD1; EXP] THEN
  DISCH_THEN(SUBST1_TAC o last o CONJUNCTS) THEN
  REWRITE_TAC[NTT_ZETA_256]);;

(* An inverse layer is linear (on residues).                                 *)

let NTT_INV_LAYER_SCALE = prove
 (`!u (x:num->int) y c.
        u < 8 /\ (!i. i < 256 ==> (x i == c * y i) (mod &8380417))
        ==> !i. i < 256
                ==> (ntt_inv_blocks u (2 EXP (7 - u)) x i ==
                     c * ntt_inv_blocks u (2 EXP (7 - u)) y i)
                    (mod &8380417)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NTT_LAYER_PARAMS) THEN
  MP_TAC(SPECL [`u:num`; `i:num`] NTT_LAYER_BLOCK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[NTT_INV_BLOCKS_LOCAL] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c' = i DIV (2 * 2 EXP u)` THEN
  ABBREV_TAC `L = 2 EXP u` THEN
  REWRITE_TAC[ntt_inv_block] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THENL
   [MATCH_MP_TAC(INTEGER_RULE
     `!x1 x2 y1 y2 c n:int.
         (x1 == c * y1) (mod n) /\ (x2 == c * y2) (mod n)
         ==> (x1 + x2 == c * (y1 + y2)) (mod n)`);
    MATCH_MP_TAC(INTEGER_RULE
     `!x1 x2 y1 y2 c z n:int.
         (x1 == c * y1) (mod n) /\ (x2 == c * y2) (mod n)
         ==> (z * (x1 - x2) == c * z * (y1 - y2)) (mod n)`);
    ALL_TAC] THEN
  TRY CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* The inverse layers respect congruence mod q, and undo the NTT up to 256.  *)

let NTT_INV_LAYERS_SCALE = prove
 (`!u (x:num->int) y c.
        u <= 8 /\ (!i. i < 256 ==> (x i == c * y i) (mod &8380417))
        ==> !i. i < 256
                ==> (ntt_inv_layers u x i == c * ntt_inv_layers u y i)
                    (mod &8380417)`,
  INDUCT_TAC THEN REWRITE_TAC[ntt_inv_layers] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC NTT_INV_LAYER_SCALE THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let NTT_INV_LAYERS_CONG = prove
 (`!u (x:num->int) y.
        u <= 8 /\ (!i. i < 256 ==> (x i == y i) (mod &8380417))
        ==> !i. i < 256
                ==> (ntt_inv_layers u x i == ntt_inv_layers u y i)
                    (mod &8380417)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:num`; `x:num->int`; `y:num->int`; `&1:int`]
               NTT_INV_LAYERS_SCALE) THEN
  ASM_REWRITE_TAC[INT_MUL_LID]);;

let NTT_INV_FWD_LAYERS = prove
 (`!a u. u <= 8
         ==> !i. i < 256
                 ==> (ntt_inv_layers u (ntt_fwd_layers 8 a) i ==
                      &2 pow u * ntt_fwd_layers (8 - u) a i)
                     (mod &8380417)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ntt_inv_layers; SUB_0; INT_POW; INT_MUL_LID] THEN
    REWRITE_TAC[INTEGER_RULE `(x:int == x) (mod n)`];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[ntt_inv_layers] THEN
  REWRITE_TAC[INT_POW] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!y. (x:int == c * y) (mod n) /\ (y == &2 * z) (mod n)
        ==> (x == (&2 * c) * z) (mod n)`) THEN
  EXISTS_TAC `ntt_inv_blocks u (2 EXP (7 - u)) (ntt_fwd_layers (8 - u) a) i` THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`u:num`; `ntt_inv_layers u (ntt_fwd_layers 8 a)`;
                  `ntt_fwd_layers (8 - u) a`; `(&2:int) pow u`]
                 NTT_INV_LAYER_SCALE) THEN
    ASM_SIMP_TAC[ARITH_RULE `SUC u <= 8 ==> u < 8`];
    SUBGOAL_THEN `8 - u = SUC(8 - SUC u) /\ 8 - SUC u = 7 - u`
     (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ntt_fwd_layers] THEN
    MATCH_MP_TAC NTT_INV_FWD_LAYER THEN ASM_ARITH_TAC]);;

let NTT_INV_LAYERS_MLDSA_NTT_INV = prove
 (`!b i. (!k. k < 256 ==> &0 <= b k /\ b k < &8380417) /\ i < 256
         ==> (&8347681 * ntt_inv_layers 8 b i ==
              coeff i (mldsa_ntt_inv b)) (mod &8380417)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLDSA_NTT_INV) THEN
  ABBREV_TAC `f = mldsa_ntt_inv b` THEN
  MP_TAC(SPECL [`8`; `b:num->int`;
                `ntt_fwd_layers 8 (\j. coeff j (f:(1->num)->int))`]
               NTT_INV_LAYERS_CONG) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`\j. coeff j (f:(1->num)->int)`; `k:num`]
                 NTT_FWD_LAYERS_MLDSA_NTT) THEN
    ASM_SIMP_TAC[MLDSA_POLY_COEFF; ETA_AX] THEN
    MATCH_ACCEPT_TAC(INTEGER_RULE
     `!x y n:int. (x == y) (mod n) ==> (y == x) (mod n)`);
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL [`\j. coeff j (f:(1->num)->int)`; `8`] NTT_INV_FWD_LAYERS) THEN
  REWRITE_TAC[LE_REFL; SUB_REFL; ntt_fwd_layers] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!c k x y z n:int. (c * k == &1) (mod n)
                      ==> (y == k * z) (mod n) ==> (x == y) (mod n)
                          ==> (c * x == z) (mod n)`) THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;
(* ------------------------------------------------------------------------- *)
(* BitRev8 (FIPS 204 Algorithm 41's helper) is bitreverse8, by evaluation    *)
(* of the generated code for each of the 256 arguments.                      *)
(* ------------------------------------------------------------------------- *)

let NTT_SCHEDULE_NUMERAL_CONV tm =
  match tm with
    Comb(Comb(Comb(Comb(Const("native_schedule",_),n),_),_),_)
      when is_numeral n ->
      if dest_numeral n =/ num 0 then
        GEN_REWRITE_CONV I [CONJUNCT1 native_schedule_DEF] tm
      else
        (RATOR_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV num_CONV))) THENC
         GEN_REWRITE_CONV I [CONJUNCT2 native_schedule_DEF]) tm
  | _ -> failwith "NTT_SCHEDULE_NUMERAL_CONV";;

let NTT_ISA_LIST_UPDATE_CONV tm =
  match tm with
    Comb(Comb(Comb(Const("isa_list_update",_),l),i),_) when is_numeral i ->
      (GEN_REWRITE_CONV I [isa_list_update] THENC
       TRY_CONV(RATOR_CONV(LAND_CONV NUM_EQ_CONV) THENC
                REWRITE_CONV[] THENC
                TRY_CONV(RAND_CONV(LAND_CONV NUM_SUB_CONV)))) tm
  | _ -> failwith "NTT_ISA_LIST_UPDATE_CONV";;

let NTT_REPLICATE_CONV tm =
  match tm with
    Comb(Comb(Const("REPLICATE",_),n),_) when is_numeral n ->
      if dest_numeral n =/ num 0 then
        GEN_REWRITE_CONV I [CONJUNCT1 REPLICATE] tm
      else
        (LAND_CONV num_CONV THENC GEN_REWRITE_CONV I [CONJUNCT2 REPLICATE]) tm
  | _ -> failwith "NTT_REPLICATE_CONV";;

let NTT_REM2_BOUNDS = prove
 (`!x. (&0 <= x rem &2 /\ x rem &2 < &2) <=> T`,
  GEN_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(SPECL [`x:int`; `&2:int`] INT_DIVISION) THEN
  REWRITE_TAC[INT_ARITH `~(&2:int = &0)`] THEN
  CONV_TAC INT_ARITH);;

let NTT_EVAL_CONV =
  let aop_distinct = distinctness "aop" in
  let rules =
    NTT_MONAD_RULES @
    [native_foldl_DEF; native_list_index_DEF; native_list_update_DEF;
     typed_hol_list_slice_DEF; typed_hol_int_to_bit_DEF;
     typed_hol_int_arithmetic_DEF; arith_faults_DEF; int_op_DEF;
     case_aop_DEF; aop_distinct; isa_take; isa_drop; isa_nat;
     isa_int_mod; isa_int_div; LENGTH;
     NUM_OF_INT_OF_NUM; BitsToInteger_hol_DEF; IntegerToBits_8_hol_DEF;
     NTT_REM2_BOUNDS] @
    BitRev8_hol_emitted_state_SELECTORS @
    [BitRev8_hol_emitted_b_rev_update_EXT; BitRev8_hol_emitted_i_update_EXT] in
  let basic = GEN_REWRITE_CONV TOP_DEPTH_CONV rules in
  let step =
    basic THENC
    DEPTH_CONV(NTT_SCHEDULE_NUMERAL_CONV ORELSEC NTT_ISA_LIST_UPDATE_CONV
               ORELSEC NTT_REPLICATE_CONV ORELSEC EL_CONV
               ORELSEC NUM_RED_CONV ORELSEC INT_RED_CONV) THENC
    TOP_DEPTH_CONV let_CONV THENC
    TOP_DEPTH_CONV BETA_CONV in
  REPEATC(CHANGED_CONV step);;

(* The generated code is evaluated once for a symbolic n: the result is the  *)
(* sum over bits i of (bit i of n) * 2^(7-i), as nested ifs. Each of the 256 *)
(* cases then only has to reduce numerals.                                   *)
let NTT_BITREV8_GENERIC =
  (REWRITE_CONV[BitRev8_hol_DEF] THENC NTT_EVAL_CONV)
    `BitRev8_hol (&(n:num))`;;

let NTT_BITREV8_CASE k =
  let ktm = mk_small_numeral k in
  let th1 = CONV_RULE(RAND_CONV(RAND_CONV INT_REDUCE_CONV))
              (INST [ktm,`n:num`] NTT_BITREV8_GENERIC) in
  let th2 = (REWRITE_CONV[bitreverse8] THENC BITMAP_CONV)
              (mk_comb(`bitreverse8`, ktm)) in
  TRANS th1 (SYM(AP_TERM `Value:int->(int)native_result`
                         (AP_TERM `int_of_num` th2)));;

let EQ_BITREV8 = prove
 (`!n. n < 256 ==> BitRev8_hol (&n) = Value (&(bitreverse8 n))`,
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC(map NTT_BITREV8_CASE (0--255)));;
(* ------------------------------------------------------------------------- *)
(* Counted loops (local versions): schedules as list_of_seq, and loops by    *)
(* invariants or by an explicit sequence of states.                          *)
(* ------------------------------------------------------------------------- *)

let NTT_RESULT_VALUE_EQ = prove
 (`!x:A y. (?s'. Value x = Value s' /\ s' = y) <=> x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[injectivity "native_result"] THEN
  MESON_TAC[]);;

let NTT_SCHEDULE_256 = prove
 (`native_schedule 257 (\i. i < &256) (\i. i + &1) (&0:int) =
   list_of_seq (\k. &k) 256`,
  REWRITE_TAC[NATIVE_SCHEDULE_INT; INT_SUB_RZERO; ISA_NAT_NUM; INT_ADD_LID] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ETA_AX]);;

let NTT_SCHEDULE_STEP = prove
 (`!m n a d:int. &0 < d /\ m < n
             ==> native_schedule n (\s. s < a + &m * d) (\s. s + d) a =
                 list_of_seq (\k. a + &k * d) m`,
  INDUCT_TAC THEN GEN_TAC THEN
  (STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THENL
    [REWRITE_TAC[LT]; ALL_TAC]) THEN
  REWRITE_TAC[native_schedule_DEF; LT_SUC] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[INT_MUL_LZERO; INT_ADD_RID; INT_LT_REFL; LIST_OF_SEQ];
    ALL_TAC] THEN
  REWRITE_TAC[LIST_OF_SEQ; INT_MUL_LZERO; INT_ADD_RID] THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN
    MATCH_MP_TAC(INT_ARITH `&0 < y ==> (a:int) < a + y`) THEN
    MATCH_MP_TAC INT_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `m:num` INT_POS) THEN INT_ARITH_TAC] THEN
  REWRITE_TAC[CONS_11] THEN
  SUBGOAL_THEN `(\s. s < a + &(SUC m) * d) = (\s. s < (a + d) + &m * (d:int))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n':num`; `a + d:int`; `d:int`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC);;

let NTT_FOLDL_INV = prove
 (`!n (body:I->S->(S)native_result) f P s0.
     P 0 s0 /\
     (!k s. k < n /\ P k s ==> ?s'. body (f k) s = Value s' /\ P (SUC k) s')
     ==> ?s. native_foldl body (list_of_seq f n) s0 = Value s /\ P n s`,
  INDUCT_TAC THEN REWRITE_TAC[LIST_OF_SEQ; native_foldl_DEF] THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `s0:S` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`0`; `s0:S`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LT_0]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:S` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[NATIVE_BIND_VALUE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`body:I->S->(S)native_result`; `(f:num->I) o SUC`;
    `\k. (P:num->S->bool) (SUC k)`; `s1:S`]) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[LT_SUC]);;

let NTT_FOLD_INV = prove
 (`!n (body:I->S->((S,R)statement_outcome)native_result) f P s0.
     P 0 s0 /\
     (!k s. k < n /\ P k s
            ==> ?s'. body (f k) s = Value (Continue s') /\ P (SUC k) s')
     ==> ?s. native_fold body (list_of_seq f n) s0 = Value (Continue s) /\
             P n s`,
  INDUCT_TAC THEN REWRITE_TAC[LIST_OF_SEQ; native_fold_DEF] THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `s0:S` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`0`; `s0:S`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LT_0]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:S` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[native_seq_DEF; NTT_CONTINUE_BIND_CONTINUE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`body:I->S->((S,R)statement_outcome)native_result`; `(f:num->I) o SUC`;
    `\k. (P:num->S->bool) (SUC k)`; `s1:S`]) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[LT_SUC]);;

(* A loop over the 256 coefficients that sets coefficient k to g k.          *)

let NTT_POINTWISE_LOOP = prove
 (`!(body:int->S->(S)native_result) (C:(fips204_zq)list->S) g l0.
     LENGTH l0 = 256 /\
     (!k l. k < 256 /\ LENGTH l = 256
            ==> body (&k) (C l) = Value (C (isa_list_update l k (g k))))
     ==> native_foldl body (list_of_seq (\k. &k) 256) (C l0) =
         Value (C (list_of_seq g 256))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`256`; `body:int->S->(S)native_result`; `\k. &k:int`;
                 `\k s. s = (C:(fips204_zq)list->S)
                              (list_of_seq (\i. if i < k then g i
                                                 else EL i l0) 256)`;
                 `(C:(fips204_zq)list->S) l0`] NTT_FOLDL_INV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN
      ASM_REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
      SIMP_TAC[EL_LIST_OF_SEQ];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LENGTH_LIST_OF_SEQ] THEN
      REWRITE_TAC[NTT_RESULT_VALUE_EQ; ISA_LIST_UPDATE_LIST_OF_SEQ] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[LT] THEN
      ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LIST_OF_SEQ_EQ THEN SIMP_TAC[]]);;
(* ------------------------------------------------------------------------- *)
(* Loops over the 256 coefficients of a polynomial: AddNTT, MultiplyNTT      *)
(* (FIPS 204 Algorithms 44 and 45), IntPolyToRq and the copies at the start  *)
(* of NTT and NTTInv.                                                        *)
(* ------------------------------------------------------------------------- *)

let NTT_BODY_RULES =
  NTT_MONAD_RULES @
  [NATIVE_LIST_INDEX_NUM; NATIVE_LIST_UPDATE_NUM; LENGTH_LIST_OF_SEQ;
   EL_LIST_OF_SEQ; LIFT_ZQ_REP; NTT_FIPS204_ZQ;
   LENGTH_ISA_LIST_UPDATE; FIPS204_POLY_COEFFICIENTS_LIFT; LENGTH_MAP;
   LENGTH_REPLICATE];;

(* The step of a pointwise loop: the body evaluated at a symbolic index.     *)

let NTT_POINTWISE_STEP_TAC ths =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC(NTT_BODY_RULES @ ths) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC(NTT_BODY_RULES @ ths) THEN
  CONV_TAC(ONCE_DEPTH_CONV NTT_LIFT_ZQ_CONV) THEN
  REWRITE_TAC[];;

(* The whole loop, for a definition th whose result is lift_poly g.          *)

let NTT_POINTWISE_TAC defth ths =
  REWRITE_TAC[defth] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[NTT_SCHEDULE_256] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [lift_poly] THEN
  MATCH_MP_TAC NTT_POINTWISE_LOOP THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_REPLICATE; LENGTH_LIST_OF_SEQ] THEN
  NTT_POINTWISE_STEP_TAC ths;;

let EQ_ADDNTT = prove
 (`!a b. AddNTT_hol (lift_poly a) (lift_poly b) =
         Value (lift_poly (\i. a i + b i))`,
  REPEAT GEN_TAC THEN NTT_POINTWISE_TAC AddNTT_hol_DEF []);;

let EQ_MULTIPLYNTT = prove
 (`!a b. MultiplyNTT_hol (lift_poly a) (lift_poly b) =
         Value (lift_poly (\i. a i * b i))`,
  REPEAT GEN_TAC THEN NTT_POINTWISE_TAC MultiplyNTT_hol_DEF []);;

let EQ_INTPOLYTORQ = prove
 (`!a. IntPolyToRq_hol (lift_intpoly a) = Value (lift_poly a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lift_intpoly] THEN
  NTT_POINTWISE_TAC IntPolyToRq_hol_DEF []);;
(* ------------------------------------------------------------------------- *)
(* The innermost loops of NTT and NTTInv (one block of butterflies). Their   *)
(* bodies are taken from the generated definitions and named, so that the    *)
(* proofs about the outer loops can rewrite freely without changing them.    *)
(* ------------------------------------------------------------------------- *)

let NTT_IS_FOLDL t =
  match t with
    Comb(Comb(Comb(Const("native_foldl",_),_),_),_) -> true
  | _ -> false;;

let NTT_IS_FOLD t =
  match t with
    Comb(Comb(Comb(Const("native_fold",_),_),_),_) -> true
  | _ -> false;;

let NTT_INNER_BODY defth boundvar =
  let rhs = rand(snd(strip_forall(concl defth))) in
  let loop = find_term (fun t -> NTT_IS_FOLDL t && mem boundvar (frees t))
                       rhs in
  lhand(rator loop);;

let ntt_hol_fwd_inner =
  let body = NTT_INNER_BODY NTT_hol_DEF `bound:int` in
  let fvs = frees body in
  let lenv = find (fun v -> name_of v = "len") fvs
  and zv = find (fun v -> name_of v = "vf") fvs in
  let c = mk_var("ntt_hol_fwd_inner",
                 mk_fun_ty `:int` (mk_fun_ty `:int` (type_of body))) in
  new_definition (mk_eq(list_mk_comb(c,[lenv; zv]), body));;

let ntt_hol_inv_inner =
  let body = NTT_INNER_BODY NTTInv_hol_DEF `bound:int` in
  let fvs = frees body in
  let lenv = find (fun v -> name_of v = "len") fvs
  and zv = find (fun v -> name_of v = "vh") fvs in
  let c = mk_var("ntt_hol_inv_inner",
                 mk_fun_ty `:int` (mk_fun_ty `:int` (type_of body))) in
  new_definition (mk_eq(list_mk_comb(c,[lenv; zv]), body));;

(* One block of the NTT: the butterflies j = S, ..., S + L - 1 with zeta z.  *)

let NTT_HOL_FWD_INNER = prove
 (`!z S L x n1 n2 n3.
        1 <= L /\ S + 2 * L <= 256
        ==> ?m1 m2 m3.
              native_foldl (ntt_hol_fwd_inner (&L) z)
                (list_of_seq (\k. &S + &k) L)
                (n1,n2,n3,Native_Assigned (lift_poly x)) =
              Value (m1,m2,m3,
                     Native_Assigned (lift_poly (ntt_fwd_block z S L x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`L:num`; `ntt_hol_fwd_inner (&L) z`; `\k. &S + &k:int`;
    `\i s. ?m1:ty_native_slot_4 m2:ty_native_slot_4 m3:ty_native_slot_4.
             s = (m1,m2,m3,
                  Native_Assigned
                   (lift_poly
                     (\p. if S <= p /\ p < S + i then x p + z * x (p + L)
                          else if S + L <= p /\ p < S + L + i
                          then x (p - L) - z * x p
                          else (x:num->int) p):(fips204_ntt)fips204_poly))`;
    `(n1:ty_native_slot_4),(n2:ty_native_slot_4),(n3:ty_native_slot_4),
     Native_Assigned (lift_poly x:(fips204_ntt)fips204_poly)`]
   NTT_FOLDL_INV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`n1:ty_native_slot_4`; `n2:ty_native_slot_4`;
                            `n3:ty_native_slot_4`] THEN
      REWRITE_TAC[PAIR_EQ] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `s:ty_native_slot_4#ty_native_slot_4#
                                    ty_native_slot_4#ty_native_slot_5`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
    SUBGOAL_THEN `S + i < 256 /\ (S + i) + L < 256 /\ ~((S + i) + L = S + i)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ntt_hol_fwd_inner] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[UNCURRY_DEF; INT_OF_NUM_ADD] THEN
    ASM_SIMP_TAC(NTT_BODY_RULES @
                 [ISA_LIST_UPDATE_LIST_OF_SEQ; NTT_RESIDUE_REP]) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; LIFT_ZQ_REP; NTT_RESIDUE_REP] THEN
    REWRITE_TAC[injectivity "native_result"; UNWIND_THM1; PAIR_EQ;
                RIGHT_EXISTS_AND_THM; injectivity "native_slot";
                EXISTS_REFL] THEN
    SUBGOAL_THEN
     `~(S + i < S + i) /\ ~(S + L <= S + i) /\ ~((S + i) + L < S + i) /\
      S + L <= (S + i) + L /\ ~((S + i) + L < S + L + i) /\
      ((S + i) + L) - L = S + i`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NTT_LIFT_ZQ_CONV) THEN
    REWRITE_TAC[lift_poly; fips204_poly_INJECT] THEN
    MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `p = S + i` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `S <= S + i /\ S + i < S + SUC i`
       (fun th -> REWRITE_TAC[th]) THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `p = (S + i) + L` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `~(S <= (S + i) + L /\ (S + i) + L < S + SUC i) /\
        S + L <= (S + i) + L /\ (S + i) + L < S + L + SUC i /\
        ((S + i) + L) - L = S + i`
       (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(p < S + SUC i <=> p < S + i) /\
                  (p < S + L + SUC i <=> p < S + L + i)`
     (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:ty_native_slot_4#ty_native_slot_4#
                                ty_native_slot_4#ty_native_slot_5`
    (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`m1:ty_native_slot_4`; `m2:ty_native_slot_4`;
                        `m3:ty_native_slot_4`] THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; ntt_fwd_block] THEN
  REWRITE_TAC[ARITH_RULE `S + L + L = S + 2 * L`]);;
(* ------------------------------------------------------------------------- *)
(* The schedules of the three loops of NTT and NTTInv.                       *)
(* ------------------------------------------------------------------------- *)

let NTT_FWD_LENS = prove
 (`[&128; &64; &32; &16; &8; &4; &2; &1] =
   list_of_seq (\t. &(2 EXP (7 - t)):int) 8`,
  CONV_TAC(RAND_CONV LIST_OF_SEQ_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let NTT_INV_LENS = prove
 (`native_schedule 256 (\len. len < &256) (int_mul (&2)) (&1) =
   list_of_seq (\u. &(2 EXP u):int) 8`,
  CONV_TAC(RAND_CONV LIST_OF_SEQ_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(CONV_TAC(ONCE_DEPTH_CONV NTT_SCHEDULE_NUMERAL_CONV) THEN
         CONV_TAC(DEPTH_CONV BETA_CONV) THEN
         CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN REWRITE_TAC[]));;

let NTT_SCHEDULE_MID = prove
 (`!t. t < 8
       ==> native_schedule 257 (\s. s < &256) (\s. s + &2 * &(2 EXP (7 - t)))
                           (&0:int) =
           list_of_seq (\b. &(2 * 2 EXP (7 - t) * b)) (2 EXP t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2 EXP t`; `257`; `&0:int`; `&2 * &(2 EXP (7 - t)):int`]
                NTT_SCHEDULE_STEP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_LT; EXP_EQ_0; ARITH_EQ;
                MULT_EQ_0; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
    TRANS_TAC LET_TRANS `2 EXP 7` THEN REWRITE_TAC[LE_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 + &(2 EXP t) * &2 * &(2 EXP (7 - t)) = &256:int`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[INT_ADD_LID; INT_OF_NUM_MUL; INT_OF_NUM_EQ] THEN
    UNDISCH_TAC `t < 8` THEN SPEC_TAC(`t:num`,`t:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; INT_ADD_LID; INT_OF_NUM_MUL] THEN
    REWRITE_TAC[MULT_AC]]);;

let NTT_SCHEDULE_INV_MID = prove
 (`!u. u < 8
       ==> native_schedule 257 (\s. s < &256) (\s. s + &2 * &(2 EXP u))
                           (&0:int) =
           list_of_seq (\b. &(2 * 2 EXP u * b)) (2 EXP (7 - u))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2 EXP (7 - u)`; `257`; `&0:int`; `&2 * &(2 EXP u):int`]
                NTT_SCHEDULE_STEP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_LT; EXP_EQ_0; ARITH_EQ;
                MULT_EQ_0; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
    TRANS_TAC LET_TRANS `2 EXP 7` THEN REWRITE_TAC[LE_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 + &(2 EXP (7 - u)) * &2 * &(2 EXP u) = &256:int`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[INT_ADD_LID; INT_OF_NUM_MUL; INT_OF_NUM_EQ] THEN
    UNDISCH_TAC `u < 8` THEN SPEC_TAC(`u:num`,`u:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; INT_ADD_LID; INT_OF_NUM_MUL] THEN
    REWRITE_TAC[MULT_AC]]);;

let NTT_SCHEDULE_BLOCK = prove
 (`!S L. native_schedule (SUC (isa_nat (((&S + &L) - &1 + &1) - &S)))
                         (\j. j < (&S + &L) - &1 + &1) (\j. j + &1) (&S:int) =
         list_of_seq (\k. &S + &k) L`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NATIVE_SCHEDULE_INT] THEN
  REWRITE_TAC[INT_ARITH `((s + l) - &1 + &1) - s:int = l`; ISA_NAT_NUM] THEN
  REWRITE_TAC[ARITH_RULE `MIN (SUC l) l = l`]);;

let NTT_SCHEDULE_BLOCK2 = prove
 (`!S L. native_schedule (SUC (isa_nat ((&S + &L) - &S)))
                         (\j. j < &S + &L) (\j. j + &1) (&S:int) =
         list_of_seq (\k. &S + &k) L`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NATIVE_SCHEDULE_INT] THEN
  REWRITE_TAC[INT_ARITH `(s + l) - s:int = l`; ISA_NAT_NUM] THEN
  REWRITE_TAC[ARITH_RULE `MIN (SUC l) l = l`]);;

let NTT_LAYER_BOUND = prove
 (`!t b. t < 8 /\ b < 2 EXP t
         ==> 2 EXP t + b < 256 /\ 1 <= 2 EXP (7 - t) /\
             2 * 2 EXP (7 - t) * b + 2 * 2 EXP (7 - t) <= 256`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;
(* ------------------------------------------------------------------------- *)
(* NTT (FIPS 204 Algorithm 41) computes the layers ntt_fwd_layers 8, and so  *)
(* mldsa_ntt. The three loops are handled by invariants on the slots that    *)
(* are read: the zeta index m and the polynomial w_NTT.                      *)
(* ------------------------------------------------------------------------- *)

let NTT_INST_P p init =
  let sv = fst(dest_abs(snd(dest_abs p))) in
  let tyin = type_match (type_of sv) (type_of init) [] in
  inst tyin p;;

let NTT_FOLD_INV_TAC n f p =
  W(fun (asl,w) ->
    let fd = find_term NTT_IS_FOLD w in
    let [body;_;init] = snd(strip_comb fd) in
    MP_TAC(ISPECL [n; body; f; NTT_INST_P p init; init] NTT_FOLD_INV));;

let NTT_HOL_RECORD_RULES =
  NTT_hol_emitted_state_SELECTORS @
  [NTT_hol_emitted_start_update_EXT; NTT_hol_emitted_len_update_EXT];;

let NTT_HOL_LAYERS = prove
 (`!a. NTT_hol (lift_poly a) = Value (lift_poly (ntt_fwd_layers 8 a))`,
  GEN_TAC THEN REWRITE_TAC[NTT_hol_DEF; GSYM ntt_hol_fwd_inner] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[NTT_SCHEDULE_256] THEN
  W(fun (asl,w) ->
    let cp = find_term NTT_IS_FOLDL w in
    SUBGOAL_THEN (mk_eq(cp, `Value (lift_poly a:(fips204_ntt)fips204_poly)`))
    SUBST1_TAC) THENL
   [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [lift_poly] THEN
    MATCH_MP_TAC NTT_POINTWISE_LOOP THEN
    REWRITE_TAC[LENGTH_MAP; LENGTH_REPLICATE] THEN NTT_POINTWISE_STEP_TAC [];
    ALL_TAC] THEN
  REWRITE_TAC[NATIVE_BIND_VALUE; NTT_FWD_LENS] THEN
  NTT_FOLD_INV_TAC `8` `\t. &(2 EXP (7 - t)):int`
   `\t s. FST(FST(FST s)) = Native_Assigned (&(2 EXP t) - &1:int) /\
          SND(FST(SND s)) =
          Native_Assigned
           (lift_poly (ntt_fwd_layers t a):(fips204_ntt)fips204_poly)` THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
     [REWRITE_TAC[ntt_fwd_layers] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC INT_REDUCE_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_REWRITE_TAC[UNCURRY_DEF] THEN
    ASM_SIMP_TAC[NTT_SCHEDULE_MID] THEN
    NTT_FOLD_INV_TAC `2 EXP k` `\b. &(2 * 2 EXP (7 - k) * b):int`
     `\b s. FST(FST(FST s)) = Native_Assigned (&(2 EXP k + b) - &1:int) /\
            SND(FST(SND s)) =
            Native_Assigned
             (lift_poly (ntt_fwd_blocks k b (ntt_fwd_layers k a)):
              (fips204_ntt)fips204_poly)` THEN
    ANTS_TAC THENL
     [CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
       [REWRITE_TAC[ntt_fwd_blocks; ADD_CLAUSES]; ALL_TAC] THEN
      REWRITE_TAC[FORALL_PAIR_THM] THEN X_GEN_TAC `b:num` THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
      ASM_REWRITE_TAC[UNCURRY_DEF] THEN REWRITE_TAC NTT_MONAD_RULES THEN
      REWRITE_TAC[INT_SUB_ADD] THEN
      MP_TAC(SPECL [`k:num`; `b:num`] NTT_LAYER_BOUND) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[EQ_BITREV8; NATIVE_BIND_VALUE; NTT_POW_MOD_NUM;
                   NTT_SCHEDULE_BLOCK2] THEN
      W(fun (asl,w) ->
        let lp = find_term NTT_IS_FOLDL w in
        let [bd; _; init] = snd(strip_comb lp) in
        let z = rand bd in
        let n1,r1 = dest_pair init in let n2,r2 = dest_pair r1 in
        let n3,wslot = dest_pair r2 in
        let x = rand(rand wslot) in
        MP_TAC(ISPECL [z; `2 * 2 EXP (7 - k) * b`; `2 EXP (7 - k)`; x;
                       n1; n2; n3] NTT_HOL_FWD_INNER)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[NATIVE_BIND_VALUE] THEN
      REWRITE_TAC(UNCURRY_DEF :: NTT_MONAD_RULES @ NTT_HOL_RECORD_RULES) THEN
      REWRITE_TAC[injectivity "native_result"; injectivity "statement_outcome";
                  UNWIND_THM1; injectivity "native_slot"; ntt_fwd_blocks] THEN
      REWRITE_TAC[ADD_CLAUSES; GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC(NTT_MONAD_RULES @ NTT_HOL_RECORD_RULES) THEN
    REWRITE_TAC[injectivity "native_result"; injectivity "statement_outcome";
                UNWIND_THM1] THEN
    ASM_REWRITE_TAC[ntt_fwd_layers; injectivity "native_slot"] THEN
    REWRITE_TAC[EXP; MULT_2];
    ALL_TAC] THEN
  DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[NTT_FINISH_CONTINUE; TYPED_HOL_SLOT_READ_ASSIGNED]);;

let EQ_NTT = prove
 (`!a. NTT_hol (lift_poly a) = Value (lift_poly (mldsa_ntt (mldsa_poly a)))`,
  REWRITE_TAC[NTT_HOL_LAYERS; NTT_LIFT_FWD_LAYERS]);;

let EQ_NTT_RQ = prove
 (`!f. f IN ring_carrier mldsa_rq
       ==> NTT_hol (lift_poly (\i. coeff i f)) = Value (lift_poly (mldsa_ntt f))`,
  SIMP_TAC[EQ_NTT; MLDSA_POLY_COEFF]);;

(* ------------------------------------------------------------------------- *)
(* NTTInv (FIPS 204 Algorithm 42): one block of inverse butterflies, the     *)
(* layers, and the final scaling by 256^-1 = 8347681 mod q.                  *)
(* ------------------------------------------------------------------------- *)

let NTT_HOL_INV_INNER = prove
 (`!z S L x n1.
        1 <= L /\ S + 2 * L <= 256
        ==> ?m1.
              native_foldl (ntt_hol_inv_inner (&L) z)
                (list_of_seq (\k. &S + &k) L)
                (n1,Native_Assigned (lift_poly x)) =
              Value (m1,Native_Assigned (lift_poly (ntt_inv_block z S L x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`L:num`; `ntt_hol_inv_inner (&L) z`; `\k. &S + &k:int`;
    `\i s. ?m1:ty_native_slot_4.
             s = (m1,
                  Native_Assigned
                   (lift_poly
                     (\p. if S <= p /\ p < S + i then x p + x (p + L)
                          else if S + L <= p /\ p < S + L + i
                          then z * (x (p - L) - x p)
                          else (x:num->int) p):(fips204_time)fips204_poly))`;
    `(n1:ty_native_slot_4),
     Native_Assigned (lift_poly x:(fips204_time)fips204_poly)`]
   NTT_FOLDL_INV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `n1:ty_native_slot_4` THEN
      REWRITE_TAC[PAIR_EQ] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `s:ty_native_slot_4#ty_native_slot_6`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THEN
    SUBGOAL_THEN `S + i < 256 /\ (S + i) + L < 256 /\ ~((S + i) + L = S + i) /\
     ~(S + i = (S + i) + L)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ntt_hol_inv_inner] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[UNCURRY_DEF; INT_OF_NUM_ADD] THEN
    ASM_SIMP_TAC(NTT_BODY_RULES @
                 [ISA_LIST_UPDATE_LIST_OF_SEQ; NTT_RESIDUE_REP]) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; LIFT_ZQ_REP; NTT_RESIDUE_REP] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[injectivity "native_result"; UNWIND_THM1; PAIR_EQ;
                RIGHT_EXISTS_AND_THM; injectivity "native_slot";
                EXISTS_REFL] THEN
    SUBGOAL_THEN
     `~(S + i < S + i) /\ ~(S + L <= S + i) /\ ~((S + i) + L < S + i) /\
      S + L <= (S + i) + L /\ ~((S + i) + L < S + L + i) /\
      ((S + i) + L) - L = S + i`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NTT_LIFT_ZQ_CONV) THEN
    REWRITE_TAC[lift_poly; fips204_poly_INJECT] THEN
    MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `p = S + i` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `S <= S + i /\ S + i < S + SUC i /\ ~(S + i = (S + i) + L)`
       (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `p = (S + i) + L` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `~(S <= (S + i) + L /\ (S + i) + L < S + SUC i) /\
        S + L <= (S + i) + L /\ (S + i) + L < S + L + SUC i /\
        ((S + i) + L) - L = S + i`
       (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(p < S + SUC i <=> p < S + i) /\
                  (p < S + L + SUC i <=> p < S + L + i)`
     (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:ty_native_slot_4#ty_native_slot_6`
    (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `m1:ty_native_slot_4` THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; ntt_inv_block] THEN
  REWRITE_TAC[ARITH_RULE `S + L + L = S + 2 * L`]);;

let NTT_INV_LAYER_BOUND = prove
 (`!k b. k < 8 /\ b < 2 EXP (7 - k)
         ==> 1 <= 2 EXP (8 - k) - b /\ 2 EXP (8 - k) - 1 - b < 256 /\
             1 <= 2 EXP k /\ 2 * 2 EXP k * b + 2 * 2 EXP k <= 256 /\
             2 EXP (8 - k) - SUC b = 2 EXP (8 - k) - 1 - b /\
             2 EXP (8 - k) - b - 1 = 2 EXP (8 - k) - 1 - b`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let NTTINV_HOL_RECORD_RULES =
  NTTInv_hol_emitted_state_SELECTORS @
  [NTTInv_hol_emitted_start_update_EXT; NTTInv_hol_emitted_len_update_EXT];;

let NTT_HOL_INV_LAYERS = prove
 (`!a. NTTInv_hol (lift_poly a) =
       Value (lift_poly (\i. &8347681 * ntt_inv_layers 8 a i))`,
  GEN_TAC THEN REWRITE_TAC[NTTInv_hol_DEF; GSYM ntt_hol_inv_inner] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[NTT_SCHEDULE_256] THEN
  W(fun (asl,w) ->
    let cp = find_term NTT_IS_FOLDL w in
    SUBGOAL_THEN (mk_eq(cp, `Value (lift_poly a:(fips204_time)fips204_poly)`))
    SUBST1_TAC) THENL
   [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [lift_poly] THEN
    MATCH_MP_TAC NTT_POINTWISE_LOOP THEN
    REWRITE_TAC[LENGTH_MAP; LENGTH_REPLICATE] THEN NTT_POINTWISE_STEP_TAC [];
    ALL_TAC] THEN
  REWRITE_TAC[NATIVE_BIND_VALUE; NTT_INV_LENS] THEN
  NTT_FOLD_INV_TAC `8` `\u. &(2 EXP u):int`
   `\t s. FST(FST s) = Native_Assigned (&(2 EXP (8 - t)):int) /\
          FST(SND(SND s)) =
          Native_Assigned
           (lift_poly (ntt_inv_layers t a):(fips204_time)fips204_poly)` THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
     [REWRITE_TAC[ntt_inv_layers] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC INT_REDUCE_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_REWRITE_TAC[UNCURRY_DEF] THEN
    ASM_SIMP_TAC[NTT_SCHEDULE_INV_MID] THEN
    NTT_FOLD_INV_TAC `2 EXP (7 - k)` `\b. &(2 * 2 EXP k * b):int`
     `\b s. FST(FST s) = Native_Assigned (&(2 EXP (8 - k) - b):int) /\
            FST(SND(SND s)) =
            Native_Assigned
             (lift_poly (ntt_inv_blocks k b (ntt_inv_layers k a)):
              (fips204_time)fips204_poly)` THEN
    ANTS_TAC THENL
     [CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
       [REWRITE_TAC[ntt_inv_blocks; SUB_0]; ALL_TAC] THEN
      REWRITE_TAC[FORALL_PAIR_THM] THEN X_GEN_TAC `b:num` THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
      ASM_REWRITE_TAC[UNCURRY_DEF] THEN REWRITE_TAC NTT_MONAD_RULES THEN
      MP_TAC(SPECL [`k:num`; `b:num`] NTT_INV_LAYER_BOUND) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&(2 EXP (8 - k) - b) - &1:int = &(2 EXP (8 - k) - 1 - b)`
       SUBST1_TAC THENL
       [ASM_REWRITE_TAC[GSYM INT_OF_NUM_SUB] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[EQ_BITREV8; NATIVE_BIND_VALUE; TYPED_HOL_INT_POW_NUM;
                   NTT_ISA_INT_MOD_Q; NTT_SCHEDULE_BLOCK] THEN
      W(fun (asl,w) ->
        let lp = find_term NTT_IS_FOLDL w in
        let [bd; _; init] = snd(strip_comb lp) in
        let z = rand bd in
        let n1,wslot = dest_pair init in
        let x = rand(rand wslot) in
        MP_TAC(ISPECL [z; `2 * 2 EXP k * b`; `2 EXP k`; x; n1]
                      NTT_HOL_INV_INNER)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[NATIVE_BIND_VALUE] THEN
      REWRITE_TAC(UNCURRY_DEF :: NTT_MONAD_RULES @ NTT_HOL_RECORD_RULES) THEN
      REWRITE_TAC(UNCURRY_DEF :: NTT_MONAD_RULES @ NTTINV_HOL_RECORD_RULES) THEN
  REWRITE_TAC[injectivity "native_result"; injectivity "statement_outcome";
                  UNWIND_THM1; injectivity "native_slot"; ntt_inv_blocks];
      DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC(NTT_MONAD_RULES @ NTTINV_HOL_RECORD_RULES) THEN
    REWRITE_TAC[injectivity "native_result"; injectivity "statement_outcome";
                UNWIND_THM1] THEN
    ASM_REWRITE_TAC[ntt_inv_layers; injectivity "native_slot"] THEN
    SUBGOAL_THEN `2 EXP (8 - k) - 2 EXP (7 - k) = 2 EXP (8 - SUC k)`
     (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `k < 8` THEN SPEC_TAC(`k:num`,`k:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV];
    DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[NTT_FINISH_CONTINUE; TYPED_HOL_SLOT_READ_ASSIGNED] THEN
    REWRITE_TAC[TYPED_HOL_SLOT_READ_ASSIGNED] THEN
  W(fun (asl,w) ->
    let lp = find_term NTT_IS_FOLDL w in
    let [bd; _; init] = snd(strip_comb lp) in
    MP_TAC(ISPECL [`256`; bd; `\k. &k:int`;
      `\k s. s = Native_Assigned
                   (lift_poly (\i. if i < k then &8347681 * ntt_inv_layers 8 a i
                                   else ntt_inv_layers 8 a i)
                     :(fips204_time)fips204_poly)`; init] NTT_FOLDL_INV)) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[LT; ETA_AX]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `s:((fips204_time)fips204_poly)native_slot`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC(NTT_BODY_RULES @
                 [ISA_LIST_UPDATE_LIST_OF_SEQ; NTT_RESIDUE_REP;
                  NTT_ISA_INT_MOD_Q]) THEN
    REWRITE_TAC[LT_REFL; injectivity "native_result"; UNWIND_THM1;
              injectivity "native_slot"] THEN
  CONV_TAC(ONCE_DEPTH_CONV NTT_LIFT_ZQ_CONV) THEN
  REWRITE_TAC[lift_poly; fips204_poly_INJECT] THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `p:num = i` THEN ASM_REWRITE_TAC[LT; LT_REFL] THEN
  CONV_TAC(ONCE_DEPTH_CONV NTT_LIFT_ZQ_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
    DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NATIVE_BIND_VALUE; TYPED_HOL_SLOT_READ_ASSIGNED; injectivity "native_result"] THEN
  REWRITE_TAC[lift_poly; fips204_poly_INJECT] THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
  SIMP_TAC[]]);;

let EQ_NTTINV = prove
 (`!a. (!k. k < 256 ==> &0 <= a k /\ a k < &8380417)
       ==> NTTInv_hol (lift_poly a) =
           Value (lift_poly (\i. coeff i (mldsa_ntt_inv a)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NTT_HOL_INV_LAYERS] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC NTT_LIFT_POLY_EQ_ALT THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC NTT_INV_LAYERS_MLDSA_NTT_INV THEN ASM_REWRITE_TAC[]);;

