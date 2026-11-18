(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The matrix-vector products of mldsa-native's code with                    *)
(* MLD_CONFIG_REDUCE_RAM (common/mldsa_native_lazy.ml) and those without it  *)
(* (common/mldsa_native_polyvec.ml, common/mldsa_native_sign.ml): the        *)
(* proofs of the statements of lazy_eq_spec.ml of a reduced-RAM build, which *)
(* its lazy_eq_proof.ml loads after that file, so that each prove below      *)
(* records the theorem for the statement (see common/relative.ml).           *)
(*                                                                           *)
(* The reduced-RAM code reduces each product of an entry of A with a         *)
(* polynomial before it adds the products and reduces the sum; the code      *)
(* without it adds the products in 64 bits and reduces the sum once. For     *)
(* entries below q and polynomials below MLD_NTT_BOUND, both sums are        *)
(* congruent mod q to 2^-32 times the exact sum and below q in absolute      *)
(* value once reduced, and so are their inverse NTTs, which mld_caddq maps   *)
(* to the same representative in [0,q).                                      *)
(* ========================================================================= *)

needs "common/fips204/properties/mldsa_native_ntt_cong.ml";;
needs "common/mldsa_native_lazy.ml";;
needs "common/mldsa_native_sign.ml";;

let is_int_cong t = can (term_match [] `(x:int == y) (mod n)`) t;;

(* ------------------------------------------------------------------------- *)
(* The entries of the matrix: the coefficients sampled from a seed whose     *)
(* SHAKE128 output has 256 acceptable groups are in [0,q), and entry (i,j)   *)
(* is polynomial l * i + j of mld_polyvec_matrix_expand l rho.               *)
(* ------------------------------------------------------------------------- *)

let MLD_POLY_UNIFORM_LT_Q = prove
 (`!seed i.
        mld_rej_uniform_terminates (mld_shake128_stream 34 seed) /\ i < 256
        ==> val(mld_poly_uniform seed i) < 8380417`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP MLD_REJ_UNIFORM_TERMINATES) THEN
  REWRITE_TAC[mld_poly_uniform; mld_rej_uniform_poly;
              mld_rej_uniform_list] THEN
  ABBREV_TAC `s = mld_shake128_stream 34 seed` THEN
  ABBREV_TAC `l = FILTER (\t:int32. val t < 8380417)
               (list_of_seq (mld_rej_uniform_cand s)
                 (280 + 56 * mld_poly_uniform_nblocks s))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `MEM (EL i l) (l:int32 list)` MP_TAC THENL
   [MATCH_MP_TAC MEM_EL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "l" THEN REWRITE_TAC[MEM_FILTER] THEN SIMP_TAC[]);;

let MLD_LAZY_IVAL_VAL_SMALL = prove
 (`!x:int32. val x < 2147483648 ==> ival x = &(val x)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ival; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let MLD_MATRIX_ENTRY_LT_Q = prove
 (`!k l rho i j n.
        mld_matrix_terminates k l rho /\ i < k /\ j < l /\ n < 256
        ==> &0 <= ival(mld_matrix_entry rho i j n) /\
            ival(mld_matrix_entry rho i j n) < &8380417`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(mld_matrix_entry rho i j n) < 8380417` ASSUME_TAC THENL
   [REWRITE_TAC[mld_matrix_entry] THEN MATCH_MP_TAC MLD_POLY_UNIFORM_LT_Q THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[mld_matrix_terminates]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLD_LAZY_IVAL_VAL_SMALL o
    rand o lhand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[INT_POS; INT_OF_NUM_LT]);;

let MLD_MATRIX_ENTRY_EXPAND = prove
 (`!l rho i j n.
        j < l /\ n < 256
        ==> mld_polyvec_matrix_expand l rho ((256 * l) * i + 256 * j + n) =
            mld_matrix_entry rho i j n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `(256 * l) * i + 256 * j + n =
                          256 * (l * i + j) + n`] THEN
  ASM_SIMP_TAC[MLD_POLYVEC_MATRIX_EXPAND_COEFF; mld_matrix_entry] THEN
  SUBGOAL_THEN `(l * i + j) DIV l = i /\ (l * i + j) MOD l = j`
   (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `~(l = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT; ADD_CLAUSES]);;

let MLD_MATRIX_ROW_ENTRY = prove
 (`!l rho i j.
        j < 256 * l
        ==> mld_polyvec_matrix_expand l rho ((256 * l) * i + j) =
            mld_matrix_entry rho i (j DIV 256) (j MOD 256)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`l:num`; `rho:num`; `i:num`; `j DIV 256`; `j MOD 256`]
               MLD_MATRIX_ENTRY_EXPAND) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ]; ARITH_TAC] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `256 * j DIV 256 + j MOD 256 = j`]]);;

(* ------------------------------------------------------------------------- *)
(* Sums and differences of 32-bit words that do not overflow.                *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_IVAL_WORD_ADD = prove
 (`!x y:int32.
        --(&2147483648) <= ival x + ival y /\ ival x + ival y < &2147483648
        ==> ival(word_add x y) = ival x + ival y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_add x y:int32 = iword(ival x + ival y)` SUBST1_TAC THENL
   [REWRITE_TAC[IWORD_INT_ADD; IWORD_IVAL]; ALL_TAC] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_INT_ARITH_TAC);;

let MLD_LAZY_IVAL_WORD_SUB = prove
 (`!x y:int32.
        --(&2147483648) <= ival x - ival y /\ ival x - ival y < &2147483648
        ==> ival(word_sub x y) = ival x - ival y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub x y:int32 = iword(ival x - ival y)` SUBST1_TAC THENL
   [REWRITE_TAC[IWORD_INT_SUB; IWORD_IVAL]; ALL_TAC] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The partial sums of a row (mld_lazy_acc): congruent to 2^-32 times the    *)
(* exact sum of the products, and below (n + 1) q for n + 1 products.        *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_IVAL_ADD_TERM w =
  find_term (fun t -> is_comb t && rator t = `ival:int32->int` &&
                      is_comb(rand t) &&
                      (try fst(dest_const(rator(rator(rand t)))) = "word_add"
                       with _ -> false)) w;;

let MLD_LAZY_ACC_CONG = prove
 (`!k l rho i (v:num->int32) n m.
        mld_matrix_terminates k l rho /\ i < k /\ n < l /\ l <= 8 /\ m < 256 /\
        (!j. j < 256 * l ==> abs(ival(v j)) < &94279689)
        ==> (ival(mld_lazy_acc rho i v n m) ==
             isum (0..n)
              (\j. ival(mld_matrix_entry rho i j m) * ival(v(256 * j + m))) *
             &(inverse_mod 8380417 4294967296)) (mod &8380417) /\
            abs(ival(mld_lazy_acc rho i v n m)) < &(n + 1) * &8380417`,
  REPLICATE_TAC 5 GEN_TAC THEN INDUCT_TAC THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THENL
   [REWRITE_TAC[mld_lazy_acc] THEN
    MP_TAC(ISPECL [`mld_matrix_entry rho i 0`; `mld_poly_of (v:num->int32) 0`;
                   `m:num`] MLD_POLY_POINTWISE_MONTGOMERY_CONG) THEN
    REWRITE_TAC[mld_poly_of; MULT_CLAUSES; ADD_CLAUSES; ETA_AX] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(SPECL [`k:num`; `l:num`; `rho:num`; `i:num`; `0`; `m:num`]
                     MLD_MATRIX_ENTRY_LT_Q) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; INT_ARITH_TAC];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[mldsa_pointwise; o_THM; INT_CONG_RREM] THEN
    REWRITE_TAC[NUMSEG_SING; ISUM_SING; MULT_CLAUSES; ADD_CLAUSES] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[GSYM INT_MUL_ASSOC]; ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
    can (find_term ((=) `mld_lazy_acc`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`mld_matrix_entry rho i (SUC n)`;
                 `mld_poly_of (v:num->int32) (SUC n)`; `m:num`]
                MLD_POLY_POINTWISE_MONTGOMERY_CONG) THEN
  REWRITE_TAC[mld_poly_of] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`k:num`; `l:num`; `rho:num`; `i:num`; `SUC n`; `m:num`]
                   MLD_MATRIX_ENTRY_LT_Q) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; INT_ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[mldsa_pointwise; o_THM; INT_CONG_RREM] THEN STRIP_TAC THEN
  REWRITE_TAC[mld_lazy_acc; mld_poly_add; mld_poly_of] THEN
  SUBGOAL_THEN `&(n + 1) <= &7:int` ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLD_LAZY_IVAL_WORD_ADD o
    MLD_LAZY_IVAL_ADD_TERM o snd) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ISUM_CLAUSES_NUMSEG; LE_0] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_int_cong o concl))) THEN
    SPEC_TAC(`&(inverse_mod 8380417 4294967296):int`,`c:int`) THEN
    SPEC_TAC(`&8380417:int`,`q:int`) THEN
    SPEC_TAC(`isum (0..n) (\j. ival (mld_matrix_entry rho i j m) *
                               ival ((v:num->int32) (256 * j + m)))`,
             `S:int`) THEN
    CONV_TAC INTEGER_RULE;
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      let t = concl th in
      not(is_forall t) && can (find_term ((=) `abs:int->int`)) t))) THEN
    REWRITE_TAC[ADD1; GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Row i of the two products: congruent and below q (for l = 4, 5 and 7,     *)
(* the lengths of ML-DSA-44, -65 and -87).                                   *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_ROW_CONG_STMT l =
  subst [mk_small_numeral l,`L:num`]
  `!k rho (v:num->int32) i m.
     mld_matrix_terminates k L rho /\ i < k /\ m < 256 /\
     (!j. j < 256 * L ==> abs(ival(v j)) < &94279689)
     ==> (ival(mld_polyvec_matrix_row_lazy L rho v i m) ==
          ival(mld_polyvec_pointwise_acc_montgomery L
                (\j. mld_polyvec_matrix_expand L rho ((256 * L) * i + j)) v m))
         (mod &8380417) /\
         abs(ival(mld_polyvec_matrix_row_lazy L rho v i m)) < &8380417 /\
         abs(ival(mld_polyvec_pointwise_acc_montgomery L
                   (\j. mld_polyvec_matrix_expand L rho ((256 * L) * i + j))
                   v m)) < &8380417`;;

let MLD_LAZY_ROW_CONG_TAC accth l =
  let lt = mk_small_numeral l and l1 = mk_small_numeral (l - 1) in
  let sub t = subst [lt,`L:num`; l1,`L1:num`] t in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; lt; `rho:num`; `i:num`; `v:num->int32`; l1; `m:num`]
               MLD_LAZY_ACC_CONG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [sub `mld_lazy_acc rho i (v:num->int32) L1`; `m:num`]
                MLD_FIPS204_POLY_REDUCE) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      let t = concl th in not(is_forall t) &&
      can (find_term ((=) `abs:int->int`)) t)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [sub `\j. mld_polyvec_matrix_expand L rho ((256 * L) * i + j)`;
                 `v:num->int32`; `m:num`] accth) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THENL
     [BETA_TAC THEN
      MP_TAC(SPECL [lt; `rho:num`; `i:num`; `j:num`] MLD_MATRIX_ROW_ENTRY) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      MP_TAC(SPECL [`k:num`; lt; `rho:num`; `i:num`; `j DIV 256`;
                    `j MOD 256`] MLD_MATRIX_ENTRY_LT_Q) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ARITH_TAC];
        INT_ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[MLDSA_POINTWISE_ACC_ISUM; o_THM; INT_CONG_RREM] THEN
  STRIP_TAC THEN
  REWRITE_TAC[mld_polyvec_matrix_row_lazy] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN (sub
     `isum {j | j < L}
       (\j. ival(mld_polyvec_matrix_expand L rho
                  ((256 * L) * i + m + 256 * j)) *
            ival((v:num->int32)(m + 256 * j))) =
      isum (0..L1)
       (\j. ival(mld_matrix_entry rho i j m) * ival(v(256 * j + m)))`)
    ASSUME_TAC THENL
     [SUBGOAL_THEN (sub `{j:num | j < L} = 0..L1`) SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC ISUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      REWRITE_TAC[ARITH_RULE `m + 256 * j = 256 * j + m`] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC MLD_MATRIX_ENTRY_EXPAND THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) &&
         can (find_term (fun t -> try fst(dest_const t) = "isum"
                                  with _ -> false)) (concl th)
      then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_int_cong o concl))) THEN
    SPEC_TAC(`&(inverse_mod 8380417 4294967296):int`,`c:int`) THEN
    SPEC_TAC(`&8380417:int`,`q:int`) THEN
    SPEC_TAC(sub `isum (0..L1) (\j. ival (mld_matrix_entry rho i j m) *
                                    ival ((v:num->int32) (256 * j + m)))`,
             `S:int`) THEN
    CONV_TAC INTEGER_RULE;
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      let t = concl th in not(is_forall t) && not(is_int_cong t) &&
      can (find_term ((=) `mld_poly_reduce`)) t))) THEN
    INT_ARITH_TAC;
    ASM_REWRITE_TAC[]];;

let MLD_LAZY_ROW_CONG_L4 = prove
 (MLD_LAZY_ROW_CONG_STMT 4,
  MLD_LAZY_ROW_CONG_TAC MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L4_CONG 4);;

let MLD_LAZY_ROW_CONG_L5 = prove
 (MLD_LAZY_ROW_CONG_STMT 5,
  MLD_LAZY_ROW_CONG_TAC MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L5_CONG 5);;

let MLD_LAZY_ROW_CONG_L7 = prove
 (MLD_LAZY_ROW_CONG_STMT 7,
  MLD_LAZY_ROW_CONG_TAC MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L7_CONG 7);;

let MLD_LAZY_ROW_CONG = prove
 (`!k l rho (v:num->int32) i m.
     (l = 4 \/ l = 5 \/ l = 7) /\
     mld_matrix_terminates k l rho /\ i < k /\ m < 256 /\
     (!j. j < 256 * l ==> abs(ival(v j)) < &94279689)
     ==> (ival(mld_polyvec_matrix_row_lazy l rho v i m) ==
          ival(mld_polyvec_pointwise_acc_montgomery l
                (\j. mld_polyvec_matrix_expand l rho ((256 * l) * i + j)) v m))
         (mod &8380417) /\
         abs(ival(mld_polyvec_matrix_row_lazy l rho v i m)) < &8380417 /\
         abs(ival(mld_polyvec_pointwise_acc_montgomery l
                   (\j. mld_polyvec_matrix_expand l rho ((256 * l) * i + j))
                   v m)) < &8380417`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  FIRST [MATCH_MP_TAC MLD_LAZY_ROW_CONG_L4; MATCH_MP_TAC MLD_LAZY_ROW_CONG_L5;
         MATCH_MP_TAC MLD_LAZY_ROW_CONG_L7] THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The inverse NTT of congruent polynomials below q: congruent and below     *)
(* q, as mld_poly_invntt_tomont only multiplies and adds coefficients;       *)
(* and mld_caddq of congruent values below q.                                *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_INT_CONG_ISUM = prove
 (`!n f g (s:A->bool).
        FINITE s /\ (!x. x IN s ==> (f x == g x) (mod n))
        ==> (isum s f == isum s g) (mod n)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(BETA_RULE(ISPEC `(\x y:int. (x == y) (mod n))`
    ISUM_RELATED)) THEN
  ASM_REWRITE_TAC[INTEGER_RULE `(x:int == x) (mod n)`;
   INTEGER_RULE
   `(x:int == y) (mod n) /\ (x' == y') (mod n)
    ==> (x + x' == y + y') (mod n)`]);;

let MLD_LAZY_BITREVERSE8_LT = prove
 (`!j. j < 256 ==> bitreverse8 j < 256`,
  SIMP_TAC[BITREVERSE8_ALT] THEN GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `word_reversefields 1 (word j:8 word)` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let MLD_LAZY_INVERSE_NTT_CONG = prove
 (`!f g k.
        (!i. i < 256 ==> (f i == g i) (mod &8380417))
        ==> arm_mldsa_inverse_ntt f k = arm_mldsa_inverse_ntt g k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[arm_mldsa_inverse_ntt; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!a x y n:int. (x == y) (mod n) ==> (a * x == a * y) (mod n)`) THEN
  MATCH_MP_TAC MLD_LAZY_INT_CONG_ISUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!x y z n:int. (x == y) (mod n) ==> (x * z == y * z) (mod n)`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC MLD_LAZY_BITREVERSE8_LT THEN
  ASM_ARITH_TAC);;

let MLD_LAZY_INVNTT_CONG = prove
 (`!x y:num->int32.
        (!i. i < 256
             ==> (ival(x i) == ival(y i)) (mod &8380417) /\
                 abs(ival(x i)) < &8380417 /\ abs(ival(y i)) < &8380417)
        ==> !i. i < 256
                ==> (ival(mld_poly_invntt_tomont x i) ==
                     ival(mld_poly_invntt_tomont y i)) (mod &8380417) /\
                    abs(ival(mld_poly_invntt_tomont x i)) < &8380417 /\
                    abs(ival(mld_poly_invntt_tomont y i)) < &8380417`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:num->int32` MLD_POLY_INVNTT_TOMONT_CONG) THEN
  MP_TAC(SPEC `y:num->int32` MLD_POLY_INVNTT_TOMONT_CONG) THEN
  ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (find_term ((=) `arm_mldsa_inverse_ntt`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `arm_mldsa_inverse_ntt (ival o (x:num->int32)) i =
                arm_mldsa_inverse_ntt (ival o (y:num->int32)) i`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MLD_LAZY_INVERSE_NTT_CONG THEN ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  SPEC_TAC(`arm_mldsa_inverse_ntt (ival o (y:num->int32)) i`,`z:int`) THEN
  SPEC_TAC(`&8380417:int`,`q:int`) THEN
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC INTEGER_RULE);;

let MLD_LAZY_CADDQ_CONG = prove
 (`!a b:int32.
        (ival a == ival b) (mod &8380417) /\
        abs(ival a) < &8380417 /\ abs(ival b) < &8380417
        ==> mld_caddq a = mld_caddq b`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM IVAL_EQ] THEN
  ASM_SIMP_TAC[MLD_CADDQ_REM] THEN ASM_REWRITE_TAC[INT_REM_EQ]);;

let MLD_LAZY_ROW_INVNTT = prove
 (`!k l rho (v:num->int32) i.
     (l = 4 \/ l = 5 \/ l = 7) /\
     mld_matrix_terminates k l rho /\ i < k /\
     (!j. j < 256 * l ==> abs(ival(v j)) < &94279689)
     ==> !m. m < 256
             ==> (ival(mld_poly_invntt_tomont
                        (mld_polyvec_matrix_row_lazy l rho v i) m) ==
                  ival(mld_poly_invntt_tomont
                        (mld_polyvec_pointwise_acc_montgomery l
                          (\j. mld_polyvec_matrix_expand l rho
                                 ((256 * l) * i + j)) v) m))
                 (mod &8380417) /\
                 abs(ival(mld_poly_invntt_tomont
                           (mld_polyvec_matrix_row_lazy l rho v i) m))
                 < &8380417 /\
                 abs(ival(mld_poly_invntt_tomont
                           (mld_polyvec_pointwise_acc_montgomery l
                             (\j. mld_polyvec_matrix_expand l rho
                                    ((256 * l) * i + j)) v) m))
                 < &8380417`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MLD_LAZY_INVNTT_CONG THEN
  X_GEN_TAC `i':num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `l:num`; `rho:num`; `v:num->int32`; `i:num`; `i':num`]
               MLD_LAZY_ROW_CONG) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Key generation: polynomial i of t1 and of t0 packed.                      *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_COMPUTE_T_COEFF = prove
 (`!k l (unpack:(num->byte)->num->int32) p r sh s2b i m.
        (l = 4 \/ l = 5 \/ l = 7) /\ mld_matrix_terminates k l r /\ i < k /\
        m < 256 /\
        (!j. j < 256 * l ==> abs(ival(sh j)) < &94279689) /\
        (!m. m < 256 ==> abs(ival(unpack (\t. s2b(p * i + t)) m)) < &8380417)
        ==> mld_poly_caddq
             (mld_poly_reduce
               (mld_poly_add
                 (mld_poly_invntt_tomont
                   (mld_polyvec_matrix_row_lazy l r sh i))
                 (unpack (\t. s2b(p * i + t))))) m =
            mld_compute_t l unpack p r sh s2b (256 * i + m)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
                        STRIP_ASSUME_TAC(CONJUNCT2 th)) THEN
  ASM_SIMP_TAC[mld_compute_t; MLD_POLYVEC_COEFF] THEN
  REWRITE_TAC[mld_poly_caddq; mld_poly_reduce; mld_poly_add] THEN
  MP_TAC(SPECL [`k:num`; `l:num`; `r:num`; `sh:num->int32`; `i:num`]
               MLD_LAZY_ROW_INVNTT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `unpack:(num->byte)->num->int32`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC MLD_LAZY_CADDQ_CONG THEN
  ABBREV_TAC `u = (unpack:(num->byte)->num->int32) (\t. s2b(p * i + t)) m` THEN
  ABBREV_TAC `a = mld_poly_invntt_tomont
                   (mld_polyvec_matrix_row_lazy l r (sh:num->int32) i) m` THEN
  ABBREV_TAC `b = mld_poly_invntt_tomont
                   (mld_polyvec_pointwise_acc_montgomery l
                     (\j. mld_polyvec_matrix_expand l r ((256 * l) * i + j))
                     (sh:num->int32)) m` THEN
  MP_TAC(ISPECL [`a:int32`; `u:int32`] MLD_LAZY_IVAL_WORD_ADD) THEN
  MP_TAC(ISPECL [`b:int32`; `u:int32`] MLD_LAZY_IVAL_WORD_ADD) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPEC `word_add (a:int32) u` MLD_FIPS204_REDUCE32) THEN
  MP_TAC(ISPEC `word_add (b:int32) u` MLD_FIPS204_REDUCE32) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; STRIP_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_INT_ARITH_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_int_cong o concl))) THEN
  SPEC_TAC(`&8380417:int`,`q:int`) THEN CONV_TAC INTEGER_RULE);;

let MLD_LAZY_COMPUTE_T_ROW = prove
 (`!k l (unpack:(num->byte)->num->int32) p r sh s2b i.
        (l = 4 \/ l = 5 \/ l = 7) /\ mld_matrix_terminates k l r /\ i < k /\
        (!j. j < 256 * l ==> abs(ival(sh j)) < &94279689) /\
        (!m. m < 256 ==> abs(ival(unpack (\t. s2b(p * i + t)) m)) < &8380417)
        ==> (!j. j < 320
                 ==> mld_polyvec_pack 320 mld_polyt1_pack
                      (mld_polyvec_map mld_poly_power2round_hi
                        (mld_compute_t l unpack p r sh s2b)) (320 * i + j) =
                     mld_polyt1_pack
                      (mld_poly_power2round_hi
                        (mld_poly_caddq
                          (mld_poly_reduce
                            (mld_poly_add
                              (mld_poly_invntt_tomont
                                (mld_polyvec_matrix_row_lazy l r sh i))
                              (unpack (\t. s2b(p * i + t))))))) j) /\
            (!j. j < 416
                 ==> mld_polyvec_pack 416 mld_polyt0_pack
                      (mld_polyvec_map mld_poly_power2round_lo
                        (mld_compute_t l unpack p r sh s2b)) (416 * i + j) =
                     mld_polyt0_pack
                      (mld_poly_power2round_lo
                        (mld_poly_caddq
                          (mld_poly_reduce
                            (mld_poly_add
                              (mld_poly_invntt_tomont
                                (mld_polyvec_matrix_row_lazy l r sh i))
                              (unpack (\t. s2b(p * i + t))))))) j)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MLD_POLYVEC_PACK_COEFF] THENL
   [MATCH_MP_TAC MLD_POLYT1_PACK_LOCAL;
    MATCH_MP_TAC MLD_POLYT0_PACK_LOCAL] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MLD_POLY_OF_POLYVEC_MAP; mld_poly_power2round_hi;
               mld_poly_power2round_lo; mld_poly_of] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MLD_LAZY_COMPUTE_T_COEFF THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]);;

(* All of t1 and t0 packed, from the rows.                                   *)

let MLD_LAZY_COMPUTE_T_PACK_TAC rowth lazyth n proj =
  let nt = mk_small_numeral n in
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN (subst [nt,`n:num`] `j = n * (j DIV n) + j MOD n`)
   SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[lazyth; MOD_LT_EQ; ARITH_EQ] THEN
  MP_TAC(SPECL [`k:num`; `l:num`; `unpack:(num->byte)->num->int32`;
                `p:num`; `r:num`; `sh:num->int32`; `s2b:num->byte`;
                mk_comb(mk_comb(`(DIV)`,`j:num`),nt)] rowth) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    ASM_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC (mk_comb(mk_comb(`(MOD)`,`j:num`),nt)) o
               proj) THEN
    REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REFL_TAC];;

let MLD_LAZY_COMPUTE_T_PACK = prove
 (`!k l (unpack:(num->byte)->num->int32) p r sh s2b.
        (l = 4 \/ l = 5 \/ l = 7) /\ mld_matrix_terminates k l r /\
        (!j. j < 256 * l ==> abs(ival(sh j)) < &94279689) /\
        (!b m. abs(ival(unpack b m)) < &8380417)
        ==> (!j. j < 320 * k
                 ==> mld_polyvec_pack 320 mld_polyt1_pack
                      (mld_polyvec_map mld_poly_power2round_hi
                        (mld_compute_t_lazy l unpack p r sh s2b)) j =
                     mld_polyvec_pack 320 mld_polyt1_pack
                      (mld_polyvec_map mld_poly_power2round_hi
                        (mld_compute_t l unpack p r sh s2b)) j) /\
            (!j. j < 416 * k
                 ==> mld_polyvec_pack 416 mld_polyt0_pack
                      (mld_polyvec_map mld_poly_power2round_lo
                        (mld_compute_t_lazy l unpack p r sh s2b)) j =
                     mld_polyvec_pack 416 mld_polyt0_pack
                      (mld_polyvec_map mld_poly_power2round_lo
                        (mld_compute_t l unpack p r sh s2b)) j)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
   [MLD_LAZY_COMPUTE_T_PACK_TAC MLD_LAZY_COMPUTE_T_ROW
     MLD_COMPUTE_T_LAZY_PACK_T1 320 CONJUNCT1;
    MLD_LAZY_COMPUTE_T_PACK_TAC MLD_LAZY_COMPUTE_T_ROW
     MLD_COMPUTE_T_LAZY_PACK_T0 416 CONJUNCT2]);;

(* ------------------------------------------------------------------------- *)
(* The NTT of polynomials below q is below MLD_NTT_BOUND; signing:           *)
(* w = A y made nonnegative.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_POLY_NTT_BOUND = prove
 (`!x:num->int32.
        (!i. i < 256 ==> abs(ival(x i)) < &8380417)
        ==> !i. i < 256 ==> abs(ival(mld_poly_ntt x i)) < &94279689`,
  MESON_TAC[MLD_POLY_NTT_CONG]);;

let MLD_LAZY_POLYVEC_NTT_BOUND = prove
 (`!n (x:num->int32).
        (!j. j < 256 * n ==> abs(ival(x j)) < &8380417)
        ==> !j. j < 256 * n
                ==> abs(ival(mld_polyvec_map mld_poly_ntt x j)) < &94279689`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `j = 256 * (j DIV 256) + j MOD 256` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[MLD_POLYVEC_MAP_COEFF; MOD_LT_EQ; ARITH_EQ] THEN
  MP_TAC(SPEC `mld_poly_of (x:num->int32) (j DIV 256)`
              MLD_LAZY_POLY_NTT_BOUND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[mld_poly_of] THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `j DIV 256 < n` MP_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC]);;

let MLD_LAZY_SIGN_W = prove
 (`!k l rho (y:num->int32) j.
        (l = 4 \/ l = 5 \/ l = 7) /\ mld_matrix_terminates k l rho /\
        j < 256 * k /\
        (!m. m < 256 * l ==> abs(ival(y m)) < &8380417)
        ==> mld_polyvec_map mld_poly_caddq
             (mld_polyvec_matrix_yvec_lazy l rho y) j =
            mld_sign_w l (mld_polyvec_matrix_expand l rho) y j`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
                        STRIP_ASSUME_TAC(CONJUNCT2 th)) THEN
  SUBGOAL_THEN `j = 256 * (j DIV 256) + j MOD 256` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `j DIV 256 < k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `i = j DIV 256` THEN ABBREV_TAC `m = j MOD 256` THEN
  SUBGOAL_THEN `m < 256` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mld_sign_w; mld_polyvec_matrix_yvec_lazy] THEN
  ASM_SIMP_TAC[MLD_POLYVEC_MAP_COEFF; MLD_POLY_OF_POLYVEC_MAP] THEN
  REWRITE_TAC[mld_poly_caddq] THEN ASM_SIMP_TAC[MLD_POLY_OF_POLYVEC_MAP] THEN
  MATCH_MP_TAC MLD_LAZY_CADDQ_CONG THEN
  MP_TAC(ISPECL
   [`mld_poly_of (mld_polyvec_map mld_poly_reduce
      (mld_polyvec (\i. mld_lazy_acc rho i
         (mld_polyvec_map mld_poly_ntt (y:num->int32)) (l - 1)))) i`;
    `mld_poly_of (mld_polyvec_matrix_pointwise_montgomery l
       (mld_polyvec_matrix_expand l rho)
       (mld_polyvec_map mld_poly_ntt (y:num->int32))) i`]
   MLD_LAZY_INVNTT_CONG) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[MLD_POLY_OF_POLYVEC_MAP] THEN
    REWRITE_TAC[mld_poly_reduce] THEN
    ASM_SIMP_TAC[mld_polyvec_matrix_pointwise_montgomery;
                 MLD_POLY_OF_POLYVEC] THEN
    MP_TAC(SPECL [`k:num`; `l:num`; `rho:num`;
                  `mld_polyvec_map mld_poly_ntt (y:num->int32)`; `i:num`;
                  `t:num`] MLD_LAZY_ROW_CONG) THEN
    REWRITE_TAC[mld_polyvec_matrix_row_lazy; mld_poly_reduce] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MLD_LAZY_POLYVEC_NTT_BOUND THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Verification: row i of A z - T, reduced, transformed back and made        *)
(* nonnegative.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_VERIFY = prove
 (`!k l rho (zhat:num->int32) (u:num->int32) i n.
        (l = 4 \/ l = 5 \/ l = 7) /\ mld_matrix_terminates k l rho /\
        i < k /\ n < 256 /\
        (!j. j < 256 * l ==> abs(ival(zhat j)) < &94279689) /\
        (!m. m < 256 ==> abs(ival(u m)) <= &1077936128)
        ==> mld_poly_caddq
             (mld_poly_invntt_tomont
               (mld_poly_reduce
                 (mld_poly_sub (mld_polyvec_matrix_row_lazy l rho zhat i) u)))
             n =
            mld_poly_caddq
             (mld_poly_invntt_tomont
               (mld_poly_reduce
                 (mld_poly_sub
                   (mld_polyvec_pointwise_acc_montgomery l
                     (\j. mld_polyvec_matrix_expand l rho ((256 * l) * i + j))
                     zhat)
                   u)))
             n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
                        STRIP_ASSUME_TAC(CONJUNCT2 th)) THEN
  REWRITE_TAC[mld_poly_caddq] THEN MATCH_MP_TAC MLD_LAZY_CADDQ_CONG THEN
  SUBGOAL_THEN
   `!m. m < 256
        ==> (ival(mld_poly_reduce
                   (mld_poly_sub (mld_polyvec_matrix_row_lazy l rho zhat i)
                                 u) m) ==
             ival(mld_poly_reduce
                   (mld_poly_sub
                     (mld_polyvec_pointwise_acc_montgomery l
                       (\j. mld_polyvec_matrix_expand l rho
                              ((256 * l) * i + j)) zhat) u) m))
            (mod &8380417) /\
            abs(ival(mld_poly_reduce
                   (mld_poly_sub (mld_polyvec_matrix_row_lazy l rho zhat i)
                                 u) m)) < &8380417 /\
            abs(ival(mld_poly_reduce
                   (mld_poly_sub
                     (mld_polyvec_pointwise_acc_montgomery l
                       (\j. mld_polyvec_matrix_expand l rho
                              ((256 * l) * i + j)) zhat) u) m)) < &8380417`
  MP_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`k:num`; `l:num`; `rho:num`; `zhat:num->int32`; `i:num`;
                  `m:num`] MLD_LAZY_ROW_CONG) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `u:num->int32`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    REWRITE_TAC[mld_poly_reduce; mld_poly_sub] THEN
    ABBREV_TAC `t = (u:num->int32) m` THEN
    ABBREV_TAC `a = mld_polyvec_matrix_row_lazy l rho (zhat:num->int32) i
                     m` THEN
    ABBREV_TAC `b = mld_polyvec_pointwise_acc_montgomery l
                     (\j. mld_polyvec_matrix_expand l rho ((256 * l) * i + j))
                     (zhat:num->int32) m` THEN
    MP_TAC(ISPECL [`a:int32`; `t:int32`] MLD_LAZY_IVAL_WORD_SUB) THEN
    MP_TAC(ISPECL [`b:int32`; `t:int32`] MLD_LAZY_IVAL_WORD_SUB) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPEC `word_sub (a:int32) t` MLD_FIPS204_REDUCE32) THEN
    MP_TAC(ISPEC `word_sub (b:int32) t` MLD_FIPS204_REDUCE32) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; STRIP_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_INT_ARITH_TAC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_int_cong o concl))) THEN
    SPEC_TAC(`&8380417:int`,`q:int`) THEN CONV_TAC INTEGER_RULE;
    DISCH_THEN(MP_TAC o MATCH_MP MLD_LAZY_INVNTT_CONG) THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* The bounds of the unpacked coefficients and of y, by bit-blasting, and    *)
(* of a Montgomery product (2^30 + q / 2 at most).                           *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_ABS_LT = INT_ARITH `!x a:int. abs x < a <=> --a < x /\ x < a`;;

let MLD_LAZY_GEN_BYTES_TAC =
  W(fun (asl,w) ->
    let ts = setify(find_terms (fun t -> type_of t = `:byte` && is_comb t &&
                                 is_var(rator t)) w) in
    MAP_EVERY (fun (t,n) -> SPEC_TAC(t,mk_var("by"^string_of_int n,`:byte`)))
              (zip ts (0--(length ts - 1))));;

let MLD_LAZY_UNPACK_BOUND_TAC defs =
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC defs THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[MLD_LAZY_ABS_LT] THEN
  MLD_LAZY_GEN_BYTES_TAC THEN REPEAT COND_CASES_TAC THEN BITBLAST_TAC;;

let MLD_LAZY_ETA_UNPACK_BOUND = prove
 (`(!b i. abs(ival(mld_polyeta_unpack_2 b i)) < &8380417) /\
   (!b i. abs(ival(mld_polyeta_unpack_4 b i)) < &8380417)`,
  MLD_LAZY_UNPACK_BOUND_TAC [mld_polyeta_unpack_2; mld_polyeta_unpack_4]);;

let MLD_LAZY_Z_UNPACK_BOUND = prove
 (`(!b i. abs(ival(mld_polyz_unpack_17 b i)) < &8380417) /\
   (!b i. abs(ival(mld_polyz_unpack_19 b i)) < &8380417)`,
  MLD_LAZY_UNPACK_BOUND_TAC [mld_polyz_unpack_17; mld_polyz_unpack_19]);;

let MLD_LAZY_SIGN_Y_BOUND = prove
 (`(!rp kappa j.
      abs(ival(mld_sign_y mld_poly_uniform_gamma1_17 rp kappa j))
      < &8380417) /\
   (!rp kappa j.
      abs(ival(mld_sign_y mld_poly_uniform_gamma1_19 rp kappa j))
      < &8380417)`,
  REWRITE_TAC[mld_sign_y; mld_polyvec; mld_poly_uniform_gamma1_17;
              mld_poly_uniform_gamma1_19; MLD_LAZY_Z_UNPACK_BOUND]);;

let MLD_LAZY_IVAL_LE_31 = prove
 (`!x:int32. abs(ival x) <= &2147483648`,
  GEN_TAC THEN MP_TAC(ISPEC `x:int32` IVAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC);;

let MLD_LAZY_POINTWISE_BOUND = prove
 (`!(a:num->int32) b m.
        abs(ival(mld_poly_pointwise_montgomery a b m)) <= &1077936128`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_poly_pointwise_montgomery;
              MLD_MONTGOMERY_REDUCE_POINTWISE] THEN
  MP_TAC(GEN_CONGBOUND_RULE
   [SPEC `(a:num->int32) m` MLD_LAZY_IVAL_LE_31;
    SPEC `(b:num->int32) m` MLD_LAZY_IVAL_LE_31]
   `mldsa_pointwise_montred
      (word_mul (word_sx((a:num->int32) m)) (word_sx((b:num->int32) m)))`) THEN
  INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The coefficients of s1 sampled in key generation are below q in absolute  *)
(* value, when the sampling terminates (mld_keypair_terminates).             *)
(* ------------------------------------------------------------------------- *)

(* The coefficient of an accepted nibble is small, as in the proof of        *)
(* MLD_FIPS204_SAMPLE_REJ_ETA_COEFF of mldsa_native_fips204_sample.ml        *)
(* (which needs FIPS 204).                                                   *)

let MLD_LAZY_REJ_ETA_COEFF_BOUND = prove
 (`!eta t:int32.
        mld_rej_eta_valid eta t
        ==> abs(ival(mld_rej_eta_coeff eta t)) < &8380417`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_rej_eta_valid] THEN
  MP_TAC(prove
   (`!n. n < (if eta = 2 then 15 else 9)
         ==> abs(ival(mld_rej_eta_coeff eta (word n:int32))) < &8380417`,
    REWRITE_TAC[mld_rej_eta_coeff] THEN
    ASM_CASES_TAC `eta = 2` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC INT_REDUCE_CONV)) THEN
  DISCH_THEN(MP_TAC o SPEC `val(t:int32)`) THEN REWRITE_TAC[WORD_VAL]);;

let MLD_LAZY_REJ_ETA_POLY_BOUND = prove
 (`!eta (s:num->byte) i.
        mld_rej_eta_terminates eta s /\ i < 256
        ==> abs(ival(mld_rej_eta_poly eta s i)) < &8380417`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP MLD_REJ_ETA_TERMINATES) THEN
  REWRITE_TAC[mld_rej_eta_poly; mld_rej_eta_list] THEN
  ABBREV_TAC `l = FILTER (mld_rej_eta_valid eta)
                   (list_of_seq (mld_rej_eta_nibble (s:num->byte))
                     (2 * 136 * ((if eta = 2 then 1 else 2) +
                                 mld_poly_uniform_eta_nblocks eta s)))` THEN
  REWRITE_TAC[LENGTH_MAP] THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < LENGTH(l:int32 list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP] THEN MATCH_MP_TAC MLD_LAZY_REJ_ETA_COEFF_BOUND THEN
  SUBGOAL_THEN `MEM (EL i l) (l:int32 list)` MP_TAC THENL
   [MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "l" THEN REWRITE_TAC[MEM_FILTER] THEN SIMP_TAC[]);;

let MLD_LAZY_KEYPAIR_S_BOUND = prove
 (`!eta k l (used:num->bool) seed.
        mld_keypair_terminates eta k l used seed /\ l < 256 /\
        (!n. n < l ==> used n)
        ==> !j. j < 256 * l
                ==> abs(ival(mld_keypair_s eta k l seed j)) < &8380417`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_keypair_terminates] THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_keypair_s; mld_polyvec; mld_poly_uniform_eta] THEN
  MATCH_MP_TAC MLD_LAZY_REJ_ETA_POLY_BOUND THEN
  REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
  SUBGOAL_THEN `j DIV 256 < l` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(j DIV 256):byte) = j DIV 256` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_8] THEN
    SUBGOAL_THEN `j DIV 256 < 256` MP_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;
