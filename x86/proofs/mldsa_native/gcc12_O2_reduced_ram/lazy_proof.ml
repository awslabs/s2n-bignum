(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The results of the lazy matrix products of the reduced-RAM configuration  *)
(* are those of the default one, where they matter: the proofs of the        *)
(* statements of lazy_spec.ml.                                               *)
(*                                                                           *)
(* A lazy row is the reduced sum of the Montgomery products of the entries   *)
(* with the vector, each reduced on its own; the default row is the          *)
(* Montgomery reduction of the sum of the products. Both are congruent       *)
(* modulo q to 2^-32 times the sum of the products, and within q of 0, when  *)
(* the entries are in [0,q) (which they are when their sampling terminates)  *)
(* and the vector is within the bound of the output of the NTT               *)
(* (MLD_ROW_LAZY_CONG). The inverse NTT maps arrays that are congruent       *)
(* coefficient by coefficient and within q of 0 to arrays with the same      *)
(* properties (MLD_POLY_INVNTT_TOMONT_CONG2), as do the reduction of a sum   *)
(* or difference with a third array within q of 0, and mld_caddq maps two    *)
(* words that are congruent and within q of 0 to the same word               *)
(* (MLD_CADDQ_CONG_EQ). Key generation and pk_from_sk add s2 to the inverse  *)
(* NTT of a row and reduce, verification subtracts c t1 2^d and reduces      *)
(* before the inverse NTT, and signing transforms the rows back directly;    *)
(* each then makes the coefficients nonnegative, with the same results.      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/lazy_spec.ml";;
needs "x86/proofs/utils/mldsa_native_fips204_ntt.ml";;
needs "x86/proofs/utils/mldsa_native_fips204_sample.ml";;
needs "x86/proofs/utils/mldsa_native_fips204_round.ml";;
needs "x86/proofs/utils/mldsa_native_fips204_pack.ml";;
needs "x86/proofs/utils/mldsa_native_fips204_sign.ml";;
needs "x86/proofs/utils/mldsa_native_fips204_verify.ml";;

(* ------------------------------------------------------------------------- *)
(* Congruences modulo q by INTEGER_RULE, after generalizing the modulus:     *)
(* INTEGER_RULE fails on some of these goals with the numeral as modulus.    *)
(* ------------------------------------------------------------------------- *)

let MLD_CONG_MOD_Q_TAC =
  SPEC_TAC(`&8380417:int`,`md:int`) THEN CONV_TAC INTEGER_RULE;;

(* ------------------------------------------------------------------------- *)
(* The inverse NTT of congruent arrays within q of 0, and mld_caddq of       *)
(* congruent words within q of 0.                                            *)
(* ------------------------------------------------------------------------- *)

let ARM_MLDSA_INVERSE_NTT_CONG = prove
 (`!(f:num->int) g k.
        (!j. j < 256 ==> (f j == g j) (mod &8380417))
        ==> arm_mldsa_inverse_ntt f k = arm_mldsa_inverse_ntt g k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[arm_mldsa_inverse_ntt; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!a b c n:int. (a == b) (mod n) ==> (c * a == c * b) (mod n)`) THEN
  MATCH_MP_TAC INT_CONG_ISUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!a b c n:int. (a == b) (mod n) ==> (a * c == b * c) (mod n)`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[BITREVERSE8_BOUND]);;

let MLD_POLY_INVNTT_TOMONT_CONG2 = prove
 (`!(x:num->int32) y.
        (!i. i < 256
             ==> abs(ival(x i)) < &8380417 /\ abs(ival(y i)) < &8380417 /\
                 (ival(x i) == ival(y i)) (mod &8380417))
        ==> !i. i < 256
                ==> abs(ival(mld_poly_invntt_tomont x i)) < &8380417 /\
                    abs(ival(mld_poly_invntt_tomont y i)) < &8380417 /\
                    (ival(mld_poly_invntt_tomont x i) ==
                     ival(mld_poly_invntt_tomont y i)) (mod &8380417)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `arm_mldsa_inverse_ntt (ival o (x:num->int32)) i =
    arm_mldsa_inverse_ntt (ival o (y:num->int32)) i`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ARM_MLDSA_INVERSE_NTT_CONG THEN ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  MP_TAC(SPEC `x:num->int32` MLD_POLY_INVNTT_TOMONT_CONG) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(MP_TAC o SPEC `i:num`)] THEN
  MP_TAC(SPEC `y:num->int32` MLD_POLY_INVNTT_TOMONT_CONG) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(MP_TAC o SPEC `i:num`)] THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`arm_mldsa_inverse_ntt (ival o (y:num->int32)) i`,`t:int`) THEN
  GEN_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `(x:int == y) (mod n)`) o concl))) THEN
  MLD_CONG_MOD_Q_TAC);;

let MLD_CADDQ_CONG_EQ = prove
 (`!a b:int32.
        abs(ival a) < &8380417 /\ abs(ival b) < &8380417 /\
        (ival a == ival b) (mod &8380417)
        ==> mld_caddq a = mld_caddq b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IVAL_EQ] THEN
  ASM_SIMP_TAC[MLD_CADDQ_REM; INT_REM_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The reduction of a word, and of the sum or difference of two words, one   *)
(* of two that are congruent, with a third, all within q of 0.               *)
(* ------------------------------------------------------------------------- *)

let MLD_REDUCE32_CONG = prove
 (`!a:int32.
        ival a <= &2143289343
        ==> (ival(mld_reduce32 a) == ival a) (mod &8380417) /\
            --(&6283009) <= ival(mld_reduce32 a) /\
            ival(mld_reduce32 a) < &6283009`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`(\i:num. a):num->int32`; `0`] MLD_FIPS204_POLY_REDUCE) THEN
  REWRITE_TAC[mld_poly_reduce]);;

let MLD_REDUCE32_ADD_SUB_CONG = prove
 (`!a b t:int32.
        abs(ival a) < &8380417 /\ abs(ival b) < &8380417 /\
        (ival a == ival b) (mod &8380417) /\ abs(ival t) < &8380417
        ==> (abs(ival(mld_reduce32(word_add a t))) < &8380417 /\
             abs(ival(mld_reduce32(word_add b t))) < &8380417 /\
             (ival(mld_reduce32(word_add a t)) ==
              ival(mld_reduce32(word_add b t))) (mod &8380417)) /\
            (abs(ival(mld_reduce32(word_sub a t))) < &8380417 /\
             abs(ival(mld_reduce32(word_sub b t))) < &8380417 /\
             (ival(mld_reduce32(word_sub a t)) ==
              ival(mld_reduce32(word_sub b t))) (mod &8380417))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ival(word_add a t:int32) = ival a + ival t /\
    ival(word_add b t:int32) = ival b + ival t /\
    ival(word_sub a t:int32) = ival a - ival t /\
    ival(word_sub b t:int32) = ival b - ival t`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MLD_FIPS204_IVAL_TAC; ALL_TAC] THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t MLD_REDUCE32_CONG))
   [`word_add a t:int32`; `word_add b t:int32`;
    `word_sub a t:int32`; `word_sub b t:int32`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(ANTS_TAC THENL [ASM_INT_ARITH_TAC; STRIP_TAC]) THEN
  REPEAT CONJ_TAC THEN TRY ASM_INT_ARITH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `(x:int == y) (mod n)`) o concl))) THEN
  MLD_CONG_MOD_Q_TAC);;

let MLD_REDUCE32_ADD_CONG = prove
 (`!a b t:int32.
        abs(ival a) < &8380417 /\ abs(ival b) < &8380417 /\
        (ival a == ival b) (mod &8380417) /\ abs(ival t) < &8380417
        ==> abs(ival(mld_reduce32(word_add a t))) < &8380417 /\
            abs(ival(mld_reduce32(word_add b t))) < &8380417 /\
            (ival(mld_reduce32(word_add a t)) ==
             ival(mld_reduce32(word_add b t))) (mod &8380417)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MLD_REDUCE32_ADD_SUB_CONG) THEN SIMP_TAC[]);;

let MLD_REDUCE32_SUB_CONG = prove
 (`!a b t:int32.
        abs(ival a) < &8380417 /\ abs(ival b) < &8380417 /\
        (ival a == ival b) (mod &8380417) /\ abs(ival t) < &8380417
        ==> abs(ival(mld_reduce32(word_sub a t))) < &8380417 /\
            abs(ival(mld_reduce32(word_sub b t))) < &8380417 /\
            (ival(mld_reduce32(word_sub a t)) ==
             ival(mld_reduce32(word_sub b t))) (mod &8380417)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MLD_REDUCE32_ADD_SUB_CONG) THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The norm check of any polynomial or vector (not only of one within the    *)
(* range of the reduction, as in MLD_FIPS204_POLY_CHKNORM_ABS): zero only if *)
(* all coefficients are below the bound in absolute value.                   *)
(* ------------------------------------------------------------------------- *)

let MLD_POLY_CHKNORM_IMP = prove
 (`!(a:num->int32) B.
        0 < B /\ B < 2147483648 /\ mld_poly_chknorm a (word B) = word 0
        ==> !i. i < 256 ==> abs(ival(a i)) < &B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0:int < &B /\ &B:int < &2147483648` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(word B:int32) = &B` ASSUME_TAC THENL
   [MP_TAC(ISPEC `word B:int32` IVAL_EQ_VAL) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `B < 2147483648 ==> B < 4294967296`];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(a:num->int32) i` IVAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ival(word_sub (word_sub (word B) (word 1))
                  (mld_ct_abs((a:num->int32) i))) =
    ival(word B:int32) - &1 - abs(ival(a i))`
  ASSUME_TAC THENL
   [REWRITE_TAC[mld_ct_abs] THEN COND_CASES_TAC THENL
     [TRANS_TAC EQ_TRANS
       `ival(word B:int32) - &1 - --ival((a:num->int32) i)` THEN
      CONJ_TAC THENL [MLD_FIPS204_IVAL_TAC; ASM_INT_ARITH_TAC];
      TRANS_TAC EQ_TRANS
       `ival(word B:int32) - &1 - ival((a:num->int32) i)` THEN
      CONJ_TAC THENL [MLD_FIPS204_IVAL_TAC; ASM_INT_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    can (find_term ((=) `mld_poly_chknorm`)) (concl th))) THEN
  REWRITE_TAC[mld_poly_chknorm] THEN
  COND_CASES_TAC THENL [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(K ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

let MLD_POLYVEC_CHKNORM_IMP = prove
 (`!n (x:num->int32) B.
        0 < B /\ B < 2147483648 /\ mld_polyvec_chknorm n x (word B) = word 0
        ==> !j. j < 256 * n ==> abs(ival(x j)) < &B`,
  INDUCT_TAC THEN REWRITE_TAC[mld_polyvec_chknorm; MULT_CLAUSES; LT] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_OR_EQ_0] THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `j < 256 * n` THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`x:num->int32`; `B:num`]) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`mld_poly_of (x:num->int32) n`; `B:num`]
                  MLD_POLY_CHKNORM_IMP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j - 256 * n`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[mld_poly_of] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(j < 256 * n) ==> 256 * n + j - 256 * n = j`]]);;

(* ------------------------------------------------------------------------- *)
(* Bounds of the vectors that are multiplied by the matrix: the unpacked     *)
(* polynomials of s1 and s2 of any secret key, those of s1 sampled in key    *)
(* generation, and the NTT of a vector within q of 0.                        *)
(* ------------------------------------------------------------------------- *)

let MLD_POLYETA_UNPACK_2_BOUND = prove
 (`!b i. i < 256 ==> abs(ival(mld_polyeta_unpack_2 b i)) < &8380417`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLD_FIPS204_POLYETA_UNPACK_2] THEN
  MP_TAC(SPECL [`3`; `list_of_seq (b:num->byte) 96`; `i:num`]
               MLDSA_FIELD_BOUND) THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC);;

let MLD_POLYETA_UNPACK_4_BOUND = prove
 (`!b i. i < 256 ==> abs(ival(mld_polyeta_unpack_4 b i)) < &8380417`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLD_FIPS204_POLYETA_UNPACK_4] THEN
  MP_TAC(SPECL [`4`; `list_of_seq (b:num->byte) 128`; `i:num`]
               MLDSA_FIELD_BOUND) THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC);;

let MLD_POLYVEC_UNPACK_BOUND = prove
 (`!P (unpack:(num->byte)->num->int32) b j.
        (!b c. c < 256 ==> abs(ival(unpack b c)) < &8380417)
        ==> abs(ival(mld_polyvec_unpack P unpack b j)) < &8380417`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `j = 256 * (j DIV 256) + j MOD 256` SUBST1_TAC THENL
   [ARITH_TAC; ASM_SIMP_TAC[MLD_POLYVEC_UNPACK_COEFF; MOD_LT_EQ; ARITH_EQ]]);;

let MLD_KEYPAIR_S_BOUND = prove
 (`!eta k l used seed j.
        mld_keypair_terminates eta k l used seed /\
        (!n. n < l ==> used n) /\ l < 256 /\ j < 256 * l
        ==> abs(ival(mld_keypair_s eta k l seed j)) < &8380417`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_keypair_terminates] THEN STRIP_TAC THEN
  SUBGOAL_THEN `j DIV 256 < l` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `j = 256 * (j DIV 256) + j MOD 256` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[mld_keypair_s; MLD_POLYVEC_COEFF; MOD_LT_EQ; ARITH_EQ] THEN
  MP_TAC(SPECL [`eta:num`; `mld_keypair_rhoprime k l seed`;
                `word(j DIV 256):byte`; `j MOD 256`]
               MLD_FIPS204_POLY_UNIFORM_ETA_BOUND) THEN
  SUBGOAL_THEN `val(word(j DIV 256):byte) = j DIV 256` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `mld_rej_eta_terminates`)) (concl th))) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    COND_CASES_TAC THEN INT_ARITH_TAC]);;

let MLD_POLYVEC_NTT_BOUND = prove
 (`!l (x:num->int32).
        (!j. j < 256 * l ==> abs(ival(x j)) < &8380417)
        ==> !j. j < 256 * l
                ==> abs(ival(mld_polyvec_map mld_poly_ntt x j)) < &94279689`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `j = 256 * (j DIV 256) + j MOD 256` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[MLD_POLYVEC_MAP_COEFF; MOD_LT_EQ; ARITH_EQ] THEN
  MP_TAC(ISPEC `mld_poly_of (x:num->int32) (j DIV 256)`
               MLD_FIPS204_POLY_NTT) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[mld_poly_of] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `j DIV 256 < l` MP_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ]; ASM_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `j MOD 256`) THEN
    SIMP_TAC[MOD_LT_EQ; ARITH_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* The entries of the matrix are in [0,q) when the sampling terminates.      *)
(* ------------------------------------------------------------------------- *)

let MLD_REJ_UNIFORM_POLY_LT = prove
 (`!(s:num->byte) i.
        mld_rej_uniform_terminates s /\ i < 256
        ==> val(mld_rej_uniform_poly s i) < 8380417`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MLD_REJ_UNIFORM_TERMINATES) THEN
  REWRITE_TAC[mld_rej_uniform_poly] THEN
  ABBREV_TAC
   `L = mld_rej_uniform_list (s:num->byte)
         (280 + 56 * mld_poly_uniform_nblocks s)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `MEM (EL i L) (L:int32 list)` MP_TAC THENL
   [MATCH_MP_TAC MEM_EL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "L" THEN REWRITE_TAC[mld_rej_uniform_list; MEM_FILTER] THEN
  SIMP_TAC[]);;

let MLD_MATRIX_ENTRY_BOUND = prove
 (`!k l rho i j c.
        mld_matrix_terminates k l rho /\ i < k /\ j < l /\ c < 256
        ==> &0 <= ival(mld_matrix_entry rho i j c) /\
            ival(mld_matrix_entry rho i j c) < &8380417`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(mld_matrix_entry rho i j c) < 8380417` MP_TAC THENL
   [REWRITE_TAC[mld_matrix_entry; mld_poly_uniform] THEN
    MATCH_MP_TAC MLD_REJ_UNIFORM_POLY_LT THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[mld_matrix_terminates]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SPEC_TAC(`mld_matrix_entry rho i j c`,`w:int32`) THEN GEN_TAC THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `ival(w:int32) = &(val w)` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_EQ_VAL THEN REWRITE_TAC[DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[INT_POS; INT_OF_NUM_LT]]);;

(* ------------------------------------------------------------------------- *)
(* The lazy sum of the products of the entries of row i with v, for columns  *)
(* 0 to n (n <= 6), is congruent to 2^-32 times the sum of the products and  *)
(* below (n + 1) q in absolute value.                                        *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_ACC_STEP = prove
 (`!(a:int32) b x y m.
        (ival a == x) (mod &8380417) /\ abs(ival a) < &m * &8380417 /\
        (ival b == y) (mod &8380417) /\ abs(ival b) < &8380417 /\ m <= 7
        ==> (ival(word_add a b) == x + y) (mod &8380417) /\
            abs(ival(word_add a b)) < &(SUC m) * &8380417`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&m:int <= &7` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(word_add a b:int32) = ival a + ival b` SUBST1_TAC THENL
   [MLD_FIPS204_IVAL_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (can (term_match []
      `(x:int == y) (mod n)`) o concl))) THEN
    MLD_CONG_MOD_Q_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN ASM_INT_ARITH_TAC]);;

let MLD_LAZY_ACC_CONG = prove
 (`!n rho (v:num->int32) i c.
        c < 256 /\ n <= 6 /\
        (!j. j <= n
             ==> &0 <= ival(mld_matrix_entry rho i j c) /\
                 ival(mld_matrix_entry rho i j c) < &8380417) /\
        (!j. j <= n ==> abs(ival(v(256 * j + c))) < &94279689)
        ==> (ival(mld_lazy_acc rho v i n c) ==
             isum (0..n)
              (\j. ival(mld_matrix_entry rho i j c) * ival(v(256 * j + c))) *
             &(inverse_mod 8380417 4294967296)) (mod &8380417) /\
            abs(ival(mld_lazy_acc rho v i n c)) < &(SUC n) * &8380417`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mld_lazy_acc] THENL
   [MP_TAC(ISPECL [`mld_matrix_entry rho i 0`;
                   `mld_poly_of (v:num->int32) 0`; `c:num`]
                  MLD_POLY_POINTWISE_MONTGOMERY_CONG) THEN
    REWRITE_TAC[mld_poly_of; MULT_CLAUSES; ADD_CLAUSES] THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `0` o
        check (fun th -> free_in `v:num->int32` (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
      REWRITE_TAC[LE_REFL; MULT_CLAUSES; ADD_CLAUSES] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[mldsa_pointwise; o_THM; INT_CONG_RREM; NUMSEG_SING;
                ISUM_SING; MULT_CLAUSES; ADD_CLAUSES; ARITH] THEN
    REWRITE_TAC[INT_MUL_ASSOC; INT_MUL_LID] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`rho:num`; `v:num->int32`; `i:num`;
                                `c:num`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`mld_matrix_entry rho i (SUC n)`;
                 `mld_poly_of (v:num->int32) (SUC n)`; `c:num`]
                MLD_POLY_POINTWISE_MONTGOMERY_CONG) THEN
  REWRITE_TAC[mld_poly_of] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `SUC n` o
      check (fun th -> free_in `v:num->int32` (concl th) &&
                       is_forall(concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC n` o check (is_forall o concl)) THEN
    REWRITE_TAC[LE_REFL] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mldsa_pointwise; o_THM; INT_CONG_RREM] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_MUL_ASSOC]) THEN
  REWRITE_TAC[mld_poly_add; ISUM_CLAUSES_NUMSEG; LE_0; INT_ADD_RDISTRIB] THEN
  MATCH_MP_TAC MLD_LAZY_ACC_STEP THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A lazy row and the default row of the product of the matrix with a        *)
(* vector within the NTT bound, for l = 4, 5 and 7 columns: congruent and    *)
(* within q of 0.                                                            *)
(* ------------------------------------------------------------------------- *)

let MLD_ROW_LAZY_CONG_STMT l =
  subst [mk_small_numeral l,`l:num`]
  `!k rho (v:num->int32) i c.
        mld_matrix_terminates k l rho /\ i < k /\ c < 256 /\
        (!j. j < 256 * l ==> abs(ival(v j)) < &94279689)
        ==> (ival(mld_polyvec_matrix_row_lazy l rho v i c) ==
             ival(mld_polyvec_pointwise_acc_montgomery l
                   (\j. mld_polyvec_matrix_expand l rho ((256 * l) * i + j))
                   v c)) (mod &8380417) /\
            abs(ival(mld_polyvec_matrix_row_lazy l rho v i c)) < &8380417 /\
            abs(ival(mld_polyvec_pointwise_acc_montgomery l
                      (\j. mld_polyvec_matrix_expand l rho
                             ((256 * l) * i + j))
                      v c)) < &8380417`;;

let MLD_ROW_LAZY_CONG_TAC acccong l =
  let lt = mk_small_numeral l and l1 = mk_small_numeral (l - 1) in
  let sl = subst [lt,`l:num`] and sl1 = subst [lt,`l:num`; l1,`m:num`] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   (sl1 `!j. j <= m
             ==> &0 <= ival(mld_matrix_entry rho i j c) /\
                 ival(mld_matrix_entry rho i j c) < &8380417`)
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC MLD_MATRIX_ENTRY_BOUND THEN
    MAP_EVERY EXISTS_TAC [`k:num`; lt] THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [l1; `rho:num`; `v:num->int32`; `i:num`; `c:num`]
               MLD_LAZY_ACC_CONG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN STRIP_TAC] THEN
  MP_TAC(SPECL
   [sl `\j. mld_polyvec_matrix_expand l rho ((256 * l) * i + j)`;
    `v:num->int32`; `c:num`] acccong) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `j:num` THEN
    DISCH_TAC THENL
     [SUBGOAL_THEN
       (sl `(256 * l) * i + j = (256 * l) * i + 256 * (j DIV 256) + j MOD 256`)
      SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) MLD_POLYVEC_MATRIX_EXPAND_ENTRY o
        rand o rand o lhand o snd) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      MP_TAC(SPECL [`k:num`; lt; `rho:num`; `i:num`; `j DIV 256`;
                    `j MOD 256`] MLD_MATRIX_ENTRY_BOUND) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; INT_ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[MLDSA_POINTWISE_ACC_ISUM; o_THM; INT_CONG_RREM] THEN
  STRIP_TAC THEN
  REWRITE_TAC[mld_polyvec_matrix_row_lazy] THEN
  CONV_TAC(DEPTH_CONV NUM_SUB_CONV) THEN
  MP_TAC(SPECL [sl1 `mld_lazy_acc rho (v:num->int32) i m`; `c:num`]
               MLD_FIPS204_POLY_REDUCE) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_INT_ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `(ival(mld_polyvec_pointwise_acc_montgomery l u v c) == x) (mod n)`) o
    concl)) THEN
  SUBGOAL_THEN
   (sl1 `isum {j | j < l}
          (\j. ival(mld_polyvec_matrix_expand l rho
                     ((256 * l) * i + c + 256 * j)) *
               ival((v:num->int32)(c + 256 * j))) =
         isum (0..m)
          (\j. ival(mld_matrix_entry rho i j c) * ival(v(256 * j + c)))`)
  SUBST1_TAC THENL
   [REWRITE_TAC[NUMSEG_LT; ARITH_EQ] THEN
    CONV_TAC(DEPTH_CONV NUM_SUB_CONV) THEN
    MATCH_MP_TAC ISUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[ARITH_RULE `c + 256 * j = 256 * j + c`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MLD_POLYVEC_MATRIX_EXPAND_ENTRY o
      rand o lhand o lhand o snd) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REFL_TAC;
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `(x:int == y) (mod n)`) o concl))) THEN
  MLD_CONG_MOD_Q_TAC;;

let MLD_ROW_LAZY_CONG_L4 = prove
 (MLD_ROW_LAZY_CONG_STMT 4,
  MLD_ROW_LAZY_CONG_TAC MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L4_CONG 4);;

let MLD_ROW_LAZY_CONG_L5 = prove
 (MLD_ROW_LAZY_CONG_STMT 5,
  MLD_ROW_LAZY_CONG_TAC MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L5_CONG 5);;

let MLD_ROW_LAZY_CONG_L7 = prove
 (MLD_ROW_LAZY_CONG_STMT 7,
  MLD_ROW_LAZY_CONG_TAC MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L7_CONG 7);;

let MLD_ROW_LAZY_CONG = prove
 (`!k l rho (v:num->int32) i c.
        (l = 4 \/ l = 5 \/ l = 7) /\
        mld_matrix_terminates k l rho /\ i < k /\ c < 256 /\
        (!j. j < 256 * l ==> abs(ival(v j)) < &94279689)
        ==> (ival(mld_polyvec_matrix_row_lazy l rho v i c) ==
             ival(mld_polyvec_pointwise_acc_montgomery l
                   (\j. mld_polyvec_matrix_expand l rho ((256 * l) * i + j))
                   v c)) (mod &8380417) /\
            abs(ival(mld_polyvec_matrix_row_lazy l rho v i c)) < &8380417 /\
            abs(ival(mld_polyvec_pointwise_acc_montgomery l
                      (\j. mld_polyvec_matrix_expand l rho
                             ((256 * l) * i + j))
                      v c)) < &8380417`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b ==> c <=> a ==> b ==> c`] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  MAP_FIRST MATCH_ACCEPT_TAC
   [MLD_ROW_LAZY_CONG_L4; MLD_ROW_LAZY_CONG_L5; MLD_ROW_LAZY_CONG_L7]);;

(* ------------------------------------------------------------------------- *)
(* Key generation and pk_from_sk: t computed with the lazy rows, packed as   *)
(* t1 and t0, is the same as with the default rows.                          *)
(* ------------------------------------------------------------------------- *)

let MLD_COMPUTE_T_LAZY_EQ = prove
 (`!k l (unpack:(num->byte)->num->int32) p rho sh s2b T1 T0.
        (l = 4 \/ l = 5 \/ l = 7) /\ mld_matrix_terminates k l rho /\
        (!j. j < 256 * l ==> abs(ival(sh j)) < &94279689) /\
        (!b c. c < 256 ==> abs(ival(unpack b c)) < &8380417) /\
        T1 = 320 * k /\ T0 = 416 * k
        ==> (!j. j < T1
                 ==> mld_polyvec_pack 320 mld_polyt1_pack
                      (mld_polyvec_map mld_poly_power2round_hi
                        (mld_compute_t_lazy l unpack p rho sh s2b)) j =
                     mld_polyvec_pack 320 mld_polyt1_pack
                      (mld_polyvec_map mld_poly_power2round_hi
                        (mld_compute_t l unpack p rho sh s2b)) j) /\
            (!j. j < T0
                 ==> mld_polyvec_pack 416 mld_polyt0_pack
                      (mld_polyvec_map mld_poly_power2round_lo
                        (mld_compute_t_lazy l unpack p rho sh s2b)) j =
                     mld_polyvec_pack 416 mld_polyt0_pack
                      (mld_polyvec_map mld_poly_power2round_lo
                        (mld_compute_t l unpack p rho sh s2b)) j)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM SUBST1_TAC) THEN
  SUBGOAL_THEN
   `!i c. i < k /\ c < 256
          ==> mld_caddq
               (mld_reduce32
                 (word_add
                   (mld_poly_invntt_tomont
                     (mld_polyvec_matrix_row_lazy l rho sh i) c)
                   ((unpack:(num->byte)->num->int32)
                     (\t. (s2b:num->byte)(p * i + t)) c))) =
              mld_caddq
               (mld_reduce32
                 (word_add
                   (mld_poly_invntt_tomont
                     (mld_polyvec_pointwise_acc_montgomery l
                       (\j. mld_polyvec_matrix_expand l rho
                              ((256 * l) * i + j)) sh) c)
                   (unpack (\t. s2b(p * i + t)) c)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`mld_polyvec_matrix_row_lazy l rho (sh:num->int32) i`;
      `mld_polyvec_pointwise_acc_montgomery l
        (\j. mld_polyvec_matrix_expand l rho ((256 * l) * i + j))
        (sh:num->int32)`] MLD_POLY_INVNTT_TOMONT_CONG2) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `c':num` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`k:num`; `l:num`; `rho:num`; `sh:num->int32`; `i:num`;
                    `c':num`] MLD_ROW_LAZY_CONG) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPEC `c:num`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC] THEN
    MATCH_MP_TAC MLD_CADDQ_CONG_EQ THEN
    MATCH_MP_TAC MLD_REDUCE32_ADD_CONG THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THENL
   [SUBGOAL_THEN `j = 320 * (j DIV 320) + j MOD 320` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[MLD_COMPUTE_T_PACK_T1; MLD_COMPUTE_T_LAZY_PACK_T1;
             MOD_LT_EQ; ARITH_EQ] THEN
    MATCH_MP_TAC MLD_POLYT1_PACK_LOCAL THEN SIMP_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    X_GEN_TAC `c:num` THEN DISCH_TAC THEN
    REWRITE_TAC[mld_poly_power2round_hi; mld_poly_caddq; mld_poly_reduce;
                mld_poly_add] THEN
    AP_TERM_TAC;
    SUBGOAL_THEN `j = 416 * (j DIV 416) + j MOD 416` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[MLD_COMPUTE_T_PACK_T0; MLD_COMPUTE_T_LAZY_PACK_T0;
             MOD_LT_EQ; ARITH_EQ] THEN
    MATCH_MP_TAC MLD_POLYT0_PACK_LOCAL THEN SIMP_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    X_GEN_TAC `c:num` THEN DISCH_TAC THEN
    REWRITE_TAC[mld_poly_power2round_lo; mld_poly_caddq; mld_poly_reduce;
                mld_poly_add] THEN
    AP_TERM_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Signing: w = invNTT(A * NTT(y)) made nonnegative, for y sampled by g1     *)
(* within q of 0.                                                            *)
(* ------------------------------------------------------------------------- *)

let MLD_SIGN_W_LAZY_EQ = prove
 (`!k l (g1:num->int16->num->int32) rho rhoprime kappa i.
        (l = 4 \/ l = 5 \/ l = 7) /\ mld_matrix_terminates k l rho /\
        (!seed nonce c. c < 256 ==> abs(ival(g1 seed nonce c)) < &8380417) /\
        i < 256 * k
        ==> mld_polyvec_map mld_poly_caddq
             (mld_yvec_lazy_w l g1 rho rhoprime kappa) i =
            mld_sign_w l (mld_polyvec_matrix_expand l rho)
             (mld_sign_y g1 rhoprime kappa) i`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[mld_sign_w; mld_sign_y; mld_yvec_lazy_w;
              mld_polyvec_matrix_pointwise_montgomery_lazy;
              mld_polyvec_matrix_pointwise_montgomery] THEN
  ABBREV_TAC
   `yhat = mld_polyvec_map mld_poly_ntt
            (mld_polyvec (\j. (g1:num->int16->num->int32) rhoprime
                                (word(kappa + j))))` THEN
  SUBGOAL_THEN
   `!j. j < 256 * l ==> abs(ival((yhat:num->int32) j)) < &94279689`
  ASSUME_TAC THENL
   [EXPAND_TAC "yhat" THEN MATCH_MP_TAC MLD_POLYVEC_NTT_BOUND THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `j = 256 * (j DIV 256) + j MOD 256` SUBST1_TAC THENL
     [ARITH_TAC; ASM_SIMP_TAC[MLD_POLYVEC_COEFF; MOD_LT_EQ; ARITH_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `i DIV 256 < k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `i = 256 * (i DIV 256) + i MOD 256` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[MLD_POLYVEC_MAP_COEFF; MOD_LT_EQ; ARITH_EQ] THEN
  REWRITE_TAC[mld_poly_caddq] THEN
  SIMP_TAC[MLD_POLY_OF_POLYVEC_MAP; MOD_LT_EQ; ARITH_EQ] THEN
  MATCH_MP_TAC MLD_CADDQ_CONG_EQ THEN
  MP_TAC(ISPECL
   [`mld_poly_of
      (mld_polyvec (\i. mld_polyvec_matrix_row_lazy l rho
                          (yhat:num->int32) i)) (i DIV 256)`;
    `mld_poly_of
      (mld_polyvec (\i. mld_polyvec_pointwise_acc_montgomery l
                          (\j. mld_polyvec_matrix_expand l rho
                                 ((256 * l) * i + j))
                          (yhat:num->int32))) (i DIV 256)`]
   MLD_POLY_INVNTT_TOMONT_CONG2) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `c:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[MLD_POLY_OF_POLYVEC] THEN
    MP_TAC(SPECL [`k:num`; `l:num`; `rho:num`; `yhat:num->int32`;
                  `i DIV 256`; `c:num`] MLD_ROW_LAZY_CONG) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `i MOD 256`) THEN
    SIMP_TAC[MOD_LT_EQ; ARITH_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Verification: row i of w1' with the lazy row of A * NTT(z), once the norm *)
(* of z is checked, given that the NTT of the challenge is within the NTT    *)
(* bound and that the use of the hints is coefficient by coefficient.        *)
(* ------------------------------------------------------------------------- *)

let MLD_VERIFY_W1_LAZY_EQ = prove
 (`!k l bnd (uh:(num->int32)->(num->int32)->num->int32) rho z
    (cphat:num->int32) pk omega hb i c.
        (l = 4 \/ l = 5 \/ l = 7) /\ mld_matrix_terminates k l rho /\
        (!a b h c. a c = b c ==> uh a h c = uh b h c) /\
        0 < bnd /\ bnd <= 8380417 /\
        mld_polyvec_chknorm l z (word bnd) = word 0 /\
        (!c. c < 256 ==> abs(ival(cphat c)) < &94279689) /\
        i < k /\ c < 256
        ==> mld_verify_w1_lazy l uh rho (mld_polyvec_map mld_poly_ntt z) cphat
                               pk omega hb i c =
            mld_verify_w1 l uh rho (mld_polyvec_map mld_poly_ntt z) cphat
                          pk omega hb i c`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[mld_verify_w1; mld_verify_w1_lazy] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[mld_poly_caddq] THEN
  MATCH_MP_TAC MLD_CADDQ_CONG_EQ THEN
  ABBREV_TAC `zhat = mld_polyvec_map mld_poly_ntt (z:num->int32)` THEN
  ABBREV_TAC
   `P = mld_poly_pointwise_montgomery
         (mld_poly_ntt (mld_poly_shiftl
           (mld_polyt1_unpack (\j. (pk:num->byte)(32 + 320 * i + j)))))
         (cphat:num->int32)` THEN
  SUBGOAL_THEN
   `!j. j < 256 * l ==> abs(ival((zhat:num->int32) j)) < &94279689`
  ASSUME_TAC THENL
   [EXPAND_TAC "zhat" THEN MATCH_MP_TAC MLD_POLYVEC_NTT_BOUND THEN
    MP_TAC(SPECL [`l:num`; `z:num->int32`; `bnd:num`]
                 MLD_POLYVEC_CHKNORM_IMP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&bnd:int <= &8380417` MP_TAC THENL
     [ASM_REWRITE_TAC[INT_OF_NUM_LE]; INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c. c < 256 ==> abs(ival((P:num->int32) c)) < &8380417`
  ASSUME_TAC THENL
   [X_GEN_TAC `c':num` THEN DISCH_TAC THEN EXPAND_TAC "P" THEN
    MP_TAC(ISPECL
     [`mld_poly_ntt (mld_poly_shiftl
        (mld_polyt1_unpack (\j. (pk:num->byte)(32 + 320 * i + j))))`;
      `cphat:num->int32`; `c':num`] MLD_POLY_POINTWISE_MONTGOMERY_CONG) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_SIMP_TAC[] THEN
    MP_TAC(SPECL [`pk:num->byte`; `k:num`; `i:num`] MLD_FIPS204_VERIFY_T1) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`mld_poly_reduce
      (mld_poly_sub (mld_polyvec_matrix_row_lazy l rho (zhat:num->int32) i)
                    (P:num->int32))`;
    `mld_poly_reduce
      (mld_poly_sub
        (mld_polyvec_pointwise_acc_montgomery l
          (\j. mld_polyvec_matrix_expand l rho ((256 * l) * i + j))
          (zhat:num->int32))
        (P:num->int32))`] MLD_POLY_INVNTT_TOMONT_CONG2) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `c':num` THEN DISCH_TAC THEN
    REWRITE_TAC[mld_poly_reduce; mld_poly_sub] THEN
    MP_TAC(SPECL [`k:num`; `l:num`; `rho:num`; `zhat:num->int32`; `i:num`;
                  `c':num`] MLD_ROW_LAZY_CONG) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC MLD_REDUCE32_SUB_CONG THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(MP_TAC o SPEC `c:num`) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The statements of lazy_spec.ml.                                           *)
(* ------------------------------------------------------------------------- *)

let MLD_KEYPAIR_T_LAZY_TAC unpackbound k used =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_keypair_terminates_44; mld_keypair_terminates_65;
              mld_keypair_terminates_87] THEN
  STRIP_TAC THEN REWRITE_TAC[mld_keypair_t] THEN
  MATCH_MP_TAC MLD_COMPUTE_T_LAZY_EQ THEN EXISTS_TAC k THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MLD_POLYVEC_NTT_BOUND THEN X_GEN_TAC `j:num` THEN
    DISCH_TAC THEN MATCH_MP_TAC MLD_KEYPAIR_S_BOUND THEN
    EXISTS_TAC used THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    SIMP_TAC[unpackbound];
    ARITH_TAC;
    ARITH_TAC];;

let MLD_PK_FROM_SK_T_LAZY_TAC unpackbound k =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mld_pk_from_sk_t] THEN
  MATCH_MP_TAC MLD_COMPUTE_T_LAZY_EQ THEN EXISTS_TAC k THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MLD_POLYVEC_NTT_BOUND THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[mld_sk_s1] THEN MATCH_MP_TAC MLD_POLYVEC_UNPACK_BOUND THEN
    SIMP_TAC[unpackbound];
    SIMP_TAC[unpackbound];
    ARITH_TAC;
    ARITH_TAC];;

let MLD_VERIFY_W1_LAZY_TAC usehint k bnd tau ctlen =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLD_VERIFY_W1_LAZY_EQ THEN
  MAP_EVERY EXISTS_TAC [k; bnd] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[usehint] THEN SIMP_TAC[];
    MP_TAC(SPECL [tau; ctlen; `cc:num`] MLD_FIPS204_VERIFY_CHALLENGE) THEN
    ASM_SIMP_TAC[]];;

let MLD_SIGN_W_LAZY_TAC g1bound k =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLD_SIGN_W_LAZY_EQ THEN
  EXISTS_TAC k THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`seed:num`; `nonce:int16`; `c:num`] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`seed:num`; `nonce:int16`; `c:num`] g1bound) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ASM_ARITH_TAC];;

let MLD_KEYPAIR_T_LAZY_44 = prove
 (MLD_KEYPAIR_T_LAZY_44_STMT,
  MLD_KEYPAIR_T_LAZY_TAC MLD_POLYETA_UNPACK_2_BOUND `4` `\n. n < 8`);;

let MLD_PK_FROM_SK_T_LAZY_44 = prove
 (MLD_PK_FROM_SK_T_LAZY_44_STMT,
  MLD_PK_FROM_SK_T_LAZY_TAC MLD_POLYETA_UNPACK_2_BOUND `4`);;

let MLD_VERIFY_W1_LAZY_44 = prove
 (MLD_VERIFY_W1_LAZY_44_STMT,
  MLD_VERIFY_W1_LAZY_TAC mld_poly_use_hint_88 `4` `130994` `39` `32`);;

let MLD_SIGN_W_LAZY_44 = prove
 (MLD_SIGN_W_LAZY_44_STMT,
  MLD_SIGN_W_LAZY_TAC MLD_FIPS204_SIGN_GAMMA1_17_BOUND `4`);;

let MLD_KEYPAIR_T_LAZY_65 = prove
 (MLD_KEYPAIR_T_LAZY_65_STMT,
  MLD_KEYPAIR_T_LAZY_TAC MLD_POLYETA_UNPACK_4_BOUND `6`
   `\n. n < 11 \/ n = 255`);;

let MLD_PK_FROM_SK_T_LAZY_65 = prove
 (MLD_PK_FROM_SK_T_LAZY_65_STMT,
  MLD_PK_FROM_SK_T_LAZY_TAC MLD_POLYETA_UNPACK_4_BOUND `6`);;

let MLD_VERIFY_W1_LAZY_65 = prove
 (MLD_VERIFY_W1_LAZY_65_STMT,
  MLD_VERIFY_W1_LAZY_TAC mld_poly_use_hint_32 `6` `524092` `49` `48`);;

let MLD_SIGN_W_LAZY_65 = prove
 (MLD_SIGN_W_LAZY_65_STMT,
  MLD_SIGN_W_LAZY_TAC MLD_FIPS204_SIGN_GAMMA1_19_BOUND `6`);;

let MLD_KEYPAIR_T_LAZY_87 = prove
 (MLD_KEYPAIR_T_LAZY_87_STMT,
  MLD_KEYPAIR_T_LAZY_TAC MLD_POLYETA_UNPACK_2_BOUND `8`
   `\n. n < 15 \/ n = 255`);;

let MLD_PK_FROM_SK_T_LAZY_87 = prove
 (MLD_PK_FROM_SK_T_LAZY_87_STMT,
  MLD_PK_FROM_SK_T_LAZY_TAC MLD_POLYETA_UNPACK_2_BOUND `8`);;

let MLD_VERIFY_W1_LAZY_87 = prove
 (MLD_VERIFY_W1_LAZY_87_STMT,
  MLD_VERIFY_W1_LAZY_TAC mld_poly_use_hint_32 `8` `524168` `60` `64`);;

let MLD_SIGN_W_LAZY_87 = prove
 (MLD_SIGN_W_LAZY_87_STMT,
  MLD_SIGN_W_LAZY_TAC MLD_FIPS204_SIGN_GAMMA1_19_BOUND `8`);;
