(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The input checks of FIPS 203 Sections 7.2 and 7.3.                         *)
(* ========================================================================= *)

needs "common/fips203/properties/kpke_ntt_domain.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The input checks: the modulus check of FIPS 203 Section 7.2 says exactly  *)
(* that ek has the right length and all its 12-bit fields (except those of   *)
(* rho) are < q.                                                             *)
(* ------------------------------------------------------------------------- *)

let LIST_OF_SEQ_EL_BYTELIST = prove
 (`!n l. n <= LENGTH l
         ==> list_of_seq (\i. EL i l) n =
             bytelist_of_num n (num_of_bytelist l)`,
  INDUCT_TAC THEN REWRITE_TAC[LIST_OF_SEQ; bytelist_of_num] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC n <= 0)`] THEN
  REWRITE_TAC[LE_SUC; num_of_bytelist; o_DEF; EL; HD; TL] THEN
  DISCH_TAC THEN REWRITE_TAC[CONS_11] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_MULT_ADD; MOD_LT; WORD_VAL];
    MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[DIV_MULT_ADD; DIV_LT; ARITH_EQ; ADD_CLAUSES] THEN
    DISCH_THEN(K ALL_TAC) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let MLKEM_SLICE_0 = prove
 (`!n l. n <= LENGTH l
         ==> mlkem_slice 0 n l = bytelist_of_num n (num_of_bytelist l)`,
  REWRITE_TAC[mlkem_slice; ADD_CLAUSES; LIST_OF_SEQ_EL_BYTELIST]);;

let BYTELIST_OF_NUM_EQ = prove
 (`!m a b. bytelist_of_num m a = bytelist_of_num m b <=>
           a MOD 256 EXP m = b MOD 256 EXP m`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `num_of_bytelist`) THEN
    REWRITE_TAC[NUM_OF_BYTELIST_OF_NUM];
    DISCH_TAC THEN
    ONCE_REWRITE_TAC[GSYM BYTELIST_OF_NUM_OF_BYTELIST] THEN
    ASM_REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM]]);;

let NUM_OF_INT_MLKEM_DECODE_12 = prove
 (`!b i. num_of_int(mlkem_decode 12 b i rem &2 pow 12) =
         ((num_of_bytelist b DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329`,
  REWRITE_TAC[mlkem_decode] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_POW; NUM_OF_INT_OF_NUM] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MATCH_MP_TAC(ARITH_RULE `x < 3329 ==> x < 2 EXP 12`) THEN
  REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]);;

let MLKEM_EK_CHECK = prove
 (`!k eta1 eta2 du dv ek.
        mlkem_ek_check (k,eta1,eta2,du,dv) ek <=>
        LENGTH ek = 384 * k + 32 /\
        !i. i < 256 * k
            ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_ek_check] THEN
  ASM_CASES_TAC `LENGTH(ek:byte list) = 384 * k + 32` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MLKEM_SLICE_0; ARITH_RULE `384 * k <= 384 * k + 32`] THEN
  REWRITE_TAC[mlkem_encode; ARITH_RULE `(12 * 256 * k) DIV 8 = 384 * k`] THEN
  REWRITE_TAC[BYTELIST_OF_NUM_EQ; NUM_OF_INT_MLKEM_DECODE_12] THEN
  SUBGOAL_THEN `256 EXP (384 * k) = (2 EXP 12) EXP (256 * k)` SUBST1_TAC THENL
   [REWRITE_TAC[EXP_EXP; ARITH_RULE `256 = 2 EXP 8`] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
   `b * 2 EXP (12 * i) = (2 EXP 12) EXP i * b`] THEN
  W(fun (_,w) ->
      let stm = lhand(lhand(lhand w)) in
      SUBGOAL_THEN (mk_binop `(<):num->num->bool` stm
                             `(2 EXP 12) EXP (256 * k)`) ASSUME_TAC) THENL
   [MATCH_MP_TAC DIGITSUM_BOUND THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < 3329 ==> x < 2 EXP 12`) THEN
    REWRITE_TAC[MOD_LT_EQ; ARITH_EQ];
    ASM_SIMP_TAC[MOD_LT]] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM DIGITSUM_WORKS_GEN] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) DIGITSUM_UNIQUE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `x < 3329 ==> x < 2 EXP 12`) THEN
    REWRITE_TAC[MOD_LT_EQ; ARITH_EQ];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; EXP_EXP; MOD_EQ_SELF; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Decoding a field of a prefix of a byte string: it agrees with decoding    *)
(* it from the whole string if the field lies inside the prefix.             *)
(* ------------------------------------------------------------------------- *)

let KPKE_DECODE_SLICE_0 = prove
 (`!d n (b:byte list) i.
        n <= LENGTH b /\ d * i + d <= 8 * n
        ==> mlkem_decode d (mlkem_slice 0 n b) i = mlkem_decode d b i`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MLKEM_SLICE_0; NUM_OF_BYTELIST_OF_NUM; mlkem_decode] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP] THEN
  ASM_SIMP_TAC[BYTES_DIV_MOD_MOD]);;

let MLKEM_DECODE12_SLICE0 = prove
 (`!n (l:byte list) i.
     n <= LENGTH l /\ 12 * i + 12 <= 8 * n
     ==> mlkem_decode 12 (mlkem_slice 0 n l) i = mlkem_decode 12 l i`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_SLICE_0] THEN
  REWRITE_TAC[mlkem_decode; NUM_OF_BYTELIST_OF_NUM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; ARITH_RULE `256 = 2 EXP 8`;
              EXP_EXP; MOD_MOD_EXP_MIN] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
