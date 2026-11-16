(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Foundation lemmas for the FIPS 203 equivalence proofs: the monadic        *)
(* plumbing of the generated model (native_bind, native_foldl,              *)
(* native_schedule, typed_hol_read and the list/integer primitives), the    *)
(* Z_q abstraction functions of base.ml, and the hash functions G, H, J, PRF.*)
(* Load from the repository root after base.ml and interface.ml.            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The result monad.                                                         *)
(* ------------------------------------------------------------------------- *)

let NATIVE_BIND_VALUE = prove
 (NATIVE_BIND_VALUE_STMT,
  REWRITE_TAC[native_bind_DEF; case_native_result_DEF]);;

let NATIVE_BIND_FAULT = prove
 (NATIVE_BIND_FAULT_STMT,
  REWRITE_TAC[native_bind_DEF; case_native_result_DEF]);;

(* ------------------------------------------------------------------------- *)
(* The Isabelle integer and natural-number primitives of the prelude.        *)
(* ------------------------------------------------------------------------- *)

let ISA_NAT_NUM = prove
 (ISA_NAT_NUM_STMT,
  REWRITE_TAC[isa_nat; INT_POS; NUM_OF_INT_OF_NUM]);;

let ISA_INT_MOD_POS = prove
 (ISA_INT_MOD_POS_STMT,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[isa_int_mod; INT_ARITH `&0:int < b ==> ~(b < &0)`]);;

let ISA_INT_DIV_POS = prove
 (ISA_INT_DIV_POS_STMT,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[isa_int_div; INT_ARITH `&0:int < b ==> ~(b < &0)`]);;

let ISA_UPT = prove
 (ISA_UPT_STMT,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[isa_upt; ARITH_RULE `0 - m = 0`; CONJUNCT1 list_of_seq];
    ALL_TAC] THEN
  REWRITE_TAC[isa_upt] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `SUC n - m = SUC(n - m)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[list_of_seq] THEN
    SUBGOAL_THEN `m + (n - m) = n` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[]];
    SUBGOAL_THEN `SUC n - m = 0` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[CONJUNCT1 list_of_seq]]]);;

(* ------------------------------------------------------------------------- *)
(* The checked integer operations.                                           *)
(* ------------------------------------------------------------------------- *)

let INT_ARITH_ADIV = prove
 (INT_ARITH_ADIV_STMT,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[typed_hol_int_arithmetic_DEF; arith_faults_DEF; int_op_DEF;
               case_aop_DEF; distinctness "aop"; ISA_INT_DIV_POS;
               INT_ARITH `&0:int < b ==> ~(b = &0)`]);;

let INT_ARITH_AQUOT = prove
 (INT_ARITH_AQUOT_STMT,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[typed_hol_int_arithmetic_DEF; arith_faults_DEF; int_op_DEF;
               case_aop_DEF; distinctness "aop"; ISA_INT_DIV_POS;
               ISA_INT_MOD_POS;
               INT_ARITH `&0:int < b ==> ~(b = &0)`]);;

let INT_ARITH_APOW = prove
 (INT_ARITH_APOW_STMT,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[typed_hol_int_arithmetic_DEF; ISA_NAT_NUM] THEN
  REWRITE_TAC[INT_ARITH `~((&n:int) < &0)`]);;

let TYPED_HOL_POW_MOD = prove
 (TYPED_HOL_POW_MOD_STMT,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0:int < &m` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[typed_hol_pow_mod_DEF; ISA_INT_MOD_POS; ISA_NAT_NUM;
               INT_ARITH `&0:int < m ==> ~((&e:int) < &0 \/ m <= &0)`]);;

let TYPED_HOL_NONNEGATIVE = prove
 (TYPED_HOL_NONNEGATIVE_STMT,
  REWRITE_TAC[typed_hol_nonnegative_DEF; INT_POS]);;

(* ------------------------------------------------------------------------- *)
(* Conversions between integers, bytes and bits.                             *)
(* ------------------------------------------------------------------------- *)

let TYPED_HOL_INT_TO_BYTE = prove
 (TYPED_HOL_INT_TO_BYTE_STMT,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[typed_hol_int_to_byte_DEF; INT_POS; INT_OF_NUM_LT;
               GSYM WORD_IWORD]);;

let TYPED_HOL_INT_TO_BIT = prove
 (TYPED_HOL_INT_TO_BIT_STMT,
  GEN_TAC THEN REWRITE_TAC[typed_hol_int_to_bit_DEF] THEN
  ASM_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN REWRITE_TAC[]);;

let TYPED_HOL_INT_TO_BIT_CLAUSES = prove
 (TYPED_HOL_INT_TO_BIT_CLAUSES_STMT,
  REWRITE_TAC[typed_hol_int_to_bit_DEF] THEN
  CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN REWRITE_TAC[]);;

let TYPED_HOL_BIT_VALUE = prove
 (TYPED_HOL_BIT_VALUE_STMT,
  GEN_TAC THEN REWRITE_TAC[typed_hol_bit_value_DEF; BITVAL_CLAUSES] THEN
  COND_CASES_TAC THEN REWRITE_TAC[bitval] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Lists: indexing, updating, slicing and extent checks.                     *)
(* ------------------------------------------------------------------------- *)

let NATIVE_LIST_INDEX = prove
 (NATIVE_LIST_INDEX_STMT,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[native_list_index_DEF; INT_POS; INT_OF_NUM_LT;
               typed_hol_read_DEF; isa_case_option; ISA_NAT_NUM]);;

let NATIVE_LIST_UPDATE = prove
 (NATIVE_LIST_UPDATE_STMT,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[native_list_update_DEF; INT_POS; INT_OF_NUM_LT;
               typed_hol_read_DEF; isa_case_option; ISA_NAT_NUM]);;

let LENGTH_ISA_LIST_UPDATE = prove
 (LENGTH_ISA_LIST_UPDATE_STMT,
  LIST_INDUCT_TAC THEN REWRITE_TAC[isa_list_update; LENGTH] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH]);;

let EL_ISA_LIST_UPDATE = prove
 (EL_ISA_LIST_UPDATE_STMT,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; isa_list_update; CONJUNCT1 LT] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  ASM_REWRITE_TAC[EL; HD; TL; NOT_SUC; SUC_INJ; LT_SUC; SUC_SUB1;
                  GSYM NOT_SUC] THEN
  ASM_SIMP_TAC[]);;

let SEQUENCE_EXTENT = prove
 (SEQUENCE_EXTENT_STMT,
  SIMP_TAC[typed_hol_sequence_extent_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Updates of a single field of a polynomial, vector or matrix.              *)
(* ------------------------------------------------------------------------- *)

let NOMINAL_UPDATE_POLY = prove
 (NOMINAL_UPDATE_POLY_STMT,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[typed_hol_nominal_update_DEF; fips203_poly_SEL_CTR;
               native_list_update_DEF; INT_POS; INT_OF_NUM_LT;
               isa_map_option; typed_hol_read_DEF; isa_case_option;
               ISA_NAT_NUM]);;

let NOMINAL_UPDATE_VEC = prove
 (NOMINAL_UPDATE_VEC_STMT,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[typed_hol_nominal_update_DEF; common_vec_SEL_CTR;
               native_list_update_DEF; INT_POS; INT_OF_NUM_LT;
               isa_map_option; typed_hol_read_DEF; isa_case_option;
               ISA_NAT_NUM]);;

let NOMINAL_UPDATE_MAT = prove
 (NOMINAL_UPDATE_MAT_STMT,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[typed_hol_nominal_update_DEF; common_mat_entries_DEF;
               fips_matrix_SEL_CTR;
               native_list_update_DEF; INT_POS; INT_OF_NUM_LT;
               isa_map_option; typed_hol_read_DEF; isa_case_option;
               ISA_NAT_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Z_q and the abstraction functions of base.ml.                             *)
(* ------------------------------------------------------------------------- *)

let FZ_POS = prove
 (FZ_POS_STMT,
  REWRITE_TAC[fz; INT_POS]);;

let LENGTH_ZQLIST = prove
 (LENGTH_ZQLIST_STMT,
  REWRITE_TAC[zqlist; LENGTH_LIST_OF_SEQ]);;

let EL_ZQLIST = prove
 (EL_ZQLIST_STMT,
  SIMP_TAC[zqlist; EL_LIST_OF_SEQ]);;

let RESIDUE_OF_INT_MOD_REP = prove
 (RESIDUE_OF_INT_MOD_REP_STMT,
  GEN_TAC THEN
  SUBGOAL_THEN `&0:int < &(dimindex(:N))` ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LT] THEN
    MESON_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> 0 < n`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[residue_of_int_mod_DEF; residue_SEL_CTR; ISA_INT_MOD_POS;
               isa_nat] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (INT_ARITH `~(&0:int <= x) ==> x < &0`)) THEN
  ASM_SIMP_TAC[GSYM INT_NOT_LE; INT_REM_POS;
               INT_ARITH `&0:int < n ==> ~(n = &0)`]);;

let FZ_RESIDUE_OF_INT_MOD = prove
 (FZ_RESIDUE_OF_INT_MOD_STMT,
  GEN_TAC THEN
  REWRITE_TAC[fz; fips203_zq_residue_DEF; RESIDUE_OF_INT_MOD_REP] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
  SIMP_TAC[INT_REM_POS; INT_OF_NUM_EQ; ARITH_EQ]);;

let ZARR_ZQLIST = prove
 (ZARR_ZQLIST_STMT,
  SIMP_TAC[zarr; EL_ZQLIST; FZ_RESIDUE_OF_INT_MOD]);;

let ZQ_LIST_OK_ZQLIST = prove
 (ZQ_LIST_OK_ZQLIST_STMT,
  REWRITE_TAC[zq_list_ok; LENGTH_ZQLIST] THEN
  SIMP_TAC[EL_ZQLIST; FZ_RESIDUE_OF_INT_MOD] THEN
  SIMP_TAC[INT_LT_REM; INT_ARITH `&0:int < &3329`]);;

let ZQLIST_EQ = prove
 (ZQLIST_EQ_STMT,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[zqlist; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[residue_of_int_mod_DEF] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  ASM_SIMP_TAC[ISA_INT_MOD_POS; INT_ARITH `&0:int < &3329`]);;

let ZQLIST_ZARR = prove
 (ZQLIST_ZARR_STMT,
  REWRITE_TAC[zq_list_ok] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[LIST_EQ] THEN
  ASM_REWRITE_TAC[LENGTH_ZQLIST] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_ZQLIST; zarr] THEN
  SUBGOAL_THEN `fz (EL i (l:fips203_zq list)) < &3329` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`EL i (l:fips203_zq list)`,`z:fips203_zq`) THEN
  MATCH_MP_TAC fips203_zq_INDUCT THEN
  X_GEN_TAC `r:(3329)residue` THEN
  REWRITE_TAC[fz; fips203_zq_residue_DEF; INT_OF_NUM_LT] THEN
  DISCH_TAC THEN REWRITE_TAC[residue_of_int_mod_DEF] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  ASM_SIMP_TAC[ISA_INT_MOD_POS; INT_ARITH `&0:int < &3329`] THEN
  ASM_SIMP_TAC[INT_OF_NUM_REM; ISA_NAT_NUM; MOD_LT; residue_CTR_SEL]);;

(* ------------------------------------------------------------------------- *)
(* Slices: isa_take of isa_drop.                                             *)
(* ------------------------------------------------------------------------- *)

let FOUNDATION_LENGTH_ISA_DROP = prove
 (`!(xs:A list) n. LENGTH (isa_drop n xs) = LENGTH xs - n`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[isa_drop; LENGTH; SUB_0] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; LENGTH; SUB_0] THEN
  ARITH_TAC);;

let FOUNDATION_LENGTH_ISA_TAKE = prove
 (`!(xs:A list) n. LENGTH (isa_take n xs) = MIN n (LENGTH xs)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[isa_take; LENGTH; ARITH_RULE `MIN n 0 = 0`] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; LENGTH] THEN
  ARITH_TAC);;

let FOUNDATION_EL_ISA_DROP = prove
 (`!(xs:A list) n i. n + i < LENGTH xs
                     ==> EL i (isa_drop n xs) = EL (n + i) xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN REWRITE_TAC[isa_drop; NOT_SUC; SUC_SUB1; ADD_CLAUSES] THEN
  REWRITE_TAC[EL; TL; ADD_CLAUSES; LT_SUC] THEN
  ASM_SIMP_TAC[]);;

let FOUNDATION_EL_ISA_TAKE = prove
 (`!(xs:A list) n i. i < n /\ i < LENGTH xs
                     ==> EL i (isa_take n xs) = EL i xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN REWRITE_TAC[isa_take; NOT_SUC; SUC_SUB1; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; LT_SUC; LT_0] THEN
  ASM_SIMP_TAC[]);;

let LIST_SLICE = prove
 (LIST_SLICE_STMT,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a:num <= LENGTH(xs:A list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[typed_hol_list_slice_DEF; INT_POS; INT_OF_NUM_LE;
               typed_hol_read_DEF; isa_case_option; ISA_NAT_NUM] THEN
  SUBGOAL_THEN `isa_nat(&u - &a) = u - a` SUBST1_TAC THENL
   [ASM_SIMP_TAC[INT_OF_NUM_SUB; ISA_NAT_NUM]; ALL_TAC] THEN
  AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[LIST_EQ] THEN
  REWRITE_TAC[FOUNDATION_LENGTH_ISA_TAKE; FOUNDATION_LENGTH_ISA_DROP;
              LENGTH_LIST_OF_SEQ] THEN
  SUBGOAL_THEN `MIN (u - a) (LENGTH(xs:A list) - a) = u - a` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  MP_TAC(ISPECL [`isa_drop a (xs:A list)`; `u - a:num`; `i:num`]
                FOUNDATION_EL_ISA_TAKE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FOUNDATION_LENGTH_ISA_DROP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC FOUNDATION_EL_ISA_DROP THEN ASM_ARITH_TAC);;

let LIST_SLICE_BYTES = prove
 (LIST_SLICE_BYTES_STMT,
  SIMP_TAC[LIST_SLICE; mlkem_slice]);;

(* ------------------------------------------------------------------------- *)
(* Loops: native_foldl over a native_schedule of indices.                    *)
(* ------------------------------------------------------------------------- *)

let NATIVE_FOLDL_VALUE = prove
 (NATIVE_FOLDL_VALUE_STMT,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[native_foldl_DEF; equiv_foldl; MEM] THEN
  X_GEN_TAC `s:S` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "step")) THEN
  SUBGOAL_THEN `(body:I->S->(S)native_result) h s = Value ((g:I->S->S) h s) /\
                (P:S->bool) (g h s)` STRIP_ASSUME_TAC THENL
   [USE_THEN "step" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[NATIVE_BIND_VALUE] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "step" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let NATIVE_SCHEDULE_UPTO = prove
 (NATIVE_SCHEDULE_UPTO_STMT,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[CONJUNCT1 LT; native_schedule_DEF] THEN
  ASM_CASES_TAC `a:num < n` THEN
  ASM_SIMP_TAC[INT_OF_NUM_LT; INT_OF_NUM_ADD] THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`a + 1`; `n:num`] th)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `n - a = SUC(n - (a + 1))` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LIST_OF_SEQ; o_DEF; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `SUC(a + x) = (a + 1) + x`];
    SUBGOAL_THEN `n - a = 0` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[CONJUNCT1 list_of_seq]]]);;

(* The number of multiples of d below n, i.e. the length of the schedule     *)
(* that starts at 0 and steps by d while staying below n.                    *)

let FOUNDATION_CEIL_DIV_LT = prove
 (`!d n k. 0 < d ==> (k < (n + d - 1) DIV d <=> d * k < n)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LDIV_LT_EQ; ARITH_RULE `0 < d ==> ~(d = 0)`] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
  ASM_ARITH_TAC);;

let FOUNDATION_CEIL_DIV_LE = prove
 (`!d n. 0 < d ==> (n + d - 1) DIV d <= n`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LE_LDIV_EQ; ARITH_RULE `0 < d ==> ~(d = 0)`] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
  SUBGOAL_THEN `n <= d * n` MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `n = 1 * n`] THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let FOUNDATION_SCHEDULE_STEP_GEN = prove
 (`!fuel d n k.
     0 < d /\ (n + d - 1) DIV d - k < fuel
     ==> native_schedule fuel (\i. int_lt i (&n)) (\i. int_add i (&d))
                         (&(d * k)) =
         list_of_seq (\i. &(d * (k + i))) ((n + d - 1) DIV d - k)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[CONJUNCT1 LT; native_schedule_DEF] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `d * k < n` THEN
  ASM_SIMP_TAC[INT_OF_NUM_LT; INT_OF_NUM_ADD] THENL
   [SUBGOAL_THEN `k < (n + d - 1) DIV d` ASSUME_TAC THENL
     [ASM_SIMP_TAC[FOUNDATION_CEIL_DIV_LT]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `d * k + d = d * (k + 1)`] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`d:num`; `n:num`; `k + 1`] th)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(n + d - 1) DIV d - k = SUC((n + d - 1) DIV d - (k + 1))`
    SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LIST_OF_SEQ; o_DEF; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `SUC(k + x) = (k + 1) + x`];
    SUBGOAL_THEN `(n + d - 1) DIV d - k = 0` SUBST1_TAC THENL
     [MP_TAC(SPECL [`d:num`; `n:num`; `k:num`] FOUNDATION_CEIL_DIV_LT) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      REWRITE_TAC[CONJUNCT1 list_of_seq]]]);;

let NATIVE_SCHEDULE_STEP = prove
 (NATIVE_SCHEDULE_STEP_STMT,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`fuel:num`; `d:num`; `n:num`; `0`]
               FOUNDATION_SCHEDULE_STEP_GEN) THEN
  REWRITE_TAC[MULT_CLAUSES; SUB_0; ADD_CLAUSES] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`d:num`; `n:num`] FOUNDATION_CEIL_DIV_LE) THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[]]);;

let NATIVE_SCHEDULE_NTTINV = prove
 (NATIVE_SCHEDULE_NTTINV_STMT,
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [ARITH_RULE `128 = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC 120)))))))`] THEN
  REWRITE_TAC[native_schedule_DEF] THEN
  CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
  REWRITE_TAC[]);;

(* A loop that writes f i into position i for every i < n.                   *)

let FOUNDATION_MEM_LIST_OF_SEQ = prove
 (`!(s:num->A) n x. MEM x (list_of_seq s n) <=> ?i. i < n /\ x = s i`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; MEM; CONJUNCT1 LT; MEM_APPEND] THEN
  ASM_REWRITE_TAC[LT] THEN MESON_TAC[]);;

let FOUNDATION_EQUIV_FOLDL_APPEND = prove
 (`!(g:I->S->S) s l1 l2.
     equiv_foldl g s (APPEND l1 l2) = equiv_foldl g (equiv_foldl g s l1) l2`,
  GEN_TAC THEN GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; equiv_foldl]);;

let foundation_fill = new_definition
 `foundation_fill (f:num->A) s k =
    equiv_foldl (\x t. isa_list_update t (isa_nat x) (f (isa_nat x))) s
                (list_of_seq (\i. &i) k)`;;

let FOUNDATION_FILL_CLAUSES = prove
 (`(!(f:num->A) s. foundation_fill f s 0 = s) /\
   (!(f:num->A) s k. foundation_fill f s (SUC k) =
                     isa_list_update (foundation_fill f s k) k (f k))`,
  REWRITE_TAC[foundation_fill; list_of_seq; equiv_foldl;
              FOUNDATION_EQUIV_FOLDL_APPEND] THEN
  REWRITE_TAC[equiv_foldl; ISA_NAT_NUM]);;

let FOUNDATION_LENGTH_FILL = prove
 (`!(f:num->A) s k. LENGTH (foundation_fill f s k) = LENGTH s`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[FOUNDATION_FILL_CLAUSES; LENGTH_ISA_LIST_UPDATE]);;

let FOUNDATION_EL_FILL = prove
 (`!(f:num->A) s k j.
     j < LENGTH s
     ==> EL j (foundation_fill f s k) = if j < k then f j else EL j s`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[FOUNDATION_FILL_CLAUSES; CONJUNCT1 LT] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_ISA_LIST_UPDATE; FOUNDATION_LENGTH_FILL] THEN
  ASM_CASES_TAC `j:num = k` THEN ASM_REWRITE_TAC[LT_REFL; LT] THEN
  ASM_MESON_TAC[]);;

let NATIVE_FOLDL_FILL = prove
 (NATIVE_FOLDL_FILL_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`body:int->(A)list->((A)list)native_result`;
    `\x t. isa_list_update (t:A list) (isa_nat x) ((f:num->A) (isa_nat x))`;
    `\t:A list. LENGTH t = n`;
    `list_of_seq (\i. &i) n :int list`;
    `s:A list`] NATIVE_FOLDL_VALUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FOUNDATION_MEM_LIST_OF_SEQ] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)
                               ASSUME_TAC) THEN
    ASM_SIMP_TAC[ISA_NAT_NUM; LENGTH_ISA_LIST_UPDATE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM foundation_fill] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[LIST_EQ] THEN
  ASM_REWRITE_TAC[FOUNDATION_LENGTH_FILL; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; FOUNDATION_EL_FILL]);;

(* ------------------------------------------------------------------------- *)
(* OneByte and BitRev7.                                                      *)
(* ------------------------------------------------------------------------- *)

let ONEBYTE_HOL = prove
 (ONEBYTE_HOL_STMT,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[OneByte_hol_DEF; ISA_NAT_NUM] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[num_CONV `1`; REPLICATE] THEN
  ASM_SIMP_TAC[TYPED_HOL_NONNEGATIVE; TYPED_HOL_INT_TO_BYTE;
               NATIVE_BIND_VALUE] THEN
  SIMP_TAC[NATIVE_LIST_UPDATE; LENGTH; ARITH] THEN
  REWRITE_TAC[isa_list_update]);;

let FOUNDATION_ADIV_POW2 = prove
 (`!a k. typed_hol_int_arithmetic ADiv a (&2 pow k) = Value (a div &2 pow k)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC INT_ARITH_ADIV THEN
  MATCH_MP_TAC INT_POW_LT THEN INT_ARITH_TAC);;

let FOUNDATION_IMOD2 = prove
 (`!a. isa_int_mod a (&2) = a rem &2`,
  SIMP_TAC[ISA_INT_MOD_POS; INT_ARITH `&0:int < &2`]);;

let FOUNDATION_SIX_SUB = INT_ARITH
 `(&6:int) - &0 = &6 /\ (&6:int) - &1 = &5 /\ (&6:int) - &2 = &4 /\
  (&6:int) - &3 = &3 /\ (&6:int) - &4 = &2 /\ (&6:int) - &5 = &1 /\
  (&6:int) - &6 = &0`;;

(* The seven-step fold of BitRev7_hol, run symbolically: bit j of r, for     *)
(* j = 0, ..., 6, contributes to the coefficient of 2^(6-j).                 *)

let FOUNDATION_BITREV7 = GEN_ALL
 ((REWRITE_CONV[BitRev7_hol_DEF] THENC
   DEPTH_CONV let_CONV THENC
   REWRITE_CONV[native_foldl_DEF; ISA_NAT_NUM; FOUNDATION_SIX_SUB;
                FOUNDATION_ADIV_POW2; INT_ARITH_APOW;
                NATIVE_BIND_VALUE; FOUNDATION_IMOD2])
  `BitRev7_hol r`);;

let BITREV7_HOL = prove
 (BITREV7_HOL_STMT,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(REWRITE_CONV[FOUNDATION_BITREV7; BITREVERSE7_CLAUSES] THENC
           WORD_REDUCE_CONV THENC NUM_REDUCE_CONV THENC
           DEPTH_CONV INT_RED_CONV));;

(* ------------------------------------------------------------------------- *)
(* The hash functions G, H, J and PRF. The generated model indexes the SHA-3 *)
(* output byte by byte over isa_upt, the handwritten one takes a prefix of   *)
(* the byte sequence.                                                        *)
(* ------------------------------------------------------------------------- *)

let FOUNDATION_MAP_ISA_UPT = prove
 (`!(f:num->A) m n.
     MAP f (isa_upt m n) = list_of_seq (\i. f (m + i)) (n - m)`,
  REWRITE_TAC[ISA_UPT; MAP_LIST_OF_SEQ; o_DEF]);;

let G_SEMANTIC = prove
 (G_SEMANTIC_STMT,
  REWRITE_TAC[G_semantic_DEF; G_DEF; hash_g_byte_DEF; mlkem_g; mlkem_slice;
              FOUNDATION_MAP_ISA_UPT] THEN
  REWRITE_TAC[ARITH_RULE `32 - 0 = 32 /\ 64 - 32 = 32`; ADD_CLAUSES]);;

let H_SEMANTIC = prove
 (H_SEMANTIC_STMT,
  REWRITE_TAC[H_semantic_DEF; H_DEF; hash_h_byte_DEF; mlkem_h;
              FOUNDATION_MAP_ISA_UPT; ADD_CLAUSES; SUB_0] THEN
  GEN_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  REWRITE_TAC[sha3_256; LENGTH_LIST_OF_SEQ]);;

let J_SEMANTIC = prove
 (J_SEMANTIC_STMT,
  REWRITE_TAC[J_semantic_DEF; J_DEF; hash_j_byte_DEF; mlkem_j;
              FOUNDATION_MAP_ISA_UPT; ADD_CLAUSES; SUB_0; ETA_AX]);;

let PRF_SEMANTIC = prove
 (PRF_SEMANTIC_STMT,
  REWRITE_TAC[PRF_semantic_DEF; UNCURRY_DEF; PRF_DEF; prf_byte_DEF; mlkem_prf;
              FOUNDATION_MAP_ISA_UPT; ADD_CLAUSES; SUB_0; ETA_AX]);;
