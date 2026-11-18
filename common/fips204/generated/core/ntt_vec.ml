(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Equivalence of the vector and matrix functions of the generated FIPS 204  *)
(* specification (common/fips204/generated/fips204_generated.ml) with        *)
(* common/fips204/fips204.ml, in lift_vec / lift_mat form: EQ_VECTORNTT_*,   *)
(* EQ_VECTORNTTINV_*, EQ_INTVECTORNTT_*, EQ_INTVECTORTORQ_*,                 *)
(* EQ_ADDVECTORNTT_*, EQ_ADDVECTORSK/L, EQ_SCALARVECTORNTT_*,                *)
(* EQ_MATRIXVECTORNTT_*, EQ_RQVECTORADD_*, EQ_RQINTVECTORADD_*,              *)
(* EQ_RQVECTORNEGATE_*, EQ_INTVECTORSCALE_*, EQ_FIXEDVECTORSUBTRACT_*, and   *)
(* on lists of coefficient lists (ntt_rows) EQ_NEGVECTORNTT, EQ_SCALEVECTOR, *)
(* and the composite EQ_MATVEC_NTTINV_*: NTTInv(A^ * NTT(y)) = lift of       *)
(* mldsa_dot (A y). Sums over the columns are written ntt_msum n f (= isum   *)
(* {j | j < n} f, NTT_MSUM_ISUM).                                            *)
(*                                                                           *)
(* Load after base.ml and common.ml; needs ntt.ml.                     *)
(* ========================================================================= *)

needs "common/fips204/generated/core/common.ml";;
needs "common/fips204/generated/core/core.ml";;
needs "common/fips204/generated/core/ntt.ml";;

(* ------------------------------------------------------------------------- *)
(* Loops over lists and vectors (generic lemmas).                            *)
(* ------------------------------------------------------------------------- *)

let NTT_LIST_LOOP = prove
 (`!(body:int->S->(S)native_result) (C:(B)list->S) (g:num->B) l0 n.
     LENGTH l0 = n /\
     (!k l. k < n /\ LENGTH l = n
            ==> body (&k) (C l) = Value (C (isa_list_update l k (g k))))
     ==> native_foldl body (list_of_seq (\k. &k) n) (C l0) =
         Value (C (list_of_seq g n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `body:int->S->(S)native_result`; `\k. &k:int`;
                 `\k s. s = (C:(B)list->S)
                              (list_of_seq (\i. if i < k then g i
                                                 else EL i l0) n)`;
                 `(C:(B)list->S) l0`] NTT_FOLDL_INV) THEN
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

let NTT_SCHEDULE_4 = prove(`native_schedule 5 (\i. i < &4) (\i. i + &1) (&0:int) = list_of_seq (\k. &k) 4`, MP_TAC(SPEC `4` NATIVE_SCHEDULE_COUNT) THEN REWRITE_TAC[ARITH]);;
let NTT_SCHEDULE_5 = prove(`native_schedule 6 (\i. i < &5) (\i. i + &1) (&0:int) = list_of_seq (\k. &k) 5`, MP_TAC(SPEC `5` NATIVE_SCHEDULE_COUNT) THEN REWRITE_TAC[ARITH]);;
let NTT_SCHEDULE_6 = prove(`native_schedule 7 (\i. i < &6) (\i. i + &1) (&0:int) = list_of_seq (\k. &k) 6`, MP_TAC(SPEC `6` NATIVE_SCHEDULE_COUNT) THEN REWRITE_TAC[ARITH]);;
let NTT_SCHEDULE_7 = prove(`native_schedule 8 (\i. i < &7) (\i. i + &1) (&0:int) = list_of_seq (\k. &k) 7`, MP_TAC(SPEC `7` NATIVE_SCHEDULE_COUNT) THEN REWRITE_TAC[ARITH]);;
let NTT_SCHEDULE_8 = prove(`native_schedule 9 (\i. i < &8) (\i. i + &1) (&0:int) = list_of_seq (\k. &k) 8`, MP_TAC(SPEC `8` NATIVE_SCHEDULE_COUNT) THEN REWRITE_TAC[ARITH]);;

let NTT_COMMON_VEC_ENTRIES_CTR = prove
 (`!l. common_vec_entries (Common_Vec l:(N,B)common_vec) = l`,
  REWRITE_TAC[common_vec_SEL_CTR]);;

let NTT_LIST_LOOP_EL = prove
 (`!(body:int->S->(S)native_result) (C:(B)list->S) (g:num->B) l0 n.
     LENGTH l0 = n /\
     (!k l. k < n /\ LENGTH l = n /\ EL k l = EL k l0
            ==> body (&k) (C l) = Value (C (isa_list_update l k (g k))))
     ==> native_foldl body (list_of_seq (\k. &k) n) (C l0) =
         Value (C (list_of_seq g n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `body:int->S->(S)native_result`; `\k. &k:int`;
                 `\k s. s = (C:(B)list->S)
                              (list_of_seq (\i. if i < k then g i
                                                 else EL i l0) n)`;
                 `(C:(B)list->S) l0`] NTT_FOLDL_INV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN
      ASM_REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
      SIMP_TAC[EL_LIST_OF_SEQ];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(fun th -> if (try is_var(lhs(concl th)) with _ -> false)
                              then SUBST_ALL_TAC th else failwith "no") THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`k:num`; `list_of_seq (\i. if i < k then g i else EL i l0) n:B list`]) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ; LT_REFL];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[LENGTH_LIST_OF_SEQ] THEN
      REWRITE_TAC[NTT_RESULT_VALUE_EQ; ISA_LIST_UPDATE_LIST_OF_SEQ] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[LT] THEN
      ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LIST_OF_SEQ_EQ THEN SIMP_TAC[]]);;

let NTT_ISA_UPDATE_SELF = prove
 (`!(l:A list) i. i < LENGTH l ==> isa_list_update l i (EL i l) = l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_ISA_LIST_UPDATE] THEN
  ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let NTT_ISA_UPDATE_UPDATE = prove
 (`!(l:A list) i a b. isa_list_update (isa_list_update l i a) i b =
                      isa_list_update l i b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_ISA_LIST_UPDATE] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_ISA_LIST_UPDATE; LENGTH_ISA_LIST_UPDATE]);;

let NTT_MAP_REPLICATE = prove
 (`!(f:A->B) n x. MAP f (REPLICATE n x) = REPLICATE n (f x)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; MAP]);;

let NTT_ROW_LOOP = prove
 (`!(body:int->S->(S)native_result) (W:(P)list->S) (R:(Q)list->P) (g:num->Q)
    l k cs0 n.
     k < LENGTH l /\ EL k l = R cs0 /\ LENGTH cs0 = n /\
     (!j cs. j < n /\ LENGTH cs = n
             ==> body (&j) (W (isa_list_update l k (R cs))) =
                 Value (W (isa_list_update l k
                            (R (isa_list_update cs j (g j))))))
     ==> native_foldl body (list_of_seq (\j. &j) n) (W l) =
         Value (W (isa_list_update l k (R (list_of_seq g n))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`body:int->S->(S)native_result`;
                 `\cs. (W:(P)list->S) (isa_list_update l k ((R:(Q)list->P) cs))`;
                 `g:num->Q`; `cs0:(Q)list`; `n:num`] NTT_LIST_LOOP) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `isa_list_update l k ((R:(Q)list->P) cs0) = l`
   (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(ISPECL [`l:P list`; `k:num`] NTT_ISA_UPDATE_SELF) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let NTT_BIT_VALUE_F = prove
 (`typed_hol_bit_value F = Value (&0)`,
  REWRITE_TAC[typed_hol_bit_value_DEF]);;

let NTT_EL_REPLICATE = prove
 (`!(x:A) n k. k < n ==> EL k (REPLICATE n x) = x`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LT];
    INDUCT_TAC THEN REWRITE_TAC[REPLICATE; EL; HD; TL] THEN
    ASM_MESON_TAC[LT_SUC]]);;

(* ------------------------------------------------------------------------- *)
(* Vector functions. A vector is Common_Vec of 4-8 polynomials; the loops    *)
(* over its entries are handled by NTT_LIST_LOOP: each iteration replaces    *)
(* entry k by a function of entry k of the inputs.                           *)
(* ------------------------------------------------------------------------- *)

let NTT_SCHEDULES =
  [NTT_SCHEDULE_4; NTT_SCHEDULE_5; NTT_SCHEDULE_6; NTT_SCHEDULE_7;
   NTT_SCHEDULE_8];;

let NTT_DIMS =
  map (fun n -> DIMINDEX_CONV (parse_term ("dimindex(:" ^ string_of_int n ^ ")")))
      [4;5;6;7;8];;

let NTT_VEC_RULES =
  [COMMON_VEC_ENTRIES_LIFT; NTT_COMMON_VEC_ENTRIES_CTR] @ NTT_DIMS;;

(* A loop over the entries of a vector, whose result is lift_vec g.          *)

let NTT_VEC_TAC defth ths =
  REWRITE_TAC[defth] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC NTT_SCHEDULES THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [lift_vec] THEN
  REWRITE_TAC NTT_DIMS THEN
  MATCH_MP_TAC NTT_LIST_LOOP THEN REWRITE_TAC[LENGTH_MAP; LENGTH_REPLICATE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC(NTT_BODY_RULES @ NTT_VEC_RULES @ ths);;

let EQ_VECTORNTT_4_MLDSA44 = prove
 (`!a. VectorNTT_4_MLDSA44_Configuration_hol (lift_vec (\i. lift_poly (a i))) =
       Value (lift_vec (\i. lift_poly (mldsa_ntt (mldsa_poly (a i)))))`,
  GEN_TAC THEN NTT_VEC_TAC VectorNTT_4_MLDSA44_Configuration_hol_DEF
   [NTT_HOL_LAYERS; NTT_LIFT_FWD_LAYERS]);;

let EQ_VECTORNTT_5_MLDSA65 = prove
 (`!a. VectorNTT_5_MLDSA65_Configuration_hol (lift_vec (\i. lift_poly (a i))) =
       Value (lift_vec (\i. lift_poly (mldsa_ntt (mldsa_poly (a i)))))`,
  GEN_TAC THEN NTT_VEC_TAC VectorNTT_5_MLDSA65_Configuration_hol_DEF
   [NTT_HOL_LAYERS; NTT_LIFT_FWD_LAYERS]);;

let EQ_VECTORNTT_6_MLDSA65 = prove
 (`!a. VectorNTT_6_MLDSA65_Configuration_hol (lift_vec (\i. lift_poly (a i))) =
       Value (lift_vec (\i. lift_poly (mldsa_ntt (mldsa_poly (a i)))))`,
  GEN_TAC THEN NTT_VEC_TAC VectorNTT_6_MLDSA65_Configuration_hol_DEF
   [NTT_HOL_LAYERS; NTT_LIFT_FWD_LAYERS]);;

let EQ_VECTORNTT_7_MLDSA87 = prove
 (`!a. VectorNTT_7_MLDSA87_Configuration_hol (lift_vec (\i. lift_poly (a i))) =
       Value (lift_vec (\i. lift_poly (mldsa_ntt (mldsa_poly (a i)))))`,
  GEN_TAC THEN NTT_VEC_TAC VectorNTT_7_MLDSA87_Configuration_hol_DEF
   [NTT_HOL_LAYERS; NTT_LIFT_FWD_LAYERS]);;

let EQ_VECTORNTT_8_MLDSA87 = prove
 (`!a. VectorNTT_8_MLDSA87_Configuration_hol (lift_vec (\i. lift_poly (a i))) =
       Value (lift_vec (\i. lift_poly (mldsa_ntt (mldsa_poly (a i)))))`,
  GEN_TAC THEN NTT_VEC_TAC VectorNTT_8_MLDSA87_Configuration_hol_DEF
   [NTT_HOL_LAYERS; NTT_LIFT_FWD_LAYERS]);;

let EQ_INTVECTORNTT_4 = prove
 (`!a. IntVectorNTT_4_hol (lift_vec (\i. lift_intpoly (a i))) =
       Value (lift_vec (\i. lift_poly (mldsa_ntt (mldsa_poly (a i)))))`,
  GEN_TAC THEN NTT_VEC_TAC IntVectorNTT_4_hol_DEF
   [EQ_INTPOLYTORQ; NTT_HOL_LAYERS; NTT_LIFT_FWD_LAYERS]);;

let EQ_INTVECTORNTT_5 = prove
 (`!a. IntVectorNTT_5_hol (lift_vec (\i. lift_intpoly (a i))) =
       Value (lift_vec (\i. lift_poly (mldsa_ntt (mldsa_poly (a i)))))`,
  GEN_TAC THEN NTT_VEC_TAC IntVectorNTT_5_hol_DEF
   [EQ_INTPOLYTORQ; NTT_HOL_LAYERS; NTT_LIFT_FWD_LAYERS]);;

let EQ_INTVECTORNTT_6 = prove
 (`!a. IntVectorNTT_6_hol (lift_vec (\i. lift_intpoly (a i))) =
       Value (lift_vec (\i. lift_poly (mldsa_ntt (mldsa_poly (a i)))))`,
  GEN_TAC THEN NTT_VEC_TAC IntVectorNTT_6_hol_DEF
   [EQ_INTPOLYTORQ; NTT_HOL_LAYERS; NTT_LIFT_FWD_LAYERS]);;

let EQ_INTVECTORNTT_7 = prove
 (`!a. IntVectorNTT_7_hol (lift_vec (\i. lift_intpoly (a i))) =
       Value (lift_vec (\i. lift_poly (mldsa_ntt (mldsa_poly (a i)))))`,
  GEN_TAC THEN NTT_VEC_TAC IntVectorNTT_7_hol_DEF
   [EQ_INTPOLYTORQ; NTT_HOL_LAYERS; NTT_LIFT_FWD_LAYERS]);;

let EQ_INTVECTORNTT_8 = prove
 (`!a. IntVectorNTT_8_hol (lift_vec (\i. lift_intpoly (a i))) =
       Value (lift_vec (\i. lift_poly (mldsa_ntt (mldsa_poly (a i)))))`,
  GEN_TAC THEN NTT_VEC_TAC IntVectorNTT_8_hol_DEF
   [EQ_INTPOLYTORQ; NTT_HOL_LAYERS; NTT_LIFT_FWD_LAYERS]);;

let EQ_VECTORNTTINV_4_MLDSA44 = prove
 (`!a. (!i k. i < 4 /\ k < 256 ==> &0 <= a i k /\ a i k < &8380417)
       ==> VectorNTTInv_4_MLDSA44_Configuration_hol
             (lift_vec (\i. lift_poly (a i))) =
           Value (lift_vec (\i. lift_poly (\k. coeff k (mldsa_ntt_inv (a i)))))`,
  REPEAT STRIP_TAC THEN NTT_VEC_TAC VectorNTTInv_4_MLDSA44_Configuration_hol_DEF
   [EQ_NTTINV]);;

let EQ_VECTORNTTINV_5_MLDSA65 = prove
 (`!a. (!i k. i < 5 /\ k < 256 ==> &0 <= a i k /\ a i k < &8380417)
       ==> VectorNTTInv_5_MLDSA65_Configuration_hol
             (lift_vec (\i. lift_poly (a i))) =
           Value (lift_vec (\i. lift_poly (\k. coeff k (mldsa_ntt_inv (a i)))))`,
  REPEAT STRIP_TAC THEN NTT_VEC_TAC VectorNTTInv_5_MLDSA65_Configuration_hol_DEF
   [EQ_NTTINV]);;

let EQ_VECTORNTTINV_6_MLDSA65 = prove
 (`!a. (!i k. i < 6 /\ k < 256 ==> &0 <= a i k /\ a i k < &8380417)
       ==> VectorNTTInv_6_MLDSA65_Configuration_hol
             (lift_vec (\i. lift_poly (a i))) =
           Value (lift_vec (\i. lift_poly (\k. coeff k (mldsa_ntt_inv (a i)))))`,
  REPEAT STRIP_TAC THEN NTT_VEC_TAC VectorNTTInv_6_MLDSA65_Configuration_hol_DEF
   [EQ_NTTINV]);;

let EQ_VECTORNTTINV_7_MLDSA87 = prove
 (`!a. (!i k. i < 7 /\ k < 256 ==> &0 <= a i k /\ a i k < &8380417)
       ==> VectorNTTInv_7_MLDSA87_Configuration_hol
             (lift_vec (\i. lift_poly (a i))) =
           Value (lift_vec (\i. lift_poly (\k. coeff k (mldsa_ntt_inv (a i)))))`,
  REPEAT STRIP_TAC THEN NTT_VEC_TAC VectorNTTInv_7_MLDSA87_Configuration_hol_DEF
   [EQ_NTTINV]);;

let EQ_VECTORNTTINV_8_MLDSA87 = prove
 (`!a. (!i k. i < 8 /\ k < 256 ==> &0 <= a i k /\ a i k < &8380417)
       ==> VectorNTTInv_8_MLDSA87_Configuration_hol
             (lift_vec (\i. lift_poly (a i))) =
           Value (lift_vec (\i. lift_poly (\k. coeff k (mldsa_ntt_inv (a i)))))`,
  REPEAT STRIP_TAC THEN NTT_VEC_TAC VectorNTTInv_8_MLDSA87_Configuration_hol_DEF
   [EQ_NTTINV]);;

let EQ_INTVECTORTORQ_4 = prove
 (`!a. IntVectorToRq_4_hol (lift_vec (\i. lift_intpoly (a i))) =
       Value (lift_vec (\i. lift_poly (a i)))`,
  GEN_TAC THEN NTT_VEC_TAC IntVectorToRq_4_hol_DEF [EQ_INTPOLYTORQ]);;

let EQ_INTVECTORTORQ_4_BODY = prove
 (`!a. IntVectorToRq_4_body_hol (lift_vec (\i. lift_intpoly (a i))) =
       Value (lift_vec (\i. lift_poly (a i)))`,
  GEN_TAC THEN NTT_VEC_TAC IntVectorToRq_4_body_hol_DEF [EQ_INTPOLYTORQ]);;

let EQ_INTVECTORTORQ_5 = prove
 (`!a. IntVectorToRq_5_hol (lift_vec (\i. lift_intpoly (a i))) =
       Value (lift_vec (\i. lift_poly (a i)))`,
  GEN_TAC THEN NTT_VEC_TAC IntVectorToRq_5_hol_DEF [EQ_INTPOLYTORQ]);;

let EQ_INTVECTORTORQ_5_BODY = prove
 (`!a. IntVectorToRq_5_body_hol (lift_vec (\i. lift_intpoly (a i))) =
       Value (lift_vec (\i. lift_poly (a i)))`,
  GEN_TAC THEN NTT_VEC_TAC IntVectorToRq_5_body_hol_DEF [EQ_INTPOLYTORQ]);;

let EQ_INTVECTORTORQ_7 = prove
 (`!a. IntVectorToRq_7_hol (lift_vec (\i. lift_intpoly (a i))) =
       Value (lift_vec (\i. lift_poly (a i)))`,
  GEN_TAC THEN NTT_VEC_TAC IntVectorToRq_7_hol_DEF [EQ_INTPOLYTORQ]);;

let EQ_INTVECTORTORQ_7_BODY = prove
 (`!a. IntVectorToRq_7_body_hol (lift_vec (\i. lift_intpoly (a i))) =
       Value (lift_vec (\i. lift_poly (a i)))`,
  GEN_TAC THEN NTT_VEC_TAC IntVectorToRq_7_body_hol_DEF [EQ_INTPOLYTORQ]);;


let EQ_ADDVECTORNTT_4_MLDSA44 = prove
 (`!a b. AddVectorNTT_4_MLDSA44_Configuration_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REPEAT GEN_TAC THEN NTT_VEC_TAC AddVectorNTT_4_MLDSA44_Configuration_hol_DEF
   [EQ_ADDNTT]);;

let EQ_SCALARVECTORNTT_4_MLDSA44 = prove
 (`!c v. ScalarVectorNTT_4_MLDSA44_Configuration_hol
           (lift_poly c) (lift_vec (\i. lift_poly (v i))) =
         Value (lift_vec (\i. lift_poly (\k. c k * v i k)))`,
  REPEAT GEN_TAC THEN NTT_VEC_TAC ScalarVectorNTT_4_MLDSA44_Configuration_hol_DEF
   [EQ_MULTIPLYNTT]);;

let EQ_ADDVECTORNTT_5_MLDSA65 = prove
 (`!a b. AddVectorNTT_5_MLDSA65_Configuration_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REPEAT GEN_TAC THEN NTT_VEC_TAC AddVectorNTT_5_MLDSA65_Configuration_hol_DEF
   [EQ_ADDNTT]);;

let EQ_SCALARVECTORNTT_5_MLDSA65 = prove
 (`!c v. ScalarVectorNTT_5_MLDSA65_Configuration_hol
           (lift_poly c) (lift_vec (\i. lift_poly (v i))) =
         Value (lift_vec (\i. lift_poly (\k. c k * v i k)))`,
  REPEAT GEN_TAC THEN NTT_VEC_TAC ScalarVectorNTT_5_MLDSA65_Configuration_hol_DEF
   [EQ_MULTIPLYNTT]);;

let EQ_ADDVECTORNTT_6_MLDSA65 = prove
 (`!a b. AddVectorNTT_6_MLDSA65_Configuration_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REPEAT GEN_TAC THEN NTT_VEC_TAC AddVectorNTT_6_MLDSA65_Configuration_hol_DEF
   [EQ_ADDNTT]);;

let EQ_SCALARVECTORNTT_6_MLDSA65 = prove
 (`!c v. ScalarVectorNTT_6_MLDSA65_Configuration_hol
           (lift_poly c) (lift_vec (\i. lift_poly (v i))) =
         Value (lift_vec (\i. lift_poly (\k. c k * v i k)))`,
  REPEAT GEN_TAC THEN NTT_VEC_TAC ScalarVectorNTT_6_MLDSA65_Configuration_hol_DEF
   [EQ_MULTIPLYNTT]);;

let EQ_ADDVECTORNTT_7_MLDSA87 = prove
 (`!a b. AddVectorNTT_7_MLDSA87_Configuration_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REPEAT GEN_TAC THEN NTT_VEC_TAC AddVectorNTT_7_MLDSA87_Configuration_hol_DEF
   [EQ_ADDNTT]);;

let EQ_SCALARVECTORNTT_7_MLDSA87 = prove
 (`!c v. ScalarVectorNTT_7_MLDSA87_Configuration_hol
           (lift_poly c) (lift_vec (\i. lift_poly (v i))) =
         Value (lift_vec (\i. lift_poly (\k. c k * v i k)))`,
  REPEAT GEN_TAC THEN NTT_VEC_TAC ScalarVectorNTT_7_MLDSA87_Configuration_hol_DEF
   [EQ_MULTIPLYNTT]);;

let EQ_ADDVECTORNTT_8_MLDSA87 = prove
 (`!a b. AddVectorNTT_8_MLDSA87_Configuration_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REPEAT GEN_TAC THEN NTT_VEC_TAC AddVectorNTT_8_MLDSA87_Configuration_hol_DEF
   [EQ_ADDNTT]);;

let EQ_SCALARVECTORNTT_8_MLDSA87 = prove
 (`!c v. ScalarVectorNTT_8_MLDSA87_Configuration_hol
           (lift_poly c) (lift_vec (\i. lift_poly (v i))) =
         Value (lift_vec (\i. lift_poly (\k. c k * v i k)))`,
  REPEAT GEN_TAC THEN NTT_VEC_TAC ScalarVectorNTT_8_MLDSA87_Configuration_hol_DEF
   [EQ_MULTIPLYNTT]);;

let EQ_ADDVECTORSK_MLDSA44 = prove
 (`!a b. AddVectorsK_MLDSA44_Configuration_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REWRITE_TAC[AddVectorsK_MLDSA44_Configuration_hol_DEF;
              EQ_ADDVECTORNTT_4_MLDSA44]);;

let EQ_ADDVECTORSL_MLDSA44 = prove
 (`!a b. AddVectorsL_MLDSA44_Configuration_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REWRITE_TAC[AddVectorsL_MLDSA44_Configuration_hol_DEF;
              EQ_ADDVECTORNTT_4_MLDSA44]);;

let EQ_ADDVECTORSK_MLDSA65 = prove
 (`!a b. AddVectorsK_MLDSA65_Configuration_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REWRITE_TAC[AddVectorsK_MLDSA65_Configuration_hol_DEF;
              EQ_ADDVECTORNTT_6_MLDSA65]);;

let EQ_ADDVECTORSL_MLDSA65 = prove
 (`!a b. AddVectorsL_MLDSA65_Configuration_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REWRITE_TAC[AddVectorsL_MLDSA65_Configuration_hol_DEF;
              EQ_ADDVECTORNTT_5_MLDSA65]);;

let EQ_ADDVECTORSK_MLDSA87 = prove
 (`!a b. AddVectorsK_MLDSA87_Configuration_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REWRITE_TAC[AddVectorsK_MLDSA87_Configuration_hol_DEF;
              EQ_ADDVECTORNTT_8_MLDSA87]);;

let EQ_ADDVECTORSL_MLDSA87 = prove
 (`!a b. AddVectorsL_MLDSA87_Configuration_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REWRITE_TAC[AddVectorsL_MLDSA87_Configuration_hol_DEF;
              EQ_ADDVECTORNTT_7_MLDSA87]);;


(* ------------------------------------------------------------------------- *)
(* Vectors of polynomials: loops over entries and over coefficients.         *)
(* ------------------------------------------------------------------------- *)

let NTT_ROW_RULES =
  [NTT_BIT_VALUE_F; TYPED_HOL_INT_POW_NUM; TYPED_HOL_NESTED_UPDATE_NUM; INT_POW_ONE;
   INT_ADD_LID; INT_MUL_LID; fips204_poly_SEL_CTR; NTT_RESIDUE_REP; INT_REM_ZERO;
   EL_ISA_LIST_UPDATE; NTT_ISA_UPDATE_UPDATE];;

(* A loop over the entries of a vector, and inside it over the 256           *)
(* coefficients of the entry: the result is lift_vec of lift_poly's (or      *)
(* lift_intpoly's).                                                          *)

let NTT_ROWVEC_PRE_TAC defth pre ths =
  REWRITE_TAC[defth] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC(NTT_SCHEDULE_256 :: NTT_SCHEDULES) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [lift_vec] THEN
  REWRITE_TAC NTT_DIMS THEN
  MATCH_MP_TAC NTT_LIST_LOOP_EL THEN REWRITE_TAC[LENGTH_MAP; LENGTH_REPLICATE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  (if pre = [] then ALL_TAC else
   ASM_SIMP_TAC(NTT_BODY_RULES @ NTT_VEC_RULES @ NTT_ROW_RULES @ pre)) THEN
  REWRITE_TAC[lift_poly; lift_intpoly] THEN
  MATCH_MP_TAC NTT_ROW_LOOP THEN
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("EL",_),_),_)),
           Comb(Comb(Const("EL",_),_),_)) ->
        MP_TAC(REWRITE_RULE[NTT_MAP_REPLICATE] th)
    | _ -> failwith "no") THEN
  ASM_SIMP_TAC[NTT_EL_REPLICATE] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("EL",_),_),_)),r) ->
        EXISTS_TAC (rand r)
    | _ -> failwith "no") THEN
  REPEAT CONJ_TAC THEN
  FIRST [REFL_TAC; ASM_ARITH_TAC;
         (REWRITE_TAC[LENGTH_MAP; LENGTH_REPLICATE] THEN NO_TAC);
         REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
         ASM_SIMP_TAC(NTT_BODY_RULES @ NTT_VEC_RULES @ NTT_ROW_RULES @ ths) THEN
         CONV_TAC(ONCE_DEPTH_CONV NTT_LIFT_ZQ_CONV) THEN
         REWRITE_TAC[INT_SUB_LZERO]];;


let NTT_ROWVEC_TAC defth ths = NTT_ROWVEC_PRE_TAC defth [] ths;;

let EQ_RQVECTORADD_4 = prove
 (`!a b. RqVectorAdd_4_hol (lift_vec (\i. lift_poly (a i)))
                           (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REPEAT GEN_TAC THEN NTT_ROWVEC_TAC RqVectorAdd_4_hol_DEF []);;

let EQ_RQVECTORADD_5 = prove
 (`!a b. RqVectorAdd_5_hol (lift_vec (\i. lift_poly (a i)))
                           (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REPEAT GEN_TAC THEN NTT_ROWVEC_TAC RqVectorAdd_5_hol_DEF []);;

let EQ_RQVECTORADD_6 = prove
 (`!a b. RqVectorAdd_6_hol (lift_vec (\i. lift_poly (a i)))
                           (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REPEAT GEN_TAC THEN NTT_ROWVEC_TAC RqVectorAdd_6_hol_DEF []);;

let EQ_RQVECTORADD_7 = prove
 (`!a b. RqVectorAdd_7_hol (lift_vec (\i. lift_poly (a i)))
                           (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REPEAT GEN_TAC THEN NTT_ROWVEC_TAC RqVectorAdd_7_hol_DEF []);;

let EQ_RQVECTORADD_8 = prove
 (`!a b. RqVectorAdd_8_hol (lift_vec (\i. lift_poly (a i)))
                           (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REPEAT GEN_TAC THEN NTT_ROWVEC_TAC RqVectorAdd_8_hol_DEF []);;

let EQ_RQINTVECTORADD_4 = prove
 (`!a b. RqIntVectorAdd_4_hol (lift_vec (\i. lift_poly (a i)))
                              (lift_vec (\i. lift_intpoly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REPEAT GEN_TAC THEN NTT_ROWVEC_PRE_TAC RqIntVectorAdd_4_hol_DEF
   [EQ_INTPOLYTORQ] []);;

let EQ_RQINTVECTORADD_6 = prove
 (`!a b. RqIntVectorAdd_6_hol (lift_vec (\i. lift_poly (a i)))
                              (lift_vec (\i. lift_intpoly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REPEAT GEN_TAC THEN NTT_ROWVEC_PRE_TAC RqIntVectorAdd_6_hol_DEF
   [EQ_INTPOLYTORQ] []);;

let EQ_RQINTVECTORADD_8 = prove
 (`!a b. RqIntVectorAdd_8_hol (lift_vec (\i. lift_poly (a i)))
                              (lift_vec (\i. lift_intpoly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k + b i k)))`,
  REPEAT GEN_TAC THEN NTT_ROWVEC_PRE_TAC RqIntVectorAdd_8_hol_DEF
   [EQ_INTPOLYTORQ] []);;


let EQ_INTVECTORSCALE_4 = prove
 (`!a c. IntVectorScale_4_hol (lift_vec (\i. lift_intpoly (a i))) c =
         Value (lift_vec (\i. lift_intpoly (\k. a i k * c)))`,
  REPEAT GEN_TAC THEN NTT_ROWVEC_TAC IntVectorScale_4_hol_DEF []);;

let EQ_INTVECTORSCALE_6 = prove
 (`!a c. IntVectorScale_6_hol (lift_vec (\i. lift_intpoly (a i))) c =
         Value (lift_vec (\i. lift_intpoly (\k. a i k * c)))`,
  REPEAT GEN_TAC THEN NTT_ROWVEC_TAC IntVectorScale_6_hol_DEF []);;

let EQ_INTVECTORSCALE_8 = prove
 (`!a c. IntVectorScale_8_hol (lift_vec (\i. lift_intpoly (a i))) c =
         Value (lift_vec (\i. lift_intpoly (\k. a i k * c)))`,
  REPEAT GEN_TAC THEN NTT_ROWVEC_TAC IntVectorScale_8_hol_DEF []);;


let EQ_RQVECTORNEGATE_4 = prove
 (`!a. RqVectorNegate_4_hol (lift_vec (\i. lift_poly (a i))) =
       Value (lift_vec (\i. lift_poly (\k. --(a i k))))`,
  GEN_TAC THEN NTT_ROWVEC_TAC RqVectorNegate_4_hol_DEF []);;

let EQ_RQVECTORNEGATE_6 = prove
 (`!a. RqVectorNegate_6_hol (lift_vec (\i. lift_poly (a i))) =
       Value (lift_vec (\i. lift_poly (\k. --(a i k))))`,
  GEN_TAC THEN NTT_ROWVEC_TAC RqVectorNegate_6_hol_DEF []);;

let EQ_RQVECTORNEGATE_8 = prove
 (`!a. RqVectorNegate_8_hol (lift_vec (\i. lift_poly (a i))) =
       Value (lift_vec (\i. lift_poly (\k. --(a i k))))`,
  GEN_TAC THEN NTT_ROWVEC_TAC RqVectorNegate_8_hol_DEF []);;


(* ------------------------------------------------------------------------- *)
(* Matrix-vector product in the NTT domain: entry (i,j) is at index i*C+j.   *)
(* ------------------------------------------------------------------------- *)

let ntt_msum = define
 `ntt_msum 0 (f:num->int) = &0 /\
  ntt_msum (SUC n) f = ntt_msum n f + f n`;;

let NTT_MSUM_ISUM = prove
 (`!n f. ntt_msum n f = isum {j | j < n} f`,
  INDUCT_TAC THEN REWRITE_TAC[ntt_msum] THENL
   [REWRITE_TAC[LT; EMPTY_GSPEC; ISUM_CLAUSES];
    ASM_REWRITE_TAC[LT] THEN
    SUBGOAL_THEN `{j | j = n \/ j < n} = n INSERT {j | j < n}`
     SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM]; ALL_TAC] THEN
    SIMP_TAC[ISUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
    REWRITE_TAC[INT_ADD_SYM]]);;

let NTT_ACC_LOOP = prove
 (`!(p:num->P) (body:int->S->(S)native_result) (W:(P)list->S) l k n.
     k < LENGTH l /\ EL k l = p 0 /\
     (!j. j < n ==> body (&j) (W (isa_list_update l k (p j))) =
                    Value (W (isa_list_update l k (p (SUC j)))))
     ==> native_foldl body (list_of_seq (\j. &j) n) (W l) =
         Value (W (isa_list_update l k (p n)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `body:int->S->(S)native_result`; `\j. &j:int`;
                 `\j s. s = (W:(P)list->S) (isa_list_update l k ((p:num->P) j))`;
                 `(W:(P)list->S) l`] NTT_FOLDL_INV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [AP_TERM_TAC THEN MP_TAC(ISPECL [`l:P list`; `k:num`] NTT_ISA_UPDATE_SELF) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN MESON_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let NTT_MAT_EL = prove
 (`!(m:num->num->E) r c i j.
     i < r /\ j < c
     ==> EL (i * c + j) (list_of_seq (\n. m (n DIV c) (n MOD c)) (r * c)) =
         m i j`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_LIST_OF_SEQ o lhand o snd) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `i * c + c` THEN
    ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
    REWRITE_TAC[ARITH_RULE `i * c + c = (i + 1) * c`] THEN
    ASM_SIMP_TAC[LE_MULT_RCANCEL; ARITH_RULE `i < r ==> i + 1 <= r`];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(c = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT;
                 ADD_CLAUSES]]);;

let NTT_MAT_IDX_LT = prove
 (`!i j r c. i < r /\ j < c ==> i * c + j < r * c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `i * c + c` THEN
  ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
  REWRITE_TAC[ARITH_RULE `i * c + c = (i + 1) * c`] THEN
  ASM_SIMP_TAC[LE_MULT_RCANCEL; ARITH_RULE `i < r ==> i + 1 <= r`]);;

let NTT_MAT_EL_4_4 = prove
 (`!(m:num->num->E) i j. i < 4 /\ j < 4
     ==> EL (i * 4 + j) (list_of_seq (\n. m (n DIV 4) (n MOD 4)) 16) = m i j`,
  GEN_TAC THEN MP_TAC(SPECL [`4`;`4`] (ISPEC `m:num->num->E` NTT_MAT_EL)) THEN
  REWRITE_TAC[ARITH]);;

let NTT_MAT_RULES =
  [INT_OF_NUM_MUL; INT_OF_NUM_ADD];;

let NTT_MAT_DIM_RULES (r,c) =
  let ty n = type_of (parse_term ("(x:" ^ string_of_int n ^ ")")) in
  let th1 = REWRITE_RULE NTT_DIMS
              (INST_TYPE [ty r,`:R`; ty c,`:C`] EL_LIFT_MAT)
  and th2 = REWRITE_RULE NTT_DIMS
              (INST_TYPE [ty r,`:R`; ty c,`:C`] LENGTH_LIFT_MAT) in
  [th1; th2];;

let NTT_ZERO_POLY = prove
 (`(lift_poly (\q. &0):(A)fips204_poly) =
   FIPS204_Poly (REPLICATE 256 (FIPS204_Zq (residue_of_int_mod (&0))))`,
  REWRITE_TAC[lift_poly; lift_zq] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `!n. list_of_seq (\q. FIPS204_Zq (residue_of_int_mod (&0)))  n = REPLICATE n (FIPS204_Zq (residue_of_int_mod (&0)))` (fun th -> REWRITE_TAC[th]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[LIST_OF_SEQ; REPLICATE; o_DEF]);;

(* The product of a matrix with a vector: row k accumulates the products of  *)
(* its entries with the entries of the vector, column by column.             *)

let NTT_MATVEC_TAC defth rc ths =
  REWRITE_TAC[defth] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC NTT_SCHEDULES THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [lift_vec] THEN
  REWRITE_TAC NTT_DIMS THEN
  MATCH_MP_TAC NTT_LIST_LOOP_EL THEN REWRITE_TAC[LENGTH_MAP; LENGTH_REPLICATE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MATCH_MP_TAC (REWRITE_RULE[] (ISPEC
   `\j. lift_poly (\q. ntt_msum j (\j'. (m:num->num->num->int) k j' q *
                                        (v:num->num->int) j' q)):(fips204_ntt)fips204_poly`
   NTT_ACC_LOOP)) THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC[NTT_MAP_REPLICATE; NTT_EL_REPLICATE; ntt_msum; NTT_ZERO_POLY];
    REPEAT STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_SIMP_TAC(NTT_BODY_RULES @ NTT_VEC_RULES @ NTT_ROW_RULES @
                 [NTT_BIT_VALUE_F; INT_MUL_RZERO; INT_ADD_RID; EQ_ADDNTT;
                  EQ_MULTIPLYNTT; ntt_msum]) THEN
    REWRITE_TAC NTT_MAT_RULES THEN
    ASM_SIMP_TAC(NTT_BODY_RULES @ NTT_VEC_RULES @ NTT_MAT_DIM_RULES rc @
                 [NTT_MAT_IDX_LT; EQ_ADDNTT; EQ_MULTIPLYNTT; ntt_msum])];;

let EQ_MATRIXVECTORNTT_4_4_MLDSA44 = prove
 (`!m v. MatrixVectorNTT_4_4_MLDSA44_Configuration_hol
           (Common_Mat (lift_mat (\i j. lift_poly (m i j))))
           (lift_vec (\j. lift_poly (v j))) =
         Value (lift_vec (\i. lift_poly
                  (\q. ntt_msum 4 (\j. m i j q * v j q))))`,
  REPEAT GEN_TAC THEN
  NTT_MATVEC_TAC MatrixVectorNTT_4_4_MLDSA44_Configuration_hol_DEF (4,4) []);;

let EQ_MATRIXVECTORNTT_6_5_MLDSA65 = prove
 (`!m v. MatrixVectorNTT_6_5_MLDSA65_Configuration_hol
           (Common_Mat (lift_mat (\i j. lift_poly (m i j))))
           (lift_vec (\j. lift_poly (v j))) =
         Value (lift_vec (\i. lift_poly
                  (\q. ntt_msum 5 (\j. m i j q * v j q))))`,
  REPEAT GEN_TAC THEN
  NTT_MATVEC_TAC MatrixVectorNTT_6_5_MLDSA65_Configuration_hol_DEF (6,5) []);;

let EQ_MATRIXVECTORNTT_8_7_MLDSA87 = prove
 (`!m v. MatrixVectorNTT_8_7_MLDSA87_Configuration_hol
           (Common_Mat (lift_mat (\i j. lift_poly (m i j))))
           (lift_vec (\j. lift_poly (v j))) =
         Value (lift_vec (\i. lift_poly
                  (\q. ntt_msum 7 (\j. m i j q * v j q))))`,
  REPEAT GEN_TAC THEN
  NTT_MATVEC_TAC MatrixVectorNTT_8_7_MLDSA87_Configuration_hol_DEF (8,7) []);;


(* ------------------------------------------------------------------------- *)
(* Functions on lists of coefficient lists: FixedVectorSubtract,             *)
(* NegVectorNTT and ScaleVector.                                             *)
(* ------------------------------------------------------------------------- *)

(* The coefficient lists of a vector of n polynomials a i, as the generated  *)
(* code sees them in NegVectorNTT, ScaleVector and FixedVectorSubtract.      *)

let ntt_rows = new_definition
 `ntt_rows n (a:num->num->int) =
    list_of_seq (\i. list_of_seq (\k. lift_zq (a i k)) 256) n`;;

let NTT_LENGTH_ROWS = prove
 (`!n a. LENGTH (ntt_rows n a) = n`,
  REWRITE_TAC[ntt_rows; LENGTH_LIST_OF_SEQ]);;

let NTT_LIST_LOOP_ID = GEN `body:int->(B)list->((B)list)native_result` (REWRITE_RULE[]
  (ISPECL [`body:int->(B)list->((B)list)native_result`; `\l:B list. l`]
          NTT_LIST_LOOP_EL));;

let NTT_ROW_LOOP_ID = GEN `body:int->((Q)list)list->(((Q)list)list)native_result` (REWRITE_RULE[]
  (ISPECL [`body:int->((Q)list)list->(((Q)list)list)native_result`;
           `\l:(Q list) list. l`; `\cs:Q list. cs`] NTT_ROW_LOOP));;

let EQ_REDUCEMODQ = prove
 (`!x. ReduceModQ_hol x = Value (lift_zq x)`,
  REWRITE_TAC[ReduceModQ_hol_DEF; lift_zq; NTT_ISA_INT_MOD_Q] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[injectivity "native_result"; injectivity "fips204_zq"] THEN
  REWRITE_TAC[NTT_RESIDUE_EQ; GSYM INT_REM_EQ; INT_REM_REM]);;

let NTT_MAP_LIST_OF_SEQ = prove
 (`!(f:A->B) g n. MAP f (list_of_seq g n) = list_of_seq (\i. f (g i)) n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_MAP; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_MAP; EL_LIST_OF_SEQ; LENGTH_LIST_OF_SEQ]);;

let NTT_ROWLIST_LOOP_TAC ths =
  MATCH_MP_TAC NTT_LIST_LOOP_ID THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_REPLICATE; LENGTH_LIST_OF_SEQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MATCH_MP_TAC NTT_ROW_LOOP_ID THEN
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("EL",_),_),_)),
           Comb(Comb(Const("EL",_),_),_)) ->
        MP_TAC(REWRITE_RULE[NTT_MAP_REPLICATE] th)
    | _ -> failwith "no") THEN
  ASM_SIMP_TAC[NTT_EL_REPLICATE; EL_LIST_OF_SEQ; LENGTH_LIST_OF_SEQ] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("EL",_),_),_)),r) ->
        EXISTS_TAC r
    | _ -> failwith "no") THEN
  REPEAT CONJ_TAC THEN
  FIRST [REFL_TAC; ASM_ARITH_TAC;
         (REWRITE_TAC[LENGTH_MAP; LENGTH_REPLICATE; LENGTH_LIST_OF_SEQ] THEN NO_TAC);
         REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
         ASM_SIMP_TAC(NTT_BODY_RULES @ NTT_VEC_RULES @ NTT_ROW_RULES @
                      [ntt_rows; EQ_REDUCEMODQ] @ ths) THEN
         CONV_TAC(ONCE_DEPTH_CONV NTT_LIFT_ZQ_CONV) THEN
         REWRITE_TAC[INT_SUB_LZERO]];;

(* The wrappers: the list loop followed by Common_Vec (MAP FIPS204_Poly _).  *)

let NTT_FIXEDVEC_TAC defth rhs ths =
  REWRITE_TAC[defth] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC(NTT_SCHEDULE_256 :: NTT_SCHEDULES) THEN
  W(fun (asl,w) ->
    let cp = find_term NTT_IS_FOLDL w in
    SUBGOAL_THEN (mk_eq(cp, rhs)) SUBST1_TAC) THENL
   [NTT_ROWLIST_LOOP_TAC ths;
    REWRITE_TAC[NATIVE_BIND_VALUE; NTT_MAP_LIST_OF_SEQ; lift_vec; lift_poly] THEN
    REWRITE_TAC NTT_DIMS];;

let NTT_SLICE_NIL = prove
 (`typed_hol_read (typed_hol_list_slice ([]:A list) (&0) (&0)) = Value []`,
  REWRITE_TAC[typed_hol_list_slice_DEF; LENGTH; INT_LE_REFL; INT_SUB_REFL;
              TYPED_HOL_READ_SOME] THEN
  REWRITE_TAC[isa_nat; INT_LE_REFL; NUM_OF_INT_OF_NUM; isa_take; isa_drop;
              TYPED_HOL_READ_SOME] THEN
  REWRITE_TAC[INT_OF_NUM_EQ; INT_LE_REFL; isa_take; isa_drop; TYPED_HOL_READ_SOME]);;

let NTT_LISTVEC_HEAD =
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ISA_NAT_NUM; REPLICATE; NTT_SLICE_NIL; NATIVE_BIND_VALUE;
              NTT_LENGTH_ROWS; NATIVE_SCHEDULE_COUNT; NTT_SCHEDULE_256];;

let EQ_NEGVECTORNTT = prove
 (`!n a. NegVectorNTT_hol (ntt_rows n a) =
         Value (ntt_rows n (\i k. --(a i k)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NegVectorNTT_hol_DEF] THEN
  NTT_LISTVEC_HEAD THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ntt_rows] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ntt_rows] THEN
  NTT_ROWLIST_LOOP_TAC []);;

let EQ_SCALEVECTOR = prove
 (`!n a c. ScaleVector_hol (ntt_rows n a) c =
           Value (ntt_rows n (\i k. a i k * c))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ScaleVector_hol_DEF] THEN
  NTT_LISTVEC_HEAD THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ntt_rows] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ntt_rows] THEN
  NTT_ROWLIST_LOOP_TAC []);;

let EQ_FIXEDVECTORSUBTRACT_4_BODY = prove
 (`!a b. FixedVectorSubtract_4_body_hol (ntt_rows 4 a) (ntt_rows 4 b) =
         Value (ntt_rows 4 (\i k. a i k - b i k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FixedVectorSubtract_4_body_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC(NTT_SCHEDULE_256 :: NTT_SCHEDULES) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ntt_rows] THEN
  NTT_ROWLIST_LOOP_TAC []);;

let EQ_FIXEDVECTORSUBTRACT_4_TIME = prove
 (`!a b. FixedVectorSubtract_4_FIPS204_Time_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k - b i k)))`,
  REPEAT GEN_TAC THEN
  NTT_FIXEDVEC_TAC FixedVectorSubtract_4_FIPS204_Time_hol_DEF
   `Value (list_of_seq (\i. list_of_seq (\k. lift_zq ((a:num->num->int) i k - (b:num->num->int) i k)) 256) 4)` []);;

let EQ_FIXEDVECTORSUBTRACT_4_NTT = prove
 (`!a b. FixedVectorSubtract_4_FIPS204_NTT_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k - b i k)))`,
  REPEAT GEN_TAC THEN
  NTT_FIXEDVEC_TAC FixedVectorSubtract_4_FIPS204_NTT_hol_DEF
   `Value (list_of_seq (\i. list_of_seq (\k. lift_zq ((a:num->num->int) i k - (b:num->num->int) i k)) 256) 4)` []);;

let EQ_FIXEDVECTORSUBTRACT_6_BODY = prove
 (`!a b. FixedVectorSubtract_6_body_hol (ntt_rows 6 a) (ntt_rows 6 b) =
         Value (ntt_rows 6 (\i k. a i k - b i k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FixedVectorSubtract_6_body_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC(NTT_SCHEDULE_256 :: NTT_SCHEDULES) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ntt_rows] THEN
  NTT_ROWLIST_LOOP_TAC []);;

let EQ_FIXEDVECTORSUBTRACT_6_TIME = prove
 (`!a b. FixedVectorSubtract_6_FIPS204_Time_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k - b i k)))`,
  REPEAT GEN_TAC THEN
  NTT_FIXEDVEC_TAC FixedVectorSubtract_6_FIPS204_Time_hol_DEF
   `Value (list_of_seq (\i. list_of_seq (\k. lift_zq ((a:num->num->int) i k - (b:num->num->int) i k)) 256) 6)` []);;

let EQ_FIXEDVECTORSUBTRACT_6_NTT = prove
 (`!a b. FixedVectorSubtract_6_FIPS204_NTT_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k - b i k)))`,
  REPEAT GEN_TAC THEN
  NTT_FIXEDVEC_TAC FixedVectorSubtract_6_FIPS204_NTT_hol_DEF
   `Value (list_of_seq (\i. list_of_seq (\k. lift_zq ((a:num->num->int) i k - (b:num->num->int) i k)) 256) 6)` []);;

let EQ_FIXEDVECTORSUBTRACT_8_BODY = prove
 (`!a b. FixedVectorSubtract_8_body_hol (ntt_rows 8 a) (ntt_rows 8 b) =
         Value (ntt_rows 8 (\i k. a i k - b i k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FixedVectorSubtract_8_body_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC(NTT_SCHEDULE_256 :: NTT_SCHEDULES) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ntt_rows] THEN
  NTT_ROWLIST_LOOP_TAC []);;

let EQ_FIXEDVECTORSUBTRACT_8_TIME = prove
 (`!a b. FixedVectorSubtract_8_FIPS204_Time_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k - b i k)))`,
  REPEAT GEN_TAC THEN
  NTT_FIXEDVEC_TAC FixedVectorSubtract_8_FIPS204_Time_hol_DEF
   `Value (list_of_seq (\i. list_of_seq (\k. lift_zq ((a:num->num->int) i k - (b:num->num->int) i k)) 256) 8)` []);;

let EQ_FIXEDVECTORSUBTRACT_8_NTT = prove
 (`!a b. FixedVectorSubtract_8_FIPS204_NTT_hol
           (lift_vec (\i. lift_poly (a i))) (lift_vec (\i. lift_poly (b i))) =
         Value (lift_vec (\i. lift_poly (\k. a i k - b i k)))`,
  REPEAT GEN_TAC THEN
  NTT_FIXEDVEC_TAC FixedVectorSubtract_8_FIPS204_NTT_hol_DEF
   `Value (list_of_seq (\i. list_of_seq (\k. lift_zq ((a:num->num->int) i k - (b:num->num->int) i k)) 256) 8)` []);;


(* ------------------------------------------------------------------------- *)
(* The composite used by the callers: NTTInv(A^ * NTT(y)) is A * y.          *)
(* ------------------------------------------------------------------------- *)


(* The row i of A * y computed by the generated code in the NTT domain, and  *)
(* transformed back, is the handwritten dot product of the row with y.       *)

let NTT_DOT_ROW = prove
 (`!n a y.
     (!j k. j < n /\ k < 256 ==> &0 <= a j k /\ a j k < &8380417) /\
     (!j. j < n ==> y j IN ring_carrier mldsa_rq)
     ==> mldsa_dot n (\j. mldsa_ntt_inv (a j)) y =
         mldsa_ntt_inv
          (\k. ntt_msum n (\j. a j k * mldsa_ntt (y j) k) rem &8380417)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `a:num->num->int`; `y:num->(1->num)->int`]
              MLDSA_DOT_NTT_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC MLDSA_NTT_INV_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[NTT_MSUM_ISUM] THEN
  MP_TAC(ISPECL [`{j | j < n}`; `\j. (a:num->num->int) j k * mldsa_ntt (y j) k`]
               MLDSA_ZQ_RING_SUM) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MLDSA_ZQ]);;

let NTT_REM_RANGE = prove
 (`!x. &0 <= x rem &8380417 /\ x rem &8380417 < &8380417`,
  GEN_TAC THEN REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV);;

let EQ_MATVEC_NTTINV_4_4_MLDSA44 = prove
 (`!a y. (!i j k. i < 4 /\ j < 4 /\ k < 256
                  ==> &0 <= a i j k /\ a i j k < &8380417) /\
         (!j. j < 4 ==> y j IN ring_carrier mldsa_rq)
         ==> native_bind
              (VectorNTT_4_MLDSA44_Configuration_hol
                (lift_vec (\j. lift_poly (\k. coeff k (y j)))))
              (\yh. native_bind
                     (MatrixVectorNTT_4_4_MLDSA44_Configuration_hol
                       (Common_Mat (lift_mat (\i j. lift_poly (a i j)))) yh)
                     VectorNTTInv_4_MLDSA44_Configuration_hol) =
             Value (lift_vec
                     (\i. lift_poly
                           (\k. coeff k (mldsa_dot 4
                                  (\j. mldsa_ntt_inv (a i j)) y))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EQ_VECTORNTT_4_MLDSA44; NATIVE_BIND_VALUE] THEN
  SUBGOAL_THEN
   `(lift_vec (\j. lift_poly (mldsa_ntt (mldsa_poly (\k. coeff k (y j))))):
     (4,(fips204_ntt)fips204_poly)common_vec) =
    lift_vec (\j. lift_poly (mldsa_ntt (y j)))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC LIFT_VEC_CONG THEN REWRITE_TAC NTT_DIMS THEN
    ASM_SIMP_TAC[MLDSA_POLY_COEFF];
    ALL_TAC] THEN
  REWRITE_TAC[EQ_MATRIXVECTORNTT_4_4_MLDSA44; NATIVE_BIND_VALUE] THEN
  MP_TAC(SPEC `\i q. ntt_msum 4 (\j. (a:num->num->num->int) i j q *
                                     mldsa_ntt ((y:num->(1->num)->int) j) q)
                     rem &8380417` EQ_VECTORNTTINV_4_MLDSA44) THEN
  REWRITE_TAC[NTT_REM_RANGE; NTT_LIFT_POLY_REM] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LIFT_VEC_CONG THEN
  REWRITE_TAC NTT_DIMS THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(SPECL [`4`; `(a:num->num->num->int) i`; `y:num->(1->num)->int`]
               NTT_DOT_ROW) THEN
  ASM_SIMP_TAC[]);;

let EQ_MATVEC_NTTINV_6_5_MLDSA65 = prove
 (`!a y. (!i j k. i < 6 /\ j < 5 /\ k < 256
                  ==> &0 <= a i j k /\ a i j k < &8380417) /\
         (!j. j < 5 ==> y j IN ring_carrier mldsa_rq)
         ==> native_bind
              (VectorNTT_5_MLDSA65_Configuration_hol
                (lift_vec (\j. lift_poly (\k. coeff k (y j)))))
              (\yh. native_bind
                     (MatrixVectorNTT_6_5_MLDSA65_Configuration_hol
                       (Common_Mat (lift_mat (\i j. lift_poly (a i j)))) yh)
                     VectorNTTInv_6_MLDSA65_Configuration_hol) =
             Value (lift_vec
                     (\i. lift_poly
                           (\k. coeff k (mldsa_dot 5
                                  (\j. mldsa_ntt_inv (a i j)) y))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EQ_VECTORNTT_5_MLDSA65; NATIVE_BIND_VALUE] THEN
  SUBGOAL_THEN
   `(lift_vec (\j. lift_poly (mldsa_ntt (mldsa_poly (\k. coeff k (y j))))):
     (5,(fips204_ntt)fips204_poly)common_vec) =
    lift_vec (\j. lift_poly (mldsa_ntt (y j)))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC LIFT_VEC_CONG THEN REWRITE_TAC NTT_DIMS THEN
    ASM_SIMP_TAC[MLDSA_POLY_COEFF];
    ALL_TAC] THEN
  REWRITE_TAC[EQ_MATRIXVECTORNTT_6_5_MLDSA65; NATIVE_BIND_VALUE] THEN
  MP_TAC(SPEC `\i q. ntt_msum 5 (\j. (a:num->num->num->int) i j q *
                                     mldsa_ntt ((y:num->(1->num)->int) j) q)
                     rem &8380417` EQ_VECTORNTTINV_6_MLDSA65) THEN
  REWRITE_TAC[NTT_REM_RANGE; NTT_LIFT_POLY_REM] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LIFT_VEC_CONG THEN
  REWRITE_TAC NTT_DIMS THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(SPECL [`5`; `(a:num->num->num->int) i`; `y:num->(1->num)->int`]
               NTT_DOT_ROW) THEN
  ASM_SIMP_TAC[]);;

let EQ_MATVEC_NTTINV_8_7_MLDSA87 = prove
 (`!a y. (!i j k. i < 8 /\ j < 7 /\ k < 256
                  ==> &0 <= a i j k /\ a i j k < &8380417) /\
         (!j. j < 7 ==> y j IN ring_carrier mldsa_rq)
         ==> native_bind
              (VectorNTT_7_MLDSA87_Configuration_hol
                (lift_vec (\j. lift_poly (\k. coeff k (y j)))))
              (\yh. native_bind
                     (MatrixVectorNTT_8_7_MLDSA87_Configuration_hol
                       (Common_Mat (lift_mat (\i j. lift_poly (a i j)))) yh)
                     VectorNTTInv_8_MLDSA87_Configuration_hol) =
             Value (lift_vec
                     (\i. lift_poly
                           (\k. coeff k (mldsa_dot 7
                                  (\j. mldsa_ntt_inv (a i j)) y))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EQ_VECTORNTT_7_MLDSA87; NATIVE_BIND_VALUE] THEN
  SUBGOAL_THEN
   `(lift_vec (\j. lift_poly (mldsa_ntt (mldsa_poly (\k. coeff k (y j))))):
     (7,(fips204_ntt)fips204_poly)common_vec) =
    lift_vec (\j. lift_poly (mldsa_ntt (y j)))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC LIFT_VEC_CONG THEN REWRITE_TAC NTT_DIMS THEN
    ASM_SIMP_TAC[MLDSA_POLY_COEFF];
    ALL_TAC] THEN
  REWRITE_TAC[EQ_MATRIXVECTORNTT_8_7_MLDSA87; NATIVE_BIND_VALUE] THEN
  MP_TAC(SPEC `\i q. ntt_msum 7 (\j. (a:num->num->num->int) i j q *
                                     mldsa_ntt ((y:num->(1->num)->int) j) q)
                     rem &8380417` EQ_VECTORNTTINV_8_MLDSA87) THEN
  REWRITE_TAC[NTT_REM_RANGE; NTT_LIFT_POLY_REM] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LIFT_VEC_CONG THEN
  REWRITE_TAC NTT_DIMS THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(SPECL [`7`; `(a:num->num->num->int) i`; `y:num->(1->num)->int`]
               NTT_DOT_ROW) THEN
  ASM_SIMP_TAC[]);;
