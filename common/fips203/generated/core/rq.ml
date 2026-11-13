(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* R_q bridge lemmas, compression, CBD sampling and addition.                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Bridge lemmas between zpoly / zqlist and R_q.                             *)
(* ------------------------------------------------------------------------- *)

let ZPOLY_IN_RQ = prove(ZPOLY_IN_RQ_STMT,
  REWRITE_TAC[zpoly; MLKEM_POLY_IN_RQ]);;

let COEFF_ZPOLY = prove(COEFF_ZPOLY_STMT,
  SIMP_TAC[zpoly; COEFF_MLKEM_POLY]);;

let ZPOLY_ZQLIST = prove(ZPOLY_ZQLIST_STMT,
  GEN_TAC THEN REWRITE_TAC[zpoly; mlkem_poly; FUN_EQ_THM] THEN
  X_GEN_TAC `m:1->num` THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[zarr; GSYM zarr; ZARR_ZQLIST; INT_REM_REM]);;

let ZPOLY_ZQLIST_COEFF = prove(ZPOLY_ZQLIST_COEFF_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ZPOLY_ZQLIST] THEN
  ASM_SIMP_TAC[MLKEM_POLY_COEFF]);;

let RQ_MEM_LIST_OF_SEQ = prove
 (`!(s:num->A) n x. MEM x (list_of_seq s n) <=> ?i. i < n /\ x = s i`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; MEM; CONJUNCT1 LT; MEM_APPEND] THEN
  ASM_REWRITE_TAC[LT] THEN MESON_TAC[]);;

let RQ_EQUIV_FOLDL_APPEND = prove
 (`!(g:I->S->S) s l1 l2.
     equiv_foldl g s (APPEND l1 l2) = equiv_foldl g (equiv_foldl g s l1) l2`,
  GEN_TAC THEN GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; equiv_foldl]);;

let rq_fill = new_definition
 `rq_fill (f:num->A) s k =
    equiv_foldl (\x t. isa_list_update t (isa_nat x) (f (isa_nat x))) s
                (list_of_seq (\i. &i) k)`;;

let RQ_FILL_CLAUSES = prove
 (`(!(f:num->A) s. rq_fill f s 0 = s) /\
   (!(f:num->A) s k. rq_fill f s (SUC k) =
                     isa_list_update (rq_fill f s k) k (f k))`,
  REWRITE_TAC[rq_fill; list_of_seq; equiv_foldl;
              RQ_EQUIV_FOLDL_APPEND] THEN
  REWRITE_TAC[equiv_foldl; ISA_NAT_NUM]);;

let RQ_LENGTH_FILL = prove
 (`!(f:num->A) s k. LENGTH (rq_fill f s k) = LENGTH s`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[RQ_FILL_CLAUSES; LENGTH_ISA_LIST_UPDATE]);;

let RQ_EL_FILL = prove
 (`!(f:num->A) s k j.
     j < LENGTH s
     ==> EL j (rq_fill f s k) = if j < k then f j else EL j s`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[RQ_FILL_CLAUSES; CONJUNCT1 LT] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_ISA_LIST_UPDATE; RQ_LENGTH_FILL] THEN
  ASM_CASES_TAC `j:num = k` THEN ASM_REWRITE_TAC[LT_REFL; LT] THEN
  ASM_MESON_TAC[]);;


let RQ_EQUIV_FOLDL_WRAP = prove
 (`!(C:A list->S) (D:S->A list) (g:I->A list->A list) l s.
     (!x. D (C x) = x)
     ==> equiv_foldl (\x p. C (g x (D p))) (C s) l = C (equiv_foldl g s l)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SPEC_TAC(`s:A list`,`s:A list`) THEN
  SPEC_TAC(`l:I list`,`l:I list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[equiv_foldl]);;

let RQ_NATIVE_FOLDL_FILL_WRAP = prove
 (`!(C:A list->S) (D:S->A list) (body:int->S->(S)native_result) (f:num->A) n s.
     (!x. D (C x) = x) /\ (!p. C (D p) = p) /\
     LENGTH s = n /\
     (!i t. i < n /\ LENGTH t = n
            ==> body (&i) (C t) = Value (C (isa_list_update t i (f i))))
     ==> native_foldl body (list_of_seq (\i. &i) n) (C s) =
         Value (C (list_of_seq f n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`body:int->S->(S)native_result`;
    `\x p. (C:A list->S) (isa_list_update ((D:S->A list) p) (isa_nat x)
                            ((f:num->A) (isa_nat x)))`;
    `\p:S. LENGTH ((D:S->A list) p) = n`;
    `list_of_seq (\i. &i) n :int list`;
    `(C:A list->S) s`] NATIVE_FOLDL_VALUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[RQ_MEM_LIST_OF_SEQ] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)
                               ASSUME_TAC) THEN
    ASM_REWRITE_TAC[ISA_NAT_NUM; LENGTH_ISA_LIST_UPDATE] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `(D:S->A list) t`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `equiv_foldl (\x p. (C:A list->S) (isa_list_update ((D:S->A list) p) (isa_nat x)
                            ((f:num->A) (isa_nat x)))) (C s) (list_of_seq (\i. &i) n)
    = C (rq_fill f s n)` SUBST1_TAC THENL
   [REWRITE_TAC[rq_fill] THEN
    MP_TAC(ISPECL [`C:A list->S`; `D:S->A list`;
      `\x t. isa_list_update (t:A list) (isa_nat (x:int)) ((f:num->A) (isa_nat x))`;
      `list_of_seq (\i. &i) n :int list`; `s:A list`] RQ_EQUIV_FOLDL_WRAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[BETA_RULE th]);
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[LIST_EQ] THEN
  ASM_REWRITE_TAC[RQ_LENGTH_FILL; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; RQ_EL_FILL]);;

let RQ_COMPRESS_TAC defn rty =
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[defn; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MP_TAC(SPECL [`257`;`0`;`256`] NATIVE_SCHEDULE_UPTO) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN
  MATCH_MP_TAC NATIVE_FOLDL_FILL THEN REWRITE_TAC[LENGTH_REPLICATE] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; mk_var("t",mk_type("list",[rty]))] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `i < LENGTH (l:fips203_zq list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[zq_list_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:int y:int. &0 < y ==>
                typed_hol_int_arithmetic ADiv x y = Value (x div y)`
   (fun th -> REWRITE_TAC[MATCH_MP th (INT_ARITH `&0:int < &2`);
                          MATCH_MP th (INT_ARITH `&0:int < &3329`)]) THENL
   [MESON_TAC[INT_ARITH_ADIV]; ALL_TAC] THEN
  ASM_SIMP_TAC[fips203_poly_SEL_CTR; NATIVE_LIST_INDEX; NATIVE_BIND_VALUE;
               INT_ARITH_APOW; NATIVE_LIST_UPDATE; ISA_INT_MOD_POS;
               INT_ARITH `&0:int < &2`; INT_ARITH `&0:int < &3329`;
               INT_ARITH `&0:int < &16`; INT_ARITH `&0:int < &32`;
               INT_ARITH `&0:int < &1024`; INT_ARITH `&0:int < &2048`] THEN
  REWRITE_TAC[GSYM RQ_COMPRESS_ARITH; zarr; fz] THEN
  CONV_TAC INT_REDUCE_CONV;;

let COMPRESS_1 = prove(COMPRESS_1_STMT,
  RQ_COMPRESS_TAC Compress_d_1_2_hol_DEF `:(2)residue`);;

let COMPRESS_4 = prove(COMPRESS_4_STMT,
  RQ_COMPRESS_TAC Compress_d_4_16_hol_DEF `:(16)residue`);;

let COMPRESS_5 = prove(COMPRESS_5_STMT,
  RQ_COMPRESS_TAC Compress_d_5_32_hol_DEF `:(32)residue`);;

let COMPRESS_10 = prove(COMPRESS_10_STMT,
  RQ_COMPRESS_TAC Compress_d_10_1024_hol_DEF `:(1024)residue`);;

let COMPRESS_11 = prove(COMPRESS_11_STMT,
  RQ_COMPRESS_TAC Compress_d_11_2048_hol_DEF `:(2048)residue`);;


let RQ_RESIDUE_REM = prove
 (`!x. (residue_of_int_mod (x rem &3329):(3329)residue) = residue_of_int_mod x`,
  GEN_TAC THEN REWRITE_TAC[residue_of_int_mod_DEF] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  ASM_SIMP_TAC[ISA_INT_MOD_POS; INT_ARITH `&0:int < &3329`; INT_REM_REM]);;

let RQ_ADIV_POW2 = prove
 (`!a k. typed_hol_int_arithmetic ADiv a (&2 pow k) = Value (a div &2 pow k)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC INT_ARITH_ADIV THEN
  MATCH_MP_TAC INT_POW_LT THEN INT_ARITH_TAC);;

let RQ_DECOMPRESS_TAC defn d rty =
  let dm1 = mk_small_numeral (d - 1) in
  let arith =
    CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)
     (SPECL [dm1; `y:int`] RQ_DECOMPRESS_ARITH) in
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[defn; LET_DEF; LET_END_DEF; zqlist] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MP_TAC(SPECL [`257`;`0`;`256`] NATIVE_SCHEDULE_UPTO) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN
  MATCH_MP_TAC(ISPECL [`FIPS203_Poly:(fips203_zq)list->(P)fips203_poly`;
                       `fips203_poly_coefficients:(P)fips203_poly->(fips203_zq)list`]
    RQ_NATIVE_FOLDL_FILL_WRAP) THEN
  REWRITE_TAC[fips203_poly_SEL_CTR; fips203_poly_CTR_SEL; LENGTH_MAP;
              LENGTH_REPLICATE] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `t:(fips203_zq)list`] THEN
  STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ASM_SIMP_TAC[NATIVE_LIST_INDEX; NATIVE_BIND_VALUE; INT_ARITH_APOW;
               RQ_ADIV_POW2; ISA_INT_MOD_POS; INT_ARITH `&0:int < &3329`] THEN
  ASM_SIMP_TAC[NOMINAL_UPDATE_POLY] THEN
  REWRITE_TAC[arith] THEN
  REWRITE_TAC[RQ_RESIDUE_REM];;

let DECOMPRESS_1 = prove(DECOMPRESS_1_STMT,
  RQ_DECOMPRESS_TAC Decompress_d_1_hol_DEF 1 `:(2)residue`);;

let DECOMPRESS_4 = prove(DECOMPRESS_4_STMT,
  RQ_DECOMPRESS_TAC Decompress_d_4_hol_DEF 4 `:(16)residue`);;

let DECOMPRESS_5 = prove(DECOMPRESS_5_STMT,
  RQ_DECOMPRESS_TAC Decompress_d_5_hol_DEF 5 `:(32)residue`);;

let DECOMPRESS_10 = prove(DECOMPRESS_10_STMT,
  RQ_DECOMPRESS_TAC Decompress_d_10_hol_DEF 10 `:(1024)residue`);;

let DECOMPRESS_11 = prove(DECOMPRESS_11_STMT,
  RQ_DECOMPRESS_TAC Decompress_d_11_hol_DEF 11 `:(2048)residue`);;
let RQ_COEFF_ADD = prove
 (`!f g n. n < 256
           ==> coeff n (ring_add mlkem_rq (zpoly f) (zpoly g)) =
               (zarr f n + zarr g n) rem &3329`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MLKEM_RQ_COEFF_ADD; ZPOLY_IN_RQ; COEFF_ZPOLY; mlkem_zq;
               INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let RQ_COEFF_SUB = prove
 (`!f g n. n < 256
           ==> coeff n (ring_sub mlkem_rq (zpoly f) (zpoly g)) =
               (zarr f n - zarr g n) rem &3329`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MLKEM_RQ_COEFF_SUB; ZPOLY_IN_RQ; COEFF_ZPOLY; mlkem_zq;
               INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let RQ_POLYADD_TAC defn coeff_lemma =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[defn; LET_DEF; LET_END_DEF; zqlist] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MP_TAC(SPECL [`257`;`0`;`256`] NATIVE_SCHEDULE_UPTO) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN
  MATCH_MP_TAC(ISPECL [`FIPS203_Poly:(fips203_zq)list->(P)fips203_poly`;
                       `fips203_poly_coefficients:(P)fips203_poly->(fips203_zq)list`]
    RQ_NATIVE_FOLDL_FILL_WRAP) THEN
  REWRITE_TAC[fips203_poly_SEL_CTR; fips203_poly_CTR_SEL; LENGTH_MAP;
              LENGTH_REPLICATE] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `t:(fips203_zq)list`] THEN
  STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN `i < LENGTH (f:fips203_zq list) /\ i < LENGTH (g:fips203_zq list)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[zq_list_ok]; ALL_TAC] THEN
  ASM_SIMP_TAC[fips203_poly_SEL_CTR; NATIVE_LIST_INDEX; NATIVE_BIND_VALUE] THEN
  ASM_SIMP_TAC[NOMINAL_UPDATE_POLY] THEN
  ASM_SIMP_TAC[coeff_lemma; zarr; fz; RQ_RESIDUE_REM];;

let RQPOLYADD_HOL_EQ = prove(RQPOLYADD_HOL_EQ_STMT,
  RQ_POLYADD_TAC RqPolyAdd_hol_DEF RQ_COEFF_ADD);;

let RQPOLYSUB_HOL_EQ = prove(RQPOLYSUB_HOL_EQ_STMT,
  RQ_POLYADD_TAC RqPolySub_hol_DEF RQ_COEFF_SUB);;

(* ------------------------------------------------------------------------- *)
(* Vectors.                                                                  *)
(* ------------------------------------------------------------------------- *)

let RQ_EL_ZVEC = prove
 (`!k (v:num->fips203_zq list) i.
     i < k
     ==> EL i (common_vec_entries (zvec k v:(A,(P)fips203_poly)common_vec)) =
         FIPS203_Poly (v i)`,
  REWRITE_TAC[zvec; common_vec_SEL_CTR] THEN
  SIMP_TAC[EL_LIST_OF_SEQ]);;

let RQ_LENGTH_ZVEC = prove
 (`!k (v:num->fips203_zq list).
     LENGTH (common_vec_entries (zvec k v:(A,(P)fips203_poly)common_vec)) = k`,
  REWRITE_TAC[zvec; common_vec_SEL_CTR; LENGTH_LIST_OF_SEQ]);;

let RQ_COMPRESSVECTOR_TAC defn polylem k =
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[defn; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MP_TAC(SPECL [mk_small_numeral (k+1); `0`; mk_small_numeral k]
               NATIVE_SCHEDULE_UPTO) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN
  MATCH_MP_TAC NATIVE_FOLDL_FILL THEN REWRITE_TAC[LENGTH_REPLICATE] THEN
  X_GEN_TAC `i:num` THEN GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ASM_SIMP_TAC[TYPED_HOL_NONNEGATIVE; NATIVE_BIND_VALUE;
               RQ_LENGTH_ZVEC; NATIVE_LIST_INDEX; RQ_EL_ZVEC] THEN
  ASM_SIMP_TAC[polylem; NATIVE_BIND_VALUE; NATIVE_LIST_UPDATE];;

let RQ_VECFILL_TAC defn simps k =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[defn; LET_DEF; LET_END_DEF; zvec] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MP_TAC(SPECL [mk_small_numeral (k+1); `0`; mk_small_numeral k]
               NATIVE_SCHEDULE_UPTO) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN
  MATCH_MP_TAC(ISPECL [`Common_Vec:B list->(A,B)common_vec`; `common_vec_entries:(A,B)common_vec->B list`]
    RQ_NATIVE_FOLDL_FILL_WRAP) THEN
  REWRITE_TAC[common_vec_SEL_CTR; common_vec_CTR_SEL; LENGTH_MAP;
              LENGTH_REPLICATE] THEN
  X_GEN_TAC `i:num` THEN GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ASM_SIMP_TAC[TYPED_HOL_NONNEGATIVE; NATIVE_BIND_VALUE] THEN
  ASM_SIMP_TAC(simps @
     [NATIVE_BIND_VALUE; NATIVE_LIST_INDEX; RQ_EL_ZVEC; RQ_LENGTH_ZVEC;
      zvec; common_vec_SEL_CTR; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]) THEN
  ASM_SIMP_TAC[NOMINAL_UPDATE_VEC];;
let COMPRESSVECTOR_2 = prove(COMPRESSVECTOR_2_STMT,
  RQ_COMPRESSVECTOR_TAC CompressVector_d_10_1024_2_MLKEM512_Configuration_hol_DEF COMPRESS_10 2);;

let DECOMPRESSVECTOR_2 = prove(DECOMPRESSVECTOR_2_STMT,
  RQ_VECFILL_TAC DecompressVector_d_10_1024_2_MLKEM512_Configuration_hol_DEF [DECOMPRESS_10] 2);;

let RQVECTORADD_2 = prove(RQVECTORADD_2_STMT,
  RQ_VECFILL_TAC RqVectorAdd_2_MLKEM512_Configuration_hol_DEF [RQPOLYADD_HOL_EQ] 2);;

let COMPRESSVECTOR_3 = prove(COMPRESSVECTOR_3_STMT,
  RQ_COMPRESSVECTOR_TAC CompressVector_d_10_1024_3_MLKEM768_Configuration_hol_DEF COMPRESS_10 3);;

let DECOMPRESSVECTOR_3 = prove(DECOMPRESSVECTOR_3_STMT,
  RQ_VECFILL_TAC DecompressVector_d_10_1024_3_MLKEM768_Configuration_hol_DEF [DECOMPRESS_10] 3);;

let RQVECTORADD_3 = prove(RQVECTORADD_3_STMT,
  RQ_VECFILL_TAC RqVectorAdd_3_MLKEM768_Configuration_hol_DEF [RQPOLYADD_HOL_EQ] 3);;

let COMPRESSVECTOR_4 = prove(COMPRESSVECTOR_4_STMT,
  RQ_COMPRESSVECTOR_TAC CompressVector_d_11_2048_4_MLKEM1024_Configuration_hol_DEF COMPRESS_11 4);;

let DECOMPRESSVECTOR_4 = prove(DECOMPRESSVECTOR_4_STMT,
  RQ_VECFILL_TAC DecompressVector_d_11_2048_4_MLKEM1024_Configuration_hol_DEF [DECOMPRESS_11] 4);;

let RQVECTORADD_4 = prove(RQVECTORADD_4_STMT,
  RQ_VECFILL_TAC RqVectorAdd_4_MLKEM1024_Configuration_hol_DEF [RQPOLYADD_HOL_EQ] 4);;


(* ------------------------------------------------------------------------- *)
(* CBD sampling.                                                             *)
(* ------------------------------------------------------------------------- *)

let RQ_BIND_FOLDL_FILL = prove
 (`!(f:num->A) n (s:A list) (body:int->(A)list->((A)list)native_result)
    (K:(A)list->(B)native_result).
   LENGTH s = n /\
   (!i t. i < n /\ LENGTH t = n
          ==> body (&i) t = Value (isa_list_update t i (f i)))
   ==> native_bind (native_foldl body (list_of_seq (\i. &i) n) s) K =
       K (list_of_seq f n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`body:int->(A)list->((A)list)native_result`; `f:num->A`;
                 `n:num`; `s:A list`] NATIVE_FOLDL_FILL) THEN
  ASM_REWRITE_TAC[NATIVE_BIND_VALUE] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NATIVE_BIND_VALUE]);;

let RQ_LOS2 = prove
 (`!(f:num->A). list_of_seq f 2 = [f 0; f 1]`,
  REWRITE_TAC[ARITH_RULE `2 = SUC 1 /\ 1 = SUC 0`; list_of_seq; APPEND] THEN
  REWRITE_TAC[ARITH_RULE `0 + 1 = 1`; ADD_CLAUSES]);;

let RQ_LOS3 = prove
 (`!(f:num->A). list_of_seq f 3 = [f 0; f 1; f 2]`,
  REWRITE_TAC[ARITH_RULE `3 = SUC 2 /\ 2 = SUC 1 /\ 1 = SUC 0`; list_of_seq;
              APPEND] THEN
  REWRITE_TAC[ADD_CLAUSES]);;

let RQ_BITVAL_ODD = prove
 (`!x. bitval (ODD x) = x MOD 2`,
  GEN_TAC THEN REWRITE_TAC[bitval; ODD_MOD] THEN
  MP_TAC(SPEC `x:num` (ARITH_RULE `!x. x MOD 2 = 0 \/ x MOD 2 = 1`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ]);;

let RQ_NSUM_LT2 = prove
 (`!f. nsum {j | j < 2} f = f 0 + f 1`,
  GEN_TAC THEN
  SUBGOAL_THEN `{j | j < 2} = {0, 1}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC;
    SIMP_TAC[NSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
             NOT_IN_EMPTY; ARITH_EQ] THEN ARITH_TAC]);;

let RQ_NSUM_LT3 = prove
 (`!f. nsum {j | j < 3} f = f 0 + f 1 + f 2`,
  GEN_TAC THEN
  SUBGOAL_THEN `{j | j < 3} = 2 INSERT {j | j < 2}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN ARITH_TAC;
    SIMP_TAC[NSUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; ARITH;
             RQ_NSUM_LT2] THEN ARITH_TAC]);;

let RQ_BIT_IDX_2A = prove
 (`!X i k. i < 256 /\ k < 2
   ==> typed_hol_read (native_list_index
         (list_of_seq (\n. ODD (X DIV 2 EXP n)) 1024) (&((2 * i) * 2 + k))) =
       Value (ODD (X DIV 2 EXP ((2 * i) * 2 + k)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`list_of_seq (\n. ODD (X DIV 2 EXP n)) 1024`; `(2 * i) * 2 + k`]
    NATIVE_LIST_INDEX) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  SUBGOAL_THEN `(2 * i) * 2 + k < 1024` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

let RQ_BIT_IDX_2B = prove
 (`!X i k. i < 256 /\ k < 2
   ==> typed_hol_read (native_list_index
         (list_of_seq (\n. ODD (X DIV 2 EXP n)) 1024) (&(((2 * i) * 2 + 2) + k))) =
       Value (ODD (X DIV 2 EXP (((2 * i) * 2 + 2) + k)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`list_of_seq (\n. ODD (X DIV 2 EXP n)) 1024`; `((2 * i) * 2 + 2) + k`]
    NATIVE_LIST_INDEX) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  SUBGOAL_THEN `((2 * i) * 2 + 2) + k < 1024` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

let RQ_BIT_IDX_3A = prove
 (`!X i k. i < 256 /\ k < 3
   ==> typed_hol_read (native_list_index
         (list_of_seq (\n. ODD (X DIV 2 EXP n)) 1536) (&((2 * i) * 3 + k))) =
       Value (ODD (X DIV 2 EXP ((2 * i) * 3 + k)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`list_of_seq (\n. ODD (X DIV 2 EXP n)) 1536`; `(2 * i) * 3 + k`]
    NATIVE_LIST_INDEX) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  SUBGOAL_THEN `(2 * i) * 3 + k < 1536` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

let RQ_BIT_IDX_3B = prove
 (`!X i k. i < 256 /\ k < 3
   ==> typed_hol_read (native_list_index
         (list_of_seq (\n. ODD (X DIV 2 EXP n)) 1536) (&(((2 * i) * 3 + 3) + k))) =
       Value (ODD (X DIV 2 EXP (((2 * i) * 3 + 3) + k)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`list_of_seq (\n. ODD (X DIV 2 EXP n)) 1536`; `((2 * i) * 3 + 3) + k`]
    NATIVE_LIST_INDEX) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  SUBGOAL_THEN `((2 * i) * 3 + 3) + k < 1536` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;


let RQ_FOLDL_PA = prove
 (`(!(body:I->S->(S)native_result). native_foldl body [] = (\s. Value s)) /\
   (!(body:I->S->(S)native_result) i l.
      native_foldl body (CONS i l) = (\s. native_bind (body i s) (native_foldl body l)))`,
  REWRITE_TAC[FUN_EQ_THM; native_foldl_DEF]);;


let RQ_CBD_TAC eta defn btb idxa idxb los nsumlt =
  let etat = mk_small_numeral eta in
  let etam1t = mk_small_numeral (eta - 1) in
  let fuel = mk_small_numeral (eta + 1) in
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[defn; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ASM_SIMP_TAC[btb; NATIVE_BIND_VALUE] THEN
  MP_TAC(SPECL [`257`;`0`;`256`] NATIVE_SCHEDULE_UPTO) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN
  W(fun (asl,w) ->
    let f = vsubst [etat,`eta:num`] `\n. FIPS203_Zq (residue_of_int_mod (coeff n (mlkem_cbd eta b)))` in
    let th2 = SPEC_ALL (ISPEC f RQ_BIND_FOLDL_FILL) in
    let pat = lhand(snd(dest_imp(concl th2))) in
    MP_TAC(INSTANTIATE (term_match [] pat (lhs w)) th2)) THEN
  ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[zqlist]] THEN
  CONJ_TAC THENL [REWRITE_TAC[LENGTH_MAP; LENGTH_REPLICATE]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `t:(fips203_zq)list`] THEN STRIP_TAC THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[INT_ARITH (mk_eq(mk_binop `(+):int->int->int` (mk_comb(`int_of_num`,etam1t)) `&1:int`,
                               mk_comb(`int_of_num`,etat)));
              ISA_NAT_NUM; ARITH_RULE (mk_eq(mk_comb(`SUC`,etat),fuel))] THEN
  MP_TAC(SPECL [fuel; `0`; etat] NATIVE_SCHEDULE_UPTO) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; SUB_0; los; native_foldl_DEF; RQ_FOLDL_PA] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[native_foldl_DEF; RQ_FOLDL_PA; NATIVE_BIND_VALUE; ADD_CLAUSES] THEN
  REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD] THEN
  ASM_SIMP_TAC[idxa; idxb; NATIVE_BIND_VALUE; TYPED_HOL_BIT_VALUE;
               ARITH_RULE `0 < 2`; ARITH_RULE `1 < 2`; ARITH_RULE `0 < 3`;
               ARITH_RULE `1 < 3`; ARITH_RULE `2 < 3`] THEN
  ASM_SIMP_TAC[NATIVE_LIST_UPDATE; ISA_INT_MOD_POS; INT_ARITH `&0:int < &3329`;
               LENGTH_MAP; LENGTH_REPLICATE] THEN
  REWRITE_TAC[RQ_BITVAL_ODD] THEN
  MP_TAC(SPECL [etat; `b:byte list`; `i:num`] RQ_CBD_COEFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[nsumlt] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ARITH_RULE `2 * 2 * i = (2 * i) * 2`;
              ARITH_RULE `2 * 3 * i = (2 * i) * 3`;
              GSYM ADD_ASSOC; INT_OF_NUM_ADD] THEN
  REPEAT AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ADD_CLAUSES] THEN INT_ARITH_TAC;;

let CBD_2 = prove(CBD_2_STMT,
  RQ_CBD_TAC 2 SamplePolyCBD_eta_2_hol_DEF BYTESTOBITS_128
    RQ_BIT_IDX_2A RQ_BIT_IDX_2B RQ_LOS2 RQ_NSUM_LT2);;

let CBD_3 = prove(CBD_3_STMT,
  RQ_CBD_TAC 3 SamplePolyCBD_eta_3_hol_DEF BYTESTOBITS_192
    RQ_BIT_IDX_3A RQ_BIT_IDX_3B RQ_LOS3 RQ_NSUM_LT3);;
