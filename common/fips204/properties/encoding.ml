(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Part 3: the bit packings (mldsa_encode, mldsa_field), sub-lists of byte   *)
(* strings, and the bit lengths used by the three parameter sets.            *)
(* ========================================================================= *)

needs "common/fips204/properties/ntt.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Byte strings: the first four theorems are about num_of_bytelist and       *)
(* bytelist_of_num only. They are also in common/words2.ml, with the same    *)
(* statements, so both files can be loaded into one session. Then the bit    *)
(* packings (mldsa_encode, and mldsa_field reads its fields back),           *)
(* sub-lists, and the bit lengths used by the three parameter sets.          *)
(* ------------------------------------------------------------------------- *)

let LENGTH_BYTELIST_OF_NUM = prove
 (`!k n. LENGTH(bytelist_of_num k n) = k`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[bytelist_of_num; LENGTH]);;

let NUM_OF_BYTELIST_OF_NUM = prove
 (`!k n. num_of_bytelist(bytelist_of_num k n) = n MOD 256 EXP k`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[bytelist_of_num; num_of_bytelist] THEN
  REWRITE_TAC[EXP; MOD_1] THEN GEN_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN
  MP_TAC(SPECL [`n:num`; `256`] DIVISION) THEN ARITH_TAC);;

let NUM_OF_BYTELIST_BOUND = prove
 (`!l. num_of_bytelist l < 256 EXP (LENGTH l)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; num_of_bytelist; ARITH; EXP] THEN
  MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ASM_ARITH_TAC);;

let BYTELIST_OF_NUM_OF_BYTELIST = prove
 (`!l. bytelist_of_num (LENGTH l) (num_of_bytelist l) = l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_bytelist; bytelist_of_num; LENGTH] THEN FIRST_X_ASSUM
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  SIMP_TAC[CONS_11; MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ; WORD_VAL_GALOIS] THEN
  REWRITE_TAC[DIMINDEX_8; MOD_EQ_SELF; ARITH; MOD_MOD_REFL] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  SIMP_TAC[DIV_LT; ADD_CLAUSES] THEN MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let MLDSA_ENCODE_LENGTH = prove
 (`!c n f. LENGTH(mldsa_encode c n f) = (c * n) DIV 8`,
  REWRITE_TAC[mldsa_encode; LENGTH_BYTELIST_OF_NUM]);;

let MLDSA_ENCODE_DIGIT = prove
 (`!c (f:num->int) i. num_of_int(f i rem &2 pow c) < 2 EXP c /\
                      &(num_of_int(f i rem &2 pow c)) = f i rem &2 pow c`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&0 <= (f:num->int) i rem &2 pow c` ASSUME_TAC THENL
   [REWRITE_TAC[INT_REM_POS_EQ; INT_POW_EQ_0] THEN CONV_TAC INT_REDUCE_CONV;
    ASM_SIMP_TAC[INT_OF_NUM_OF_INT]] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_POW; INT_LT_REM_EQ; INT_LT_POW2]);;

let NUM_OF_BYTELIST_MLDSA_ENCODE = prove
 (`!c n f. 8 divides (c * n)
           ==> num_of_bytelist(mldsa_encode c n f) =
               nsum {i | i < n}
                    (\i. num_of_int(f i rem &2 pow c) * 2 EXP (c * i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_encode; NUM_OF_BYTELIST_OF_NUM] THEN
  MATCH_MP_TAC MOD_LT THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` MP_TAC o REWRITE_RULE[divides]) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(8 * m) DIV 8 = m`] THEN
  SUBGOAL_THEN `256 EXP m = (2 EXP c) EXP n` SUBST1_TAC THENL
   [REWRITE_TAC[EXP_EXP; ARITH_RULE `256 = 2 EXP 8`] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
   `b * 2 EXP (c * i) = (2 EXP c) EXP i * b`] THEN
  MATCH_MP_TAC DIGITSUM_BOUND THEN REWRITE_TAC[MLDSA_ENCODE_DIGIT]);;

let MLDSA_ENCODE_EQ = prove
 (`!c n f g. (!i. i < n ==> f i = g i)
             ==> mldsa_encode c n f = mldsa_encode c n g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_encode] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]);;

let MLDSA_ENCODE_EQ_REM = prove
 (`!c n f g. (!i. i < n ==> f i rem &2 pow c = g i rem &2 pow c)
             ==> mldsa_encode c n f = mldsa_encode c n g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_encode] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]);;

let MLDSA_FIELD_BOUND = prove
 (`!c b i. &0 <= mldsa_field c b i /\ mldsa_field c b i < &2 pow c`,
  REWRITE_TAC[mldsa_field; INT_POS; INT_OF_NUM_POW; INT_OF_NUM_LT] THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

let MLDSA_FIELD_ENCODE = prove
 (`!c n f i.
        8 divides (c * n) /\ i < n
        ==> mldsa_field c (mldsa_encode c n f) i = f i rem &2 pow c`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[mldsa_field; NUM_OF_BYTELIST_MLDSA_ENCODE] THEN
  REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
   `b * 2 EXP (d * i) = (2 EXP d) EXP i * b`] THEN
  REWRITE_TAC[GSYM EXP_EXP] THEN
  MP_TAC(ISPECL [`2 EXP c`; `\i. num_of_int ((f:num->int) i rem &2 pow c)`;
                 `{i:num | i < n}`; `i:num`] DIGITSUM_DIV_MOD) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; MLDSA_ENCODE_DIGIT] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MLDSA_ENCODE_DIGIT]);;

let MLDSA_FIELD_ENCODE_SMALL = prove
 (`!c n f i.
        8 divides (c * n) /\ i < n /\ &0 <= f i /\ f i < &2 pow c
        ==> mldsa_field c (mldsa_encode c n f) i = f i`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLDSA_FIELD_ENCODE] THEN
  MATCH_MP_TAC INT_REM_LT THEN ASM_REWRITE_TAC[]);;

let MLDSA_ENCODE_FIELD = prove
 (`!c n b. 8 divides (c * n) /\ LENGTH b = (c * n) DIV 8
           ==> mldsa_encode c n (mldsa_field c b) = b`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM BYTELIST_OF_NUM_OF_BYTELIST] THEN
  ASM_REWRITE_TAC[mldsa_encode] THEN AP_TERM_TAC THEN
  REWRITE_TAC[mldsa_field; INT_OF_NUM_POW; INT_OF_NUM_REM;
              NUM_OF_INT_OF_NUM; MOD_MOD_REFL] THEN
  REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
   `b * 2 EXP (d * i) = (2 EXP d) EXP i * b`] THEN
  REWRITE_TAC[GSYM EXP_EXP; DIGITSUM_WORKS_GEN] THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[EXP_EXP] THEN
  MP_TAC(ISPEC `b:byte list` NUM_OF_BYTELIST_BOUND) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
    REWRITE_RULE[divides]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(8 * m) DIV 8 = m`] THEN
  REWRITE_TAC[EXP_EXP; ARITH_RULE `256 = 2 EXP 8`]);;

let LENGTH_MLDSA_SLICE = prove
 (`!a n l. LENGTH(mldsa_slice a n l) = n`,
  REWRITE_TAC[mldsa_slice; LENGTH_LIST_OF_SEQ]);;

let EL_MLDSA_SLICE = prove
 (`!a n l i. i < n ==> EL i (mldsa_slice a n l) = EL (a + i) l`,
  SIMP_TAC[mldsa_slice; EL_LIST_OF_SEQ]);;

let MLDSA_SLICE_LENGTH = prove
 (`!l. mldsa_slice 0 (LENGTH l) l = l`,
  GEN_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_MLDSA_SLICE] THEN
  SIMP_TAC[EL_MLDSA_SLICE; ADD_CLAUSES]);;

let MLDSA_SLICE_SLICE = prove
 (`!a n b m l. a + n <= m
               ==> mldsa_slice a n (mldsa_slice b m l) =
                   mldsa_slice (b + a) n l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_MLDSA_SLICE] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_MLDSA_SLICE] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_MLDSA_SLICE o lhand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ADD_ASSOC]);;

let MLDSA_SLICE_APPEND = prove
 (`!a n l m.
        (a + n <= LENGTH l
         ==> mldsa_slice a n (APPEND l m) = mldsa_slice a n l) /\
        (LENGTH l <= a
         ==> mldsa_slice a n (APPEND l m) = mldsa_slice (a - LENGTH l) n m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_MLDSA_SLICE] THEN
  SIMP_TAC[EL_MLDSA_SLICE; EL_APPEND] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN
  ASM_ARITH_TAC);;

let MLDSA_BITLEN_UNIQUE = prove
 (`!n c. n < 2 EXP c /\ 2 EXP c <= 2 * n ==> mldsa_bitlen n = c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_bitlen] THEN
  MATCH_MP_TAC MINIMAL_UNIQUE THEN ASM_REWRITE_TAC[NOT_LT] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 EXP c = 2 * 2 EXP (c - 1) /\ 2 EXP m <= 2 EXP (c - 1)`
  MP_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 EXP); LE_EXP] THEN
    CONJ_TAC THENL [AP_TERM_TAC; ALL_TAC] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let MLDSA_BITLEN_0 = prove
 (`mldsa_bitlen 0 = 0`,
  REWRITE_TAC[mldsa_bitlen] THEN MATCH_MP_TAC MINIMAL_UNIQUE THEN
  REWRITE_TAC[EXP; LT] THEN ARITH_TAC);;

(* Evaluation of mldsa_bitlen n for a numeral n.                             *)

let MLDSA_BITLEN_CONV =
  let pth = MLDSA_BITLEN_UNIQUE in
  let rec bits n = if n =/ num 0 then 0 else 1 + bits (quo_num n (num 2)) in
  fun tm ->
    match tm with
      Comb(Const("mldsa_bitlen",_),ntm) when is_numeral ntm ->
        let n = dest_numeral ntm in
        if n =/ num 0 then MLDSA_BITLEN_0 else
        let th = SPECL [ntm; mk_small_numeral(bits n)] pth in
        MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))
    | _ -> failwith "MLDSA_BITLEN_CONV";;

let MLDSA_BITLEN_CLAUSES = prove
 (`mldsa_bitlen 4 = 3 /\ mldsa_bitlen 8 = 4 /\ mldsa_bitlen 15 = 4 /\
   mldsa_bitlen 43 = 6 /\ mldsa_bitlen 131071 = 17 /\
   mldsa_bitlen 524287 = 19`,
  CONV_TAC(DEPTH_CONV MLDSA_BITLEN_CONV) THEN REWRITE_TAC[]);;

type_invention_error := false;;
