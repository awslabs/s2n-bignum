(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-KEM (FIPS 203 Algorithms 16-21 and the input checks of Section 7):    *)
(* the generated functions agree with the handwritten ones.                  *)
(* ========================================================================= *)

(* The re-encoding computed by the generated encapsulation key check.       *)

let MLKEM_EQ_ENCODE_DECODE_VEC = prove
 (`!k (l:byte list).
     384 * k <= LENGTH l
     ==> mlkem_encode 12 (256 * k)
           (\n. zarr (zqlist (\n'. mlkem_decode 12 (mlkem_slice 0 (384 * k) l)
                                     (256 * n DIV 256 + n')))
                     (n MOD 256)) =
         mlkem_encode 12 (256 * k) (mlkem_decode 12 l)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLKEM_ENCODE_EQ THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SIMP_TAC[ZARR_ZQLIST; MOD_LT_EQ; ARITH_EQ; DIVISION_SIMP] THEN
  SUBGOAL_THEN `mlkem_decode 12 (mlkem_slice 0 (384 * k) l) n =
                mlkem_decode 12 l n` SUBST1_TAC THENL
   [MATCH_MP_TAC MLKEM_DECODE12_SLICE0 THEN ASM_ARITH_TAC;
    MATCH_MP_TAC INT_REM_LT THEN REWRITE_TAC[MLKEM_DECODE_12_BOUNDS]]);;

(* ------------------------------------------------------------------------- *)
(* Generic tactics, instantiated per parameter set.                          *)
(* ------------------------------------------------------------------------- *)

(* Evaluate slices, sequence extents and the constant powers APow 1 n.       *)

let MLKEM_EQ_SLICES_TAC =
  REWRITE_TAC[INT_ARITH_APOW; NATIVE_BIND_VALUE] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
  ASM_SIMP_TAC[LIST_SLICE_BYTES; ARITH; NATIVE_BIND_VALUE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[SEQUENCE_EXTENT; LENGTH_MLKEM_SLICE; NATIVE_BIND_VALUE];;

let MLKEM_EQ_KEYGEN_INTERNAL_TAC def kpke params =
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[def; kpke] THEN
  REWRITE_TAC[params] THEN REWRITE_TAC[mlkem_keygen_internal] THEN
  W(fun (_,w) ->
      let t = find_term
        (fun t -> is_comb t && is_comb (rator t) &&
                  rator(rator t) = `kpke_keygen`) w in
      SPEC_TAC(t,`p:byte list#byte list`)) THEN
  REWRITE_TAC[FORALL_PAIR_THM; NATIVE_BIND_VALUE; H_SEMANTIC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[NATIVE_BIND_VALUE; APPEND_ASSOC];;

let MLKEM_EQ_ENCAPS_INTERNAL_TAC def kpke params =
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[def; NATIVE_BIND_VALUE; H_SEMANTIC; G_SEMANTIC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[kpke; NATIVE_BIND_VALUE] THEN
  REWRITE_TAC[params] THEN REWRITE_TAC[mlkem_encaps_internal] THEN
  SPEC_TAC(`mlkem_g (APPEND m (mlkem_h ek))`,`p:byte list#byte list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[];;

(* slice_eq is `mlkem_slice (384k) 32 (mlkem_slice (384k) (384k+32) dk) =   *)
(* mlkem_slice (768k) 32 dk` with the numerals of the parameter set.         *)

let MLKEM_EQ_DECAPS_INTERNAL_TAC def kdec kenc params slice_eq =
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[def] THEN MLKEM_EQ_SLICES_TAC THEN
  SUBGOAL_THEN slice_eq ASSUME_TAC THENL
   [SIMP_TAC[MLKEM_EQ_SLICE_SLICE; ARITH]; ALL_TAC] THEN
  ASM_SIMP_TAC[kdec; LENGTH_MLKEM_SLICE; NATIVE_BIND_VALUE;
               G_SEMANTIC; J_SEMANTIC] THEN
  ASM_SIMP_TAC[kenc; LENGTH_MLKEM_SLICE; NATIVE_BIND_VALUE;
               MLKEM_KPKE_DECRYPT_LENGTH] THEN
  REWRITE_TAC[params] THEN REWRITE_TAC[mlkem_decaps_internal] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  W(fun (_,w) ->
     let t = find_term (fun t -> is_comb t && rator t = `mlkem_g`) w in
     SPEC_TAC(t, `p:byte list#byte list`)) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[COND_SWAP] THEN MESON_TAC[];;

let MLKEM_EQ_EK_CHECK_TAC def params len k =
  GEN_TAC THEN REWRITE_TAC[def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[params; mlkem_ek_check; INT_OF_NUM_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC (mk_eq(`LENGTH(ek:byte list)`,len)) THEN
  ASM_REWRITE_TAC[TYPED_HOL_INT_TO_BIT_CLAUSES] THEN
  MLKEM_EQ_SLICES_TAC THEN
  SIMP_TAC[ZQBYTEDECODEVECTOR12_2; ZQBYTEDECODEVECTOR12_3;
           ZQBYTEDECODEVECTOR12_4; LENGTH_MLKEM_SLICE; NATIVE_BIND_VALUE] THEN
  SIMP_TAC[ZQBYTEENCODEVECTOR12_2; ZQBYTEENCODEVECTOR12_3;
           ZQBYTEENCODEVECTOR12_4; ZQ_LIST_OK_ZQLIST; NATIVE_BIND_VALUE] THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
          (SPECL [k; `ek:byte list`] MLKEM_EQ_ENCODE_DECODE_VEC)) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[];;

let MLKEM_EQ_DECAPS_CHECK_TAC idef kdef params clen dklen =
  REPEAT GEN_TAC THEN REWRITE_TAC[idef; kdef] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[params; mlkem_decaps_check; INT_OF_NUM_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC (mk_eq(`LENGTH(c:byte list)`,clen)) THEN
  ASM_REWRITE_TAC[TYPED_HOL_INT_TO_BIT_CLAUSES] THEN
  ASM_CASES_TAC (mk_eq(`LENGTH(dk:byte list)`,dklen)) THEN
  ASM_REWRITE_TAC[TYPED_HOL_INT_TO_BIT_CLAUSES] THEN
  MLKEM_EQ_SLICES_TAC THEN REWRITE_TAC[H_SEMANTIC; NATIVE_BIND_VALUE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[TYPED_HOL_INT_TO_BIT_CLAUSES];;

let MLKEM_EQ_KEYGEN_TAC def internal =
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[def; isa_case_option; internal; NATIVE_BIND_VALUE] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[mlkem_keygen_internal];;

let MLKEM_EQ_KEYGEN_BOTTOM_TAC def =
  GEN_TAC THEN REWRITE_TAC[def] THEN
  MP_TAC(ISPEC `(ent:num->(byte list)option) 0` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[isa_case_option] THEN
  REWRITE_TAC[option_DISTINCT] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[isa_case_option];;

let MLKEM_EQ_ENCAPS_TAC def internal params =
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_encaps_checked] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[params; mlkem_ek_check]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_SIMP_TAC[def; isa_case_option; internal; NATIVE_BIND_VALUE] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[];;

let MLKEM_EQ_ENCAPS_BOTTOM_TAC def =
  SIMP_TAC[def; isa_case_option];;

let MLKEM_EQ_DECAPS_TAC def internal params =
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_decaps_checked] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  POP_ASSUM(MP_TAC o REWRITE_RULE[params; mlkem_decaps_check]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ASM_SIMP_TAC[def; internal];;

(* ------------------------------------------------------------------------- *)
(* ML-KEM-512.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_KEYGEN_INTERNAL_512_EQUIV = prove
 (MLKEM_KEYGEN_INTERNAL_512_EQUIV_STMT,
  MLKEM_EQ_KEYGEN_INTERNAL_TAC
   ML_KEM_KeyGen_internal_MLKEM512_Configuration_hol_DEF
   KPKE_KEYGEN_512_EQUIV mlkem512);;

let MLKEM_ENCAPS_INTERNAL_512_EQUIV = prove
 (MLKEM_ENCAPS_INTERNAL_512_EQUIV_STMT,
  MLKEM_EQ_ENCAPS_INTERNAL_TAC
   ML_KEM_Encaps_internal_MLKEM512_Configuration_hol_DEF
   KPKE_ENCRYPT_512_EQUIV mlkem512);;

let MLKEM_DECAPS_INTERNAL_512_EQUIV = prove
 (MLKEM_DECAPS_INTERNAL_512_EQUIV_STMT,
  MLKEM_EQ_DECAPS_INTERNAL_TAC
   ML_KEM_Decaps_internal_MLKEM512_Configuration_hol_DEF
   KPKE_DECRYPT_512_EQUIV KPKE_ENCRYPT_512_EQUIV mlkem512
   `mlkem_slice 768 32 (mlkem_slice 768 800 dk) = mlkem_slice 1536 32 dk`);;

let MLKEM_EK_CHECK_512_EQUIV = prove
 (MLKEM_EK_CHECK_512_EQUIV_STMT,
  MLKEM_EQ_EK_CHECK_TAC
   ML_KEM_EncapsKeyCheck_MLKEM512_Configuration_hol_DEF mlkem512
   `800` `2`);;

let MLKEM_DECAPS_CHECK_512_EQUIV = prove
 (MLKEM_DECAPS_CHECK_512_EQUIV_STMT,
  MLKEM_EQ_DECAPS_CHECK_TAC
   ML_KEM_DecapsInputCheck_MLKEM512_Configuration_hol_DEF
   ML_KEM_DecapsKeyCheck_MLKEM512_Configuration_hol_DEF mlkem512
   `768` `1632`);;

let MLKEM_KEYGEN_512_EQUIV = prove
 (MLKEM_KEYGEN_512_EQUIV_STMT,
  MLKEM_EQ_KEYGEN_TAC ML_KEM_KeyGen_MLKEM512_Configuration_hol_DEF
   MLKEM_KEYGEN_INTERNAL_512_EQUIV);;

let MLKEM_KEYGEN_512_BOTTOM = prove
 (MLKEM_KEYGEN_512_BOTTOM_STMT,
  MLKEM_EQ_KEYGEN_BOTTOM_TAC ML_KEM_KeyGen_MLKEM512_Configuration_hol_DEF);;

let MLKEM_ENCAPS_512_EQUIV = prove
 (MLKEM_ENCAPS_512_EQUIV_STMT,
  MLKEM_EQ_ENCAPS_TAC ML_KEM_Encaps_MLKEM512_Configuration_hol_DEF
   MLKEM_ENCAPS_INTERNAL_512_EQUIV mlkem512);;

let MLKEM_ENCAPS_512_BOTTOM = prove
 (MLKEM_ENCAPS_512_BOTTOM_STMT,
  MLKEM_EQ_ENCAPS_BOTTOM_TAC ML_KEM_Encaps_MLKEM512_Configuration_hol_DEF);;

let MLKEM_DECAPS_512_EQUIV = prove
 (MLKEM_DECAPS_512_EQUIV_STMT,
  MLKEM_EQ_DECAPS_TAC ML_KEM_Decaps_MLKEM512_Configuration_hol_DEF
   MLKEM_DECAPS_INTERNAL_512_EQUIV mlkem512);;

(* ------------------------------------------------------------------------- *)
(* ML-KEM-768.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_KEYGEN_INTERNAL_768_EQUIV = prove
 (MLKEM_KEYGEN_INTERNAL_768_EQUIV_STMT,
  MLKEM_EQ_KEYGEN_INTERNAL_TAC
   ML_KEM_KeyGen_internal_MLKEM768_Configuration_hol_DEF
   KPKE_KEYGEN_768_EQUIV mlkem768);;

let MLKEM_ENCAPS_INTERNAL_768_EQUIV = prove
 (MLKEM_ENCAPS_INTERNAL_768_EQUIV_STMT,
  MLKEM_EQ_ENCAPS_INTERNAL_TAC
   ML_KEM_Encaps_internal_MLKEM768_Configuration_hol_DEF
   KPKE_ENCRYPT_768_EQUIV mlkem768);;

let MLKEM_DECAPS_INTERNAL_768_EQUIV = prove
 (MLKEM_DECAPS_INTERNAL_768_EQUIV_STMT,
  MLKEM_EQ_DECAPS_INTERNAL_TAC
   ML_KEM_Decaps_internal_MLKEM768_Configuration_hol_DEF
   KPKE_DECRYPT_768_EQUIV KPKE_ENCRYPT_768_EQUIV mlkem768
   `mlkem_slice 1152 32 (mlkem_slice 1152 1184 dk) = mlkem_slice 2304 32 dk`);;

let MLKEM_EK_CHECK_768_EQUIV = prove
 (MLKEM_EK_CHECK_768_EQUIV_STMT,
  MLKEM_EQ_EK_CHECK_TAC
   ML_KEM_EncapsKeyCheck_MLKEM768_Configuration_hol_DEF mlkem768
   `1184` `3`);;

let MLKEM_DECAPS_CHECK_768_EQUIV = prove
 (MLKEM_DECAPS_CHECK_768_EQUIV_STMT,
  MLKEM_EQ_DECAPS_CHECK_TAC
   ML_KEM_DecapsInputCheck_MLKEM768_Configuration_hol_DEF
   ML_KEM_DecapsKeyCheck_MLKEM768_Configuration_hol_DEF mlkem768
   `1088` `2400`);;

let MLKEM_KEYGEN_768_EQUIV = prove
 (MLKEM_KEYGEN_768_EQUIV_STMT,
  MLKEM_EQ_KEYGEN_TAC ML_KEM_KeyGen_MLKEM768_Configuration_hol_DEF
   MLKEM_KEYGEN_INTERNAL_768_EQUIV);;

let MLKEM_KEYGEN_768_BOTTOM = prove
 (MLKEM_KEYGEN_768_BOTTOM_STMT,
  MLKEM_EQ_KEYGEN_BOTTOM_TAC ML_KEM_KeyGen_MLKEM768_Configuration_hol_DEF);;

let MLKEM_ENCAPS_768_EQUIV = prove
 (MLKEM_ENCAPS_768_EQUIV_STMT,
  MLKEM_EQ_ENCAPS_TAC ML_KEM_Encaps_MLKEM768_Configuration_hol_DEF
   MLKEM_ENCAPS_INTERNAL_768_EQUIV mlkem768);;

let MLKEM_ENCAPS_768_BOTTOM = prove
 (MLKEM_ENCAPS_768_BOTTOM_STMT,
  MLKEM_EQ_ENCAPS_BOTTOM_TAC ML_KEM_Encaps_MLKEM768_Configuration_hol_DEF);;

let MLKEM_DECAPS_768_EQUIV = prove
 (MLKEM_DECAPS_768_EQUIV_STMT,
  MLKEM_EQ_DECAPS_TAC ML_KEM_Decaps_MLKEM768_Configuration_hol_DEF
   MLKEM_DECAPS_INTERNAL_768_EQUIV mlkem768);;

(* ------------------------------------------------------------------------- *)
(* ML-KEM-1024.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_KEYGEN_INTERNAL_1024_EQUIV = prove
 (MLKEM_KEYGEN_INTERNAL_1024_EQUIV_STMT,
  MLKEM_EQ_KEYGEN_INTERNAL_TAC
   ML_KEM_KeyGen_internal_MLKEM1024_Configuration_hol_DEF
   KPKE_KEYGEN_1024_EQUIV mlkem1024);;

let MLKEM_ENCAPS_INTERNAL_1024_EQUIV = prove
 (MLKEM_ENCAPS_INTERNAL_1024_EQUIV_STMT,
  MLKEM_EQ_ENCAPS_INTERNAL_TAC
   ML_KEM_Encaps_internal_MLKEM1024_Configuration_hol_DEF
   KPKE_ENCRYPT_1024_EQUIV mlkem1024);;

let MLKEM_DECAPS_INTERNAL_1024_EQUIV = prove
 (MLKEM_DECAPS_INTERNAL_1024_EQUIV_STMT,
  MLKEM_EQ_DECAPS_INTERNAL_TAC
   ML_KEM_Decaps_internal_MLKEM1024_Configuration_hol_DEF
   KPKE_DECRYPT_1024_EQUIV KPKE_ENCRYPT_1024_EQUIV mlkem1024
   `mlkem_slice 1536 32 (mlkem_slice 1536 1568 dk) = mlkem_slice 3072 32 dk`);;

let MLKEM_EK_CHECK_1024_EQUIV = prove
 (MLKEM_EK_CHECK_1024_EQUIV_STMT,
  MLKEM_EQ_EK_CHECK_TAC
   ML_KEM_EncapsKeyCheck_MLKEM1024_Configuration_hol_DEF mlkem1024
   `1568` `4`);;

let MLKEM_DECAPS_CHECK_1024_EQUIV = prove
 (MLKEM_DECAPS_CHECK_1024_EQUIV_STMT,
  MLKEM_EQ_DECAPS_CHECK_TAC
   ML_KEM_DecapsInputCheck_MLKEM1024_Configuration_hol_DEF
   ML_KEM_DecapsKeyCheck_MLKEM1024_Configuration_hol_DEF mlkem1024
   `1568` `3168`);;

let MLKEM_KEYGEN_1024_EQUIV = prove
 (MLKEM_KEYGEN_1024_EQUIV_STMT,
  MLKEM_EQ_KEYGEN_TAC ML_KEM_KeyGen_MLKEM1024_Configuration_hol_DEF
   MLKEM_KEYGEN_INTERNAL_1024_EQUIV);;

let MLKEM_KEYGEN_1024_BOTTOM = prove
 (MLKEM_KEYGEN_1024_BOTTOM_STMT,
  MLKEM_EQ_KEYGEN_BOTTOM_TAC ML_KEM_KeyGen_MLKEM1024_Configuration_hol_DEF);;

let MLKEM_ENCAPS_1024_EQUIV = prove
 (MLKEM_ENCAPS_1024_EQUIV_STMT,
  MLKEM_EQ_ENCAPS_TAC ML_KEM_Encaps_MLKEM1024_Configuration_hol_DEF
   MLKEM_ENCAPS_INTERNAL_1024_EQUIV mlkem1024);;

let MLKEM_ENCAPS_1024_BOTTOM = prove
 (MLKEM_ENCAPS_1024_BOTTOM_STMT,
  MLKEM_EQ_ENCAPS_BOTTOM_TAC ML_KEM_Encaps_MLKEM1024_Configuration_hol_DEF);;

let MLKEM_DECAPS_1024_EQUIV = prove
 (MLKEM_DECAPS_1024_EQUIV_STMT,
  MLKEM_EQ_DECAPS_TAC ML_KEM_Decaps_MLKEM1024_Configuration_hol_DEF
   MLKEM_DECAPS_INTERNAL_1024_EQUIV mlkem1024);;
