(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Equivalence of the local helper functions that the generated              *)
(* ML_DSA_Sign_internal(_mu)_P and ML_DSA_Verify_internal(_mu)_P define      *)
(* inside their bodies ("callables"), for ML-DSA-44, -65 and -87.            *)
(*                                                                           *)
(* Each callable is a copy of a stand-alone generated function whose         *)
(* argument is wrapped in native_bottom (the FIPS 204 value or bottom). On   *)
(* Native_Value x it is the stand-alone function on x, which is proved by    *)
(* rewriting (CALL_*_EQ); the equations below then come from the lemmas of   *)
(* hints.ml, sample.ml and rounding.ml. Lemma names are                      *)
(*   EQ_SIGN_INTERNAL[_MU]_CALLABLE_<n>_0_<P>,                               *)
(*   EQ_VERIFY_INTERNAL[_MU]_CALLABLE_<n>_0_<P>,   P = MLDSA44|65|87.        *)
(*                                                                           *)
(* Sign (k x l matrix, omega = 80/55/75), n =                                *)
(*   0   sigEncode on Native_Value z, Native_Value h; hypothesis: BitPack    *)
(* of one polynomial of z (hints_bitpack_hyp, discharged in sigcodec.ml); *)
(*   2   hint count (FixedCountOnes_k);                                      *)
(*   4   ExpandA, under xof_ok and LENGTH rho = 32, the matrix of            *)
(*       NTT(ExpandA) as in EQ_EXPANDA_NTT_P of sample.ml;                   *)
(*   5   NTT of a vector of k integer polynomials (s2, t0; also s1 for       *)
(*       ML-DSA-44, where k = l); for 65 and 87 callable 6 does l            *)
(*       polynomials (s1). Hypothesis call_ntt_hyp: IntPolyToRq and NTT on   *)
(*       one polynomial (EQ_INTPOLYTORQ and EQ_NTT of ntt.ml), to be         *)
(* discharged with PROVE_HYP in sign.ml;                                *)
(*   6|7 HintBitPack (6 for ML-DSA-44, 7 for 65 and 87): equal to            *)
(*       HintBitPack_P on Native_Value h (the lemma EQ_..._HINTBITPACK_...   *)
(*       is this equation, not the handwritten form; EQ_SIGN..._0_0 covers   *)
(*       the use).                                                           *)
(* Callables 1 and 3 (centering and norm) are in rounding.ml.                *)
(*                                                                           *)
(* Verify: 0 UseHint over the hint vector (Native_Value h, vector r of Z_q   *)
(* polynomials), 1 scaling of the integer vector by c, 2 ExpandA (as 4 of    *)
(* Sign).                                                                    *)
(*                                                                           *)
(* Load from the repository root after base.ml and common.ml.          *)
(* ========================================================================= *)

needs "common/fips204/generated/core/core.ml";;
needs "common/fips204/generated/core/rounding.ml";;
needs "common/fips204/generated/core/sample.ml";;
needs "common/fips204/generated/core/hints.ml";;

(* ------------------------------------------------------------------------- *)
(* Generic lemmas (CALL_ prefix).                                            *)
(* ------------------------------------------------------------------------- *)

let CALL_INIT_POLYVEC = prove
 (`!n. n = dimindex(:N)
       ==> Common_Vec (MAP (\element. FIPS204_Poly (MAP FIPS204_Zq element))
                        (REPLICATE n (REPLICATE 256 (residue_of_int_mod (&0))))) =
           (lift_vec (\i. lift_poly (\j. &0)):(N,(A)fips204_poly)common_vec)`,
  SIMP_TAC[lift_vec; lift_poly; lift_zq; REPLICATE_LIST_OF_SEQ;
           MAP_LIST_OF_SEQ; o_DEF]);;

let CALL_UPDATE_POLYVEC = prove
 (`!s i b. i < dimindex(:N)
        ==> typed_hol_nominal_update Common_Vec common_vec_entries
             (\l. native_list_update l (&i) (lift_poly b:(A)fips204_poly))
             (lift_vec (\i. lift_poly (s i)):(N,(A)fips204_poly)common_vec) =
            SOME (lift_vec (\m. lift_poly (if m = i then b else s m)))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[typed_hol_nominal_update_DEF; COMMON_VEC_ENTRIES_LIFT;
               ROUND_LIST_UPDATE_LIST_OF_SEQ; isa_map_option] THEN
  REWRITE_TAC[lift_vec] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x:num = i` THEN ASM_REWRITE_TAC[]);;

let CALL_POLYVEC_CONG = prove
 (`!s s':num->num->int.
        (!i. i < dimindex(:N) ==> s i = s' i)
        ==> (lift_vec (\i. lift_poly (s i)):(N,(A)fips204_poly)common_vec) =
            lift_vec (\i. lift_poly (s' i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lift_vec] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN ASM_SIMP_TAC[]);;

(* A counted loop over i < k whose state is rep s for an array s of values,  *)
(* and step i sets s i to f i (the one-index analogue of ROUND_MAPLOOP).     *)

let CALL_MAPLOOP1 = prove
 (`!(rep:(num->A)->S) (body:int->S->(S)native_result) f z k m.
        k < m /\
        (!s s'. (!i. i < k ==> s i = s' i) ==> rep s = rep s') /\
        (!s i. i < k ==> body (&i) (rep s) =
                         Value (rep (\i'. if i' = i then f i else s i')))
        ==> native_foldl body
             (native_schedule m (\i. i < &k) (\i. i + &1) (&0)) (rep z) =
            Value (rep f)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cong") (LABEL_TAC "step"))) THEN
  MP_TAC(ISPECL
   [`body:int->S->(S)native_result`;
    `\i. (rep:(num->A)->S) (\i'. if i' < i then f i' else z i')`;
    `m:num`; `k:num`] ROUND_FOLDL_SCHEDULE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "step" (fun th -> MP_TAC(SPECL
      [`\i'. if i' < i then (f:num->A) i' else z i'`; `i:num`] th)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN
    USE_THEN "cong" MATCH_MP_TAC THEN
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN BETA_TAC THEN
    ASM_CASES_TAC `x:num = i` THEN ASM_REWRITE_TAC[LT; LT_REFL];
    SUBGOAL_THEN `(rep:(num->A)->S) (\i'. if i' < 0 then f i' else z i') =
                  rep z` SUBST1_TAC THENL
     [USE_THEN "cong" MATCH_MP_TAC THEN REWRITE_TAC[LT]; ALL_TAC] THEN
    SUBGOAL_THEN `(rep:(num->A)->S) (\i'. if i' < k then f i' else z i') =
                  rep f` SUBST1_TAC THENL
     [USE_THEN "cong" MATCH_MP_TAC THEN SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN ACCEPT_TAC]);;

(* The NTT-domain maps need IntPolyToRq and NTT of one polynomial.           *)

let call_ntt_hyp =
 `(!a. IntPolyToRq_hol (lift_intpoly a) = Value (lift_poly a)) /\
  (!a. NTT_hol (lift_poly a) = Value (lift_poly (mldsa_ntt (mldsa_poly a))))`;;

let call_rewrite_eq eq th = REWRITE_RULE[GSYM eq] th;;

let call_tm = round_tm;;

let CALL_BOTTOM_THMS = [case_native_bottom_DEF; typed_hol_bottom_index_DEF];;

(* The callable on Native_Value x is the stand-alone function on x.          *)

let call_eq_prove tm def standalone_def =
  prove(tm, REPEAT GEN_TAC THEN
    REWRITE_TAC([def; standalone_def; TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE] @
                CALL_BOTTOM_THMS));;

(* ------------------------------------------------------------------------- *)
(* The callables of Sign.                                                    *)
(* ------------------------------------------------------------------------- *)

let call_sign_thms (fam,p,k,l,omega,g1,c) (n_hp,n_l)
                   (d0,dhp,d2,d4,d5,d5l) (sigdef,hpdef,cntdef,expdef)
                   (e_sig,e_cnt,e_exp) =
  let tm = call_tm ["@F@",fam; "@P@",p; "@K@",string_of_int k;
                    "@L@",string_of_int l; "@HP@",string_of_int n_hp;
                    "@NL@",string_of_int n_l] in
  (* HintBitPack on Native_Value *)
  let hp_eq = call_eq_prove
   (tm "!h. @F@_@P@_Configuration_callable_@HP@_0_call (Native_Value h) =
            HintBitPack_@P@_Configuration_hol h") dhp hpdef in
  (* sigEncode *)
  let sig_eq = prove
   (tm "!c z h. @F@_@P@_Configuration_callable_0_0_call c
                  (Native_Value z) (Native_Value h) =
                sigEncode_@P@_Configuration_hol c z h",
    REPEAT GEN_TAC THEN
    REWRITE_TAC([d0; sigdef; TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE; hp_eq] @
                CALL_BOTTOM_THMS)) in
  let c0 = call_rewrite_eq sig_eq e_sig in
  (* hint count *)
  let cnt_eq = call_eq_prove
   (tm "!h. @F@_@P@_Configuration_callable_2_0_call (Native_Value h) =
            FixedCountOnes_@K@_hol h") d2 cntdef in
  let c2 = call_rewrite_eq cnt_eq e_cnt in
  (* ExpandA *)
  let exp_eq = call_eq_prove
   (tm "!rho. @F@_@P@_Configuration_callable_4_0_call (Native_Value rho) =
              ExpandA_@P@_Configuration_hol rho") d4 expdef in
  let c4 = call_rewrite_eq exp_eq e_exp in
  (* NTT of a vector of n integer polynomials *)
  let ntt_thm n n_c def =
    let tm' = call_tm ["@N@",string_of_int n; "@NC@",string_of_int n_c;
                       "@F@",fam; "@P@",p] in
    prove
     (mk_imp(call_ntt_hyp, tm' "!a. @F@_@P@_Configuration_callable_@NC@_0_call
        (Native_Value (lift_vec (\\i. lift_intpoly (a i)):
                         (@N@,fips204_intpoly)common_vec)) =
        Value (lift_vec (\\i. lift_poly (mldsa_ntt (mldsa_poly (a i)))))"),
      DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rq") (LABEL_TAC "ntt")) THEN
      GEN_TAC THEN REWRITE_TAC[def] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SIMP_TAC(CALL_INIT_POLYVEC :: ROUND_DIMINDEX_THMS) THEN
      MATCH_MP_TAC(BETA_RULE(ISPEC
        `\s:num->num->int. lift_vec (\i. lift_poly (s i))` CALL_MAPLOOP1)) THEN
      REPEAT CONJ_TAC THENL
       [ARITH_TAC;
        REPEAT STRIP_TAC THEN MATCH_MP_TAC CALL_POLYVEC_CONG THEN
        ASM_REWRITE_TAC ROUND_DIMINDEX_THMS;
        REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
        ASM_SIMP_TAC(ROUND_STEP_THMS @
          [case_native_bottom_DEF; typed_hol_bottom_index_DEF;
           CALL_UPDATE_POLYVEC])]) in
  let c5 = ntt_thm k 5 d5 in
  let c5l = ntt_thm l n_l d5l in
  (c0,c2,c4,c5,c5l,hp_eq);;

(* ------------------------------------------------------------------------- *)
(* The callables of Verify.                                                  *)
(* ------------------------------------------------------------------------- *)

let call_verify_thms (fam,p,k) (d0,d1,d2) (usedef,expdef) (e_use,e_exp) =
  let tm = call_tm ["@F@",fam; "@P@",p; "@K@",string_of_int k] in
  (* UseHint over the hint vector *)
  let use_eq = call_eq_prove
   (tm "!h r. @F@_@P@_Configuration_callable_0_0_call (Native_Value h) r =
              FixedVectorUseHint_@K@_@P@_Configuration_hol h r") d0 usedef in
  let c0 = call_rewrite_eq use_eq e_use in
  (* scaling by c *)
  let c1 = prove
   (tm "!t c. @F@_@P@_Configuration_callable_1_0_call
        (Native_Value (lift_vec (\\i. lift_intpoly (t i)):
                         (@K@,fips204_intpoly)common_vec)) c =
      Value (lift_vec (\\i. lift_intpoly (\\j. t i j * c)):
                         (@K@,fips204_intpoly)common_vec)",
    ROUND_UNFOLD_TAC d1 THEN
    ROUND_MAPLOOP_TAC (round_intvec_rep k) ROUND_INTVEC_CONG
      CALL_BOTTOM_THMS) in
  (* ExpandA *)
  let exp_eq = call_eq_prove
   (tm "!rho. @F@_@P@_Configuration_callable_2_0_call (Native_Value rho) =
              ExpandA_@P@_Configuration_hol rho") d2 expdef in
  let c2 = call_rewrite_eq exp_eq e_exp in
  (c0,c1,c2);;

(* ------------------------------------------------------------------------- *)
(* Instances.                                                                *)
(* ------------------------------------------------------------------------- *)

let EQ_SIGN_INTERNAL_CALLABLE_0_0_MLDSA44,
    EQ_SIGN_INTERNAL_CALLABLE_2_0_MLDSA44,
    EQ_SIGN_INTERNAL_CALLABLE_4_0_MLDSA44,
    EQ_SIGN_INTERNAL_CALLABLE_5_0_MLDSA44,
    _,
    EQ_SIGN_INTERNAL_CALLABLE_6_0_MLDSA44 =
  call_sign_thms ("ML_DSA_Sign_internal","MLDSA44",4,4,80,131072,18) (6,5)
   (ML_DSA_Sign_internal_MLDSA44_Configuration_callable_0_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA44_Configuration_callable_6_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA44_Configuration_callable_2_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA44_Configuration_callable_4_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA44_Configuration_callable_5_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA44_Configuration_callable_5_0_call_DEF)
   (sigEncode_MLDSA44_Configuration_hol_DEF,
    HintBitPack_MLDSA44_Configuration_hol_DEF,
    FixedCountOnes_4_hol_DEF,
    ExpandA_MLDSA44_Configuration_hol_DEF)
   (EQ_SIGENCODE_MLDSA44,EQ_FIXEDCOUNTONES_4,EQ_EXPANDA_NTT_MLDSA44);;

let EQ_SIGN_INTERNAL_CALLABLE_0_0_MLDSA65,
    EQ_SIGN_INTERNAL_CALLABLE_2_0_MLDSA65,
    EQ_SIGN_INTERNAL_CALLABLE_4_0_MLDSA65,
    EQ_SIGN_INTERNAL_CALLABLE_5_0_MLDSA65,
    EQ_SIGN_INTERNAL_CALLABLE_6_0_MLDSA65,
    EQ_SIGN_INTERNAL_CALLABLE_7_0_MLDSA65 =
  call_sign_thms ("ML_DSA_Sign_internal","MLDSA65",6,5,55,524288,20) (7,6)
   (ML_DSA_Sign_internal_MLDSA65_Configuration_callable_0_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA65_Configuration_callable_7_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA65_Configuration_callable_2_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA65_Configuration_callable_4_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA65_Configuration_callable_5_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA65_Configuration_callable_6_0_call_DEF)
   (sigEncode_MLDSA65_Configuration_hol_DEF,
    HintBitPack_MLDSA65_Configuration_hol_DEF,
    FixedCountOnes_6_hol_DEF,
    ExpandA_MLDSA65_Configuration_hol_DEF)
   (EQ_SIGENCODE_MLDSA65,EQ_FIXEDCOUNTONES_6,EQ_EXPANDA_NTT_MLDSA65);;

let EQ_SIGN_INTERNAL_CALLABLE_0_0_MLDSA87,
    EQ_SIGN_INTERNAL_CALLABLE_2_0_MLDSA87,
    EQ_SIGN_INTERNAL_CALLABLE_4_0_MLDSA87,
    EQ_SIGN_INTERNAL_CALLABLE_5_0_MLDSA87,
    EQ_SIGN_INTERNAL_CALLABLE_6_0_MLDSA87,
    EQ_SIGN_INTERNAL_CALLABLE_7_0_MLDSA87 =
  call_sign_thms ("ML_DSA_Sign_internal","MLDSA87",8,7,75,524288,20) (7,6)
   (ML_DSA_Sign_internal_MLDSA87_Configuration_callable_0_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA87_Configuration_callable_7_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA87_Configuration_callable_2_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA87_Configuration_callable_4_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA87_Configuration_callable_5_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA87_Configuration_callable_6_0_call_DEF)
   (sigEncode_MLDSA87_Configuration_hol_DEF,
    HintBitPack_MLDSA87_Configuration_hol_DEF,
    FixedCountOnes_8_hol_DEF,
    ExpandA_MLDSA87_Configuration_hol_DEF)
   (EQ_SIGENCODE_MLDSA87,EQ_FIXEDCOUNTONES_8,EQ_EXPANDA_NTT_MLDSA87);;

let EQ_SIGN_INTERNAL_MU_CALLABLE_0_0_MLDSA44,
    EQ_SIGN_INTERNAL_MU_CALLABLE_2_0_MLDSA44,
    EQ_SIGN_INTERNAL_MU_CALLABLE_4_0_MLDSA44,
    EQ_SIGN_INTERNAL_MU_CALLABLE_5_0_MLDSA44,
    _,
    EQ_SIGN_INTERNAL_MU_CALLABLE_6_0_MLDSA44 =
  call_sign_thms ("ML_DSA_Sign_internal_mu","MLDSA44",4,4,80,131072,18) (6,5)
   (ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_0_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_6_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_2_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_4_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_5_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_5_0_call_DEF)
   (sigEncode_MLDSA44_Configuration_hol_DEF,
    HintBitPack_MLDSA44_Configuration_hol_DEF,
    FixedCountOnes_4_hol_DEF,
    ExpandA_MLDSA44_Configuration_hol_DEF)
   (EQ_SIGENCODE_MLDSA44,EQ_FIXEDCOUNTONES_4,EQ_EXPANDA_NTT_MLDSA44);;

let EQ_SIGN_INTERNAL_MU_CALLABLE_0_0_MLDSA65,
    EQ_SIGN_INTERNAL_MU_CALLABLE_2_0_MLDSA65,
    EQ_SIGN_INTERNAL_MU_CALLABLE_4_0_MLDSA65,
    EQ_SIGN_INTERNAL_MU_CALLABLE_5_0_MLDSA65,
    EQ_SIGN_INTERNAL_MU_CALLABLE_6_0_MLDSA65,
    EQ_SIGN_INTERNAL_MU_CALLABLE_7_0_MLDSA65 =
  call_sign_thms ("ML_DSA_Sign_internal_mu","MLDSA65",6,5,55,524288,20) (7,6)
   (ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_0_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_7_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_2_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_4_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_5_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_6_0_call_DEF)
   (sigEncode_MLDSA65_Configuration_hol_DEF,
    HintBitPack_MLDSA65_Configuration_hol_DEF,
    FixedCountOnes_6_hol_DEF,
    ExpandA_MLDSA65_Configuration_hol_DEF)
   (EQ_SIGENCODE_MLDSA65,EQ_FIXEDCOUNTONES_6,EQ_EXPANDA_NTT_MLDSA65);;

let EQ_SIGN_INTERNAL_MU_CALLABLE_0_0_MLDSA87,
    EQ_SIGN_INTERNAL_MU_CALLABLE_2_0_MLDSA87,
    EQ_SIGN_INTERNAL_MU_CALLABLE_4_0_MLDSA87,
    EQ_SIGN_INTERNAL_MU_CALLABLE_5_0_MLDSA87,
    EQ_SIGN_INTERNAL_MU_CALLABLE_6_0_MLDSA87,
    EQ_SIGN_INTERNAL_MU_CALLABLE_7_0_MLDSA87 =
  call_sign_thms ("ML_DSA_Sign_internal_mu","MLDSA87",8,7,75,524288,20) (7,6)
   (ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_0_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_7_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_2_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_4_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_5_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_6_0_call_DEF)
   (sigEncode_MLDSA87_Configuration_hol_DEF,
    HintBitPack_MLDSA87_Configuration_hol_DEF,
    FixedCountOnes_8_hol_DEF,
    ExpandA_MLDSA87_Configuration_hol_DEF)
   (EQ_SIGENCODE_MLDSA87,EQ_FIXEDCOUNTONES_8,EQ_EXPANDA_NTT_MLDSA87);;
let EQ_VERIFY_INTERNAL_CALLABLE_0_0_MLDSA44,
    EQ_VERIFY_INTERNAL_CALLABLE_1_0_MLDSA44,
    EQ_VERIFY_INTERNAL_CALLABLE_2_0_MLDSA44 =
  call_verify_thms ("ML_DSA_Verify_internal","MLDSA44",4) (ML_DSA_Verify_internal_MLDSA44_Configuration_callable_0_0_call_DEF,
    ML_DSA_Verify_internal_MLDSA44_Configuration_callable_1_0_call_DEF,
    ML_DSA_Verify_internal_MLDSA44_Configuration_callable_2_0_call_DEF)
   (FixedVectorUseHint_4_MLDSA44_Configuration_hol_DEF,
    ExpandA_MLDSA44_Configuration_hol_DEF)
   (EQ_FIXEDVECTORUSEHINT_4_MLDSA44,EQ_EXPANDA_NTT_MLDSA44);;

let EQ_VERIFY_INTERNAL_CALLABLE_0_0_MLDSA65,
    EQ_VERIFY_INTERNAL_CALLABLE_1_0_MLDSA65,
    EQ_VERIFY_INTERNAL_CALLABLE_2_0_MLDSA65 =
  call_verify_thms ("ML_DSA_Verify_internal","MLDSA65",6) (ML_DSA_Verify_internal_MLDSA65_Configuration_callable_0_0_call_DEF,
    ML_DSA_Verify_internal_MLDSA65_Configuration_callable_1_0_call_DEF,
    ML_DSA_Verify_internal_MLDSA65_Configuration_callable_2_0_call_DEF)
   (FixedVectorUseHint_6_MLDSA65_Configuration_hol_DEF,
    ExpandA_MLDSA65_Configuration_hol_DEF)
   (EQ_FIXEDVECTORUSEHINT_6_MLDSA65,EQ_EXPANDA_NTT_MLDSA65);;

let EQ_VERIFY_INTERNAL_CALLABLE_0_0_MLDSA87,
    EQ_VERIFY_INTERNAL_CALLABLE_1_0_MLDSA87,
    EQ_VERIFY_INTERNAL_CALLABLE_2_0_MLDSA87 =
  call_verify_thms ("ML_DSA_Verify_internal","MLDSA87",8) (ML_DSA_Verify_internal_MLDSA87_Configuration_callable_0_0_call_DEF,
    ML_DSA_Verify_internal_MLDSA87_Configuration_callable_1_0_call_DEF,
    ML_DSA_Verify_internal_MLDSA87_Configuration_callable_2_0_call_DEF)
   (FixedVectorUseHint_8_MLDSA87_Configuration_hol_DEF,
    ExpandA_MLDSA87_Configuration_hol_DEF)
   (EQ_FIXEDVECTORUSEHINT_8_MLDSA87,EQ_EXPANDA_NTT_MLDSA87);;

let EQ_VERIFY_INTERNAL_MU_CALLABLE_0_0_MLDSA44,
    EQ_VERIFY_INTERNAL_MU_CALLABLE_1_0_MLDSA44,
    EQ_VERIFY_INTERNAL_MU_CALLABLE_2_0_MLDSA44 =
  call_verify_thms ("ML_DSA_Verify_internal_mu","MLDSA44",4) (ML_DSA_Verify_internal_mu_MLDSA44_Configuration_callable_0_0_call_DEF,
    ML_DSA_Verify_internal_mu_MLDSA44_Configuration_callable_1_0_call_DEF,
    ML_DSA_Verify_internal_mu_MLDSA44_Configuration_callable_2_0_call_DEF)
   (FixedVectorUseHint_4_MLDSA44_Configuration_hol_DEF,
    ExpandA_MLDSA44_Configuration_hol_DEF)
   (EQ_FIXEDVECTORUSEHINT_4_MLDSA44,EQ_EXPANDA_NTT_MLDSA44);;

let EQ_VERIFY_INTERNAL_MU_CALLABLE_0_0_MLDSA65,
    EQ_VERIFY_INTERNAL_MU_CALLABLE_1_0_MLDSA65,
    EQ_VERIFY_INTERNAL_MU_CALLABLE_2_0_MLDSA65 =
  call_verify_thms ("ML_DSA_Verify_internal_mu","MLDSA65",6) (ML_DSA_Verify_internal_mu_MLDSA65_Configuration_callable_0_0_call_DEF,
    ML_DSA_Verify_internal_mu_MLDSA65_Configuration_callable_1_0_call_DEF,
    ML_DSA_Verify_internal_mu_MLDSA65_Configuration_callable_2_0_call_DEF)
   (FixedVectorUseHint_6_MLDSA65_Configuration_hol_DEF,
    ExpandA_MLDSA65_Configuration_hol_DEF)
   (EQ_FIXEDVECTORUSEHINT_6_MLDSA65,EQ_EXPANDA_NTT_MLDSA65);;

let EQ_VERIFY_INTERNAL_MU_CALLABLE_0_0_MLDSA87,
    EQ_VERIFY_INTERNAL_MU_CALLABLE_1_0_MLDSA87,
    EQ_VERIFY_INTERNAL_MU_CALLABLE_2_0_MLDSA87 =
  call_verify_thms ("ML_DSA_Verify_internal_mu","MLDSA87",8) (ML_DSA_Verify_internal_mu_MLDSA87_Configuration_callable_0_0_call_DEF,
    ML_DSA_Verify_internal_mu_MLDSA87_Configuration_callable_1_0_call_DEF,
    ML_DSA_Verify_internal_mu_MLDSA87_Configuration_callable_2_0_call_DEF)
   (FixedVectorUseHint_8_MLDSA87_Configuration_hol_DEF,
    ExpandA_MLDSA87_Configuration_hol_DEF)
   (EQ_FIXEDVECTORUSEHINT_8_MLDSA87,EQ_EXPANDA_NTT_MLDSA87);;
