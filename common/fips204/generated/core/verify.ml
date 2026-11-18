(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification: the generated ML_DSA_Verify_internal_mu_P_Configuration_hol *)
(* equals lift_verify_bool (mldsa_verify_mu ...) of                          *)
(* common/fips204/fips204.ml, for ML-DSA-44, -65 and -87                     *)
(* (STMT_VERIFY_INTERNAL_MU of toplevel.ml), and from it                     *)
(* ML_DSA_Verify_internal_P_Configuration_hol (STMT_VERIFY_INTERNAL).        *)
(*                                                                           *)
(* Method. TOP_VERIFY_MU_ABSTRACT_P (toplevel.ml) gives the result of the    *)
(* generated function from one Value equation per component call. Each       *)
(* equation is instantiated by the equivalence lemma of the component        *)
(* (wv_chain, which instantiates the equations in the order of the generated *)
(* code, so that each argument is the lifted result of the previous call).   *)
(* The resulting boolean (norm bound /\ recomputed c-tilde equals c-tilde)   *)
(* is then shown equal to mldsa_verify_mu_accepts (which mldsa_verify_mu     *)
(* turns into a result) through the NTT-domain form                          *)
(* MLDSA_VERIFY_MU_FIPS of common/fips204/properties/fips204_properties.ml.  *)
(* sigDecode returns Native_Bottom exactly when mldsa_hintbitunpack fails;   *)
(* the generated code then returns false before using the other components,  *)
(* so that case is proved from the definition (wv_none).                     *)
(*                                                                           *)
(* Load from the repository root after base.ml and common.ml.          *)
(* ========================================================================= *)

needs "common/fips204/generated/core/toplevel.ml";;
needs "common/fips204/generated/core/rounding.ml";;
needs "common/fips204/generated/core/sample.ml";;
needs "common/fips204/generated/core/ball.ml";;
needs "common/fips204/generated/core/hints.ml";;
needs "common/fips204/generated/core/callables.ml";;
needs "common/fips204/generated/core/sigcodec.ml";;
needs "common/fips204/generated/core/encode.ml";;
needs "common/fips204/generated/core/ntt.ml";;
needs "common/fips204/generated/core/ntt_vec.ml";;

(* ------------------------------------------------------------------------- *)
(* Small lemmas.                                                             *)
(* ------------------------------------------------------------------------- *)


let WV_USEHINT_RANGE = prove
 (`!g2 h r. ~(g2 = 0) /\ (2 * g2) divides 8380416
            ==> &0 <= mldsa_usehint g2 h r /\
                mldsa_usehint g2 h r < &(8380416 DIV (2 * g2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g2:num`; `r:int`] MLDSA_DECOMPOSE_VALID) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
                       ASSUME_TAC(CONJUNCT1(CONJUNCT2 th))) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  SUBGOAL_THEN `8380416 DIV (2 * g2) = M` (LABEL_TAC "hd") THENL
   [FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC DIV_MULT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "hd" (fun hd -> REWRITE_TAC[hd]) THEN
  SUBGOAL_THEN `&0 < (&M:int)` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(M = 0)` MP_TAC THENL [DISCH_TAC THEN UNDISCH_TAC `8380416 = (2 * g2) * M` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN REWRITE_TAC[INT_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mldsa_highbits g2 r < &M` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&(2 * g2) * &M:int <= &(2 * g2) * mldsa_highbits g2 r`
     MP_TAC THENL
     [MATCH_MP_TAC INT_LE_LMUL THEN ASM_REWRITE_TAC[INT_OF_NUM_LE; LE_0];
      REWRITE_TAC[INT_OF_NUM_MUL] THEN
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `8380416` then
        REWRITE_TAC[GSYM th] else NO_TAC) THEN ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[mldsa_usehint] THEN USE_THEN "hd" (fun hd -> REWRITE_TAC[hd]) THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
  TRY(ASM_INT_ARITH_TAC));;

let WV_NORM = prove
 (`!k a b. (!i j. i < k /\ j < 256 ==> abs(a i j) < &1000000)
           ==> (round_infnorm k a < &b <=>
                ~(b = 0) /\ mldsa_vec_norm_lt k b (\i. mldsa_poly (a i)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM(SPECL [`k:num`; `b:num`; `\i. mldsa_poly ((a:num->num->int) i)`]
                     ROUND_INFNORM_VEC_NORM_LT)] THEN
  SUBGOAL_THEN
   `round_infnorm k (\i j. mldsa_modpm (coeff j (mldsa_poly ((a:num->num->int) i))) 8380417) =
    round_infnorm k a`
   (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC ROUND_INFNORM_CONG THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[COEFF_MLDSA_POLY; MLDSA_MODPM_REM] THEN
  MATCH_MP_TAC MLDSA_MODPM_SMALL THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
  INT_ARITH_TAC);;

let WV_CONG_SUB = prove
 (`!x y n. (x rem n - y rem n == x - y) (mod n)`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`x:int`; `n:int`] INT_REM_MOD_SELF) THEN
  MP_TAC(SPECL [`y:int`; `n:int`] INT_REM_MOD_SELF) THEN
  CONV_TAC INTEGER_RULE);;

(* The ring operations of Z_q in the NTT-domain form of FIPS 204 Algorithm   *)
(* 8.                                                                        *)
let WV_RING = prove
 (`!l (a:num->int) z c t.
     ring_sub mldsa_zq
       (ring_sum mldsa_zq {j | j < l}
          (\j. ring_mul mldsa_zq (a j) (z j)))
       (ring_mul mldsa_zq c t) =
     (ntt_msum l (\j. a j * z j) - c * t) rem &8380417`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MLDSA_ZQ; NTT_MSUM_ISUM] THEN
  MP_TAC(ISPECL [`{j | j < l}`; `\j. (a:num->int) j * z j`] MLDSA_ZQ_RING_SUM) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INT_REM_EQ] THEN
  REWRITE_TAC[INT_CONG_LREM; INT_CONG_RREM] THEN
  REWRITE_TAC[WV_CONG_SUB]);;

let WV_REJ = prove
 (`!(pk:byte list) k l.
     LENGTH pk = 32 + 320 * k
     ==> (!i j n. i < k /\ j < l /\ n < 256
                  ==> mldsa_rej_ntt_poly
                       (APPEND (mldsa_slice 0 32 pk) [word j; word i]) n
                      < &8380417)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`APPEND (mldsa_slice 0 32 (pk:byte list)) [word j:byte; word i]`; `n:num`]
         MLDSA_REJ_NTT_POLY_RANGE) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_MLDSA_SLICE; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let WV_ENC = prove
 (`!c N (ct:byte list) mu (f:num->int) g lam4.
     (!n. f n = g n)
     ==> ((ct = mldsa_h (APPEND mu (mldsa_encode c N f)) lam4) <=>
          (mldsa_h (APPEND mu (mldsa_encode c N g)) lam4 = ct))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `f:num->int = g` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM]; MATCH_ACCEPT_TAC EQ_SYM_EQ]);;

let WV_DIVMOD = prove
 (`!n. 256 * (n DIV 256) + n MOD 256 = n`, ARITH_TAC);;

let WV_MUL8192 = prove
 (`!f:num->int. (\j. f j * &8192) = (\j. &8192 * f j)`,
  REWRITE_TAC[FUN_EQ_THM; INT_MUL_SYM]);;


(* ------------------------------------------------------------------------- *)
(* Instantiating the abstract lemma one equation at a time. wv_chain takes   *)
(* a table from the head constant of the call to a function producing the    *)
(* equation |- call = Value result for the (already instantiated) call, and  *)
(* walks along the conjuncts of the hypothesis of the abstract lemma,        *)
(* instantiating the result variable of each by the result of the lemma.     *)
(* wv_asl (assumptions) and wv_tac (tactic for side conditions) are set by   *)
(* the caller.                                                               *)
(* ------------------------------------------------------------------------- *)

let wv_conjs_of th = conjuncts (lhand (concl th));;

let wv_inst lem tm =
  let th = SPEC_ALL lem in
  let rec strip c = if is_imp c then strip(snd(dest_imp c)) else c in
  let eq = strip(concl th) in
  let (_,tmi,tyi) = term_match [] (lhand eq) tm in
  INST tmi (INST_TYPE tyi th);;

let wv_discharge asl tac th =
  let rec go th =
    if is_imp(concl th) then
      let (a,_) = dest_imp(concl th) in
      let ath = TAC_PROOF((map (fun t -> "",t) asl, a), tac) in
      go (MP th ath)
    else th in
  go th;;

let wv_asl : thm list ref = ref [];;
let wv_tac : tactic ref = ref ALL_TAC;;
let wv_lem lem l =
  CONV_RULE(DEPTH_CONV BETA_CONV) (wv_discharge !wv_asl !wv_tac (wv_inst lem l));;

let wv_head tm = try fst(dest_const(fst(strip_comb tm))) with Failure _ -> "";;

let wv_is_value_eq c =
  is_eq c && (try fst(dest_const(rator(rand c))) = "Value" with Failure _ -> false);;

(* table: head constant -> (term -> thm giving |- l = Value r)               *)
let wv_chain table abs =
  let n = length (wv_conjs_of abs) in
  let rec go th proved i =
    if i = n then MP th (end_itlist CONJ (rev proved)) else
    let c = el i (wv_conjs_of th) in
    if wv_is_value_eq c then begin
      let l = lhs c in
      let h = wv_head l in
      let f = try assoc h table with Failure _ -> failwith ("wv_chain: no lemma for " ^ h) in
      let eqth = try f l with Failure m -> (print_string ("FAIL at " ^ string_of_int i ^ " " ^ h ^ "\n" ^ string_of_term l ^ "\n"); failwith m) in
      let (_,tmi,tyi) = term_match [] (rhs c) (rhs (concl eqth)) in
      let th' = CONV_RULE(DEPTH_CONV BETA_CONV) (INST tmi (INST_TYPE tyi th)) in
      go th' (eqth :: proved) (i+1)
    end else begin
      let pth = try TAC_PROOF((map (fun t -> "",t) !wv_asl, c), !wv_tac) with Failure m -> (print_string ("FAIL tac at " ^ string_of_int i ^ " " ^ string_of_term c ^ "\n"); failwith m) in
      go th (pth :: proved) (i+1)
    end in
  go abs [] 0;;

(* ------------------------------------------------------------------------- *)
(* The parameter sets. @LAM4@ = lambda/4 (the length of c-tilde), @ZLEN@ the *)
(* length of the encoded z, @HOFF@ and @HLEN@ offset and length of the hint  *)
(* part of the signature, @C@ = 1 + bitlen(gamma1 - 1), @ZB@ = gamma1 -      *)
(* tau * eta, @UHMAX@ = (q - 1)/(2 * gamma2) - 1.                            *)
(* ------------------------------------------------------------------------- *)

let wv_params p =
  match p with
    "44" -> ["@P@","MLDSA44"; "@HW@","mldsa44"; "@K@","4"; "@L@","4";
             "@PK@","1312"; "@SIG@","2420"; "@ETA@","2"; "@TAU@","39";
             "@LAM@","128"; "@LAM4@","32"; "@G1@","131072"; "@G2@","95232";
             "@OM@","80"; "@ZLEN@","2304"; "@HOFF@","2336"; "@HLEN@","84";
             "@C@","18"; "@ZB@","130994"; "@UHMAX@","43"]
  | "65" -> ["@P@","MLDSA65"; "@HW@","mldsa65"; "@K@","6"; "@L@","5";
             "@PK@","1952"; "@SIG@","3309"; "@ETA@","4"; "@TAU@","49";
             "@LAM@","192"; "@LAM4@","48"; "@G1@","524288"; "@G2@","261888";
             "@OM@","55"; "@ZLEN@","3200"; "@HOFF@","3248"; "@HLEN@","61";
             "@C@","20"; "@ZB@","524092"; "@UHMAX@","15"]
  | "87" -> ["@P@","MLDSA87"; "@HW@","mldsa87"; "@K@","8"; "@L@","7";
             "@PK@","2592"; "@SIG@","4627"; "@ETA@","2"; "@TAU@","60";
             "@LAM@","256"; "@LAM4@","64"; "@G1@","524288"; "@G2@","261888";
             "@OM@","75"; "@ZLEN@","4480"; "@HOFF@","4544"; "@HLEN@","83";
             "@C@","20"; "@ZB@","524168"; "@UHMAX@","15"]
  | _ -> failwith "wv_params";;

let wv_tm p s = parse_term (top_subst (wv_params p) s);;

(* The component lemmas of each parameter set: pkDecode, its tuple           *)
(* decomposition, sigDecode, ExpandA (callable 2), the scaling by 2^d        *)
(* (callable 1), UseHint (callable 0), SampleInBall, IntVectorNTT of z and   *)
(* of t1, MatrixVectorNTT, ScalarVectorNTT, FixedVectorSubtract, NTTInv,     *)
(* w1Encode, IntVectorInfNorm.                                               *)

let wv_thms p =
  match p with
    "44" -> (EQ_PKDECODE_MLDSA44, EQ_DECODEDPUBLICKEYSTRINGS_MLDSA44,
             EQ_SIGDECODE_FINAL_MLDSA44,
             EQ_VERIFY_INTERNAL_MU_CALLABLE_2_0_MLDSA44,
             EQ_VERIFY_INTERNAL_MU_CALLABLE_1_0_MLDSA44,
             EQ_VERIFY_INTERNAL_MU_CALLABLE_0_0_MLDSA44,
             EQ_SAMPLEINBALL_MLDSA44, EQ_INTVECTORNTT_4, EQ_INTVECTORNTT_4,
             EQ_MATRIXVECTORNTT_4_4_MLDSA44, EQ_SCALARVECTORNTT_4_MLDSA44,
             EQ_FIXEDVECTORSUBTRACT_4_NTT, EQ_VECTORNTTINV_4_MLDSA44,
             EQ_W1ENCODE_MLDSA44, EQ_INTVECTORINFNORM_4)
  | "65" -> (EQ_PKDECODE_MLDSA65, EQ_DECODEDPUBLICKEYSTRINGS_MLDSA65,
             EQ_SIGDECODE_FINAL_MLDSA65,
             EQ_VERIFY_INTERNAL_MU_CALLABLE_2_0_MLDSA65,
             EQ_VERIFY_INTERNAL_MU_CALLABLE_1_0_MLDSA65,
             EQ_VERIFY_INTERNAL_MU_CALLABLE_0_0_MLDSA65,
             EQ_SAMPLEINBALL_MLDSA65, EQ_INTVECTORNTT_5, EQ_INTVECTORNTT_6,
             EQ_MATRIXVECTORNTT_6_5_MLDSA65, EQ_SCALARVECTORNTT_6_MLDSA65,
             EQ_FIXEDVECTORSUBTRACT_6_NTT, EQ_VECTORNTTINV_6_MLDSA65,
             EQ_W1ENCODE_MLDSA65, EQ_INTVECTORINFNORM_5)
  | "87" -> (EQ_PKDECODE_MLDSA87, EQ_DECODEDPUBLICKEYSTRINGS_MLDSA87,
             EQ_SIGDECODE_FINAL_MLDSA87,
             EQ_VERIFY_INTERNAL_MU_CALLABLE_2_0_MLDSA87,
             EQ_VERIFY_INTERNAL_MU_CALLABLE_1_0_MLDSA87,
             EQ_VERIFY_INTERNAL_MU_CALLABLE_0_0_MLDSA87,
             EQ_SAMPLEINBALL_MLDSA87, EQ_INTVECTORNTT_7, EQ_INTVECTORNTT_8,
             EQ_MATRIXVECTORNTT_8_7_MLDSA87, EQ_SCALARVECTORNTT_8_MLDSA87,
             EQ_FIXEDVECTORSUBTRACT_8_NTT, EQ_VECTORNTTINV_8_MLDSA87,
             EQ_W1ENCODE_MLDSA87, EQ_INTVECTORINFNORM_7)
  | _ -> failwith "wv_thms";;

let wv_abstract p =
  match p with
    "44" -> TOP_VERIFY_MU_ABSTRACT_44
  | "65" -> TOP_VERIFY_MU_ABSTRACT_65
  | "87" -> TOP_VERIFY_MU_ABSTRACT_87
  | _ -> failwith "wv_abstract";;

let wv_def p =
  match p with
    "44" -> ML_DSA_Verify_internal_mu_MLDSA44_Configuration_hol_DEF
  | "65" -> ML_DSA_Verify_internal_mu_MLDSA65_Configuration_hol_DEF
  | "87" -> ML_DSA_Verify_internal_mu_MLDSA87_Configuration_hol_DEF
  | _ -> failwith "wv_def";;

let wv_hwdef p =
  match p with "44" -> mldsa44 | "65" -> mldsa65 | "87" -> mldsa87
  | _ -> failwith "wv_hwdef";;

(* UseHint takes values in [0, (q - 1)/(2 gamma2) - 1], which is the range   *)
(* that w1Encode requires.                                                   *)

let wv_usehint p =
  prove(wv_tm p "!h r. &0 <= mldsa_usehint @G2@ h r /\\
                       mldsa_usehint @G2@ h r <= &@UHMAX@",
   REPEAT GEN_TAC THEN
   MP_TAC(SPECL [wv_tm p "@G2@"; `h:bool`; `r:int`] WV_USEHINT_RANGE) THEN
   CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
   ANTS_TAC THENL
    [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
     REWRITE_TAC[];
     ALL_TAC] THEN
   INT_ARITH_TAC);;

(* The equation for NTTInv: the argument is the difference of two lifted     *)
(* vectors, not reduced, so reduce it first.                                 *)

let wv_nttinv lem l =
  let vec = rand l in
  let (i,b) = dest_abs(rand vec) in
  let g = rand b in
  let (k,bd) = dest_abs g in
  let a = mk_abs(i, mk_abs(k, mk_comb(mk_comb(`(rem):int->int->int`, bd),
                                      `(&8380417:int)`))) in
  let th = CONV_RULE(DEPTH_CONV BETA_CONV) (SPEC a lem) in
  REWRITE_RULE[NTT_REM_RANGE; NTT_LIFT_POLY_REM] th;;

(* The chain of the abstract lemma, for a signature whose hint part decodes  *)
(* to h. Hypotheses of the result: xof_ok, the two lengths and the decoding  *)
(* of the hints.                                                             *)

let wv_chain_some p =
  let (pkd,dec,sigd,c2,c1,c0,ball,nttl,nttk,matv,scal,subt,ninv,w1e,norm) =
    wv_thms p in
  let xo = ASSUME `xof_ok`
  and lpk = ASSUME(wv_tm p "LENGTH (pk:byte list) = @PK@")
  and lsg = ASSUME(wv_tm p "LENGTH (sg:byte list) = @SIG@")
  and hu = ASSUME(wv_tm p
     "mldsa_hintbitunpack @K@ @OM@ (mldsa_slice @HOFF@ @HLEN@ sg) = SOME h") in
  let uh = wv_usehint p in
  wv_asl := [xo; lpk; lsg];
  wv_tac := REPEAT CONJ_TAC THEN
            FIRST [FIRST_ASSUM ACCEPT_TAC;
                   ASM_SIMP_TAC[LENGTH_MLDSA_SLICE] THEN ASM_ARITH_TAC;
                   REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[uh]];
  let nmc s = "ML_DSA_Verify_internal_mu_@P@_Configuration_callable_" ^ s in
  let cn s = top_subst (wv_params p) s in
  let wvl = wv_lem in
  let table =
   [cn "pkDecode_@P@_Configuration_hol", wvl pkd;
    cn "DecodedPublicKeyStrings_@K@_@P@_Configuration_body_hol", wvl dec;
    cn "sigDecode_@P@_Configuration_hol",
       (fun l -> REWRITE_RULE[hu] (wvl sigd l));
    cn (nmc "2_0_call"), wvl c2;
    cn "SampleInBall_@P@_Configuration_hol", wvl ball;
    "IntPolyToRq_hol", wvl EQ_INTPOLYTORQ;
    cn "IntVectorNTT_@L@_hol", wvl nttl;
    cn "IntVectorNTT_@K@_hol", wvl nttk;
    cn "MatrixVectorNTT_@K@_@L@_@P@_Configuration_hol", wvl matv;
    "NTT_hol", wvl EQ_NTT;
    cn (nmc "1_0_call"), wvl c1;
    cn "ScalarVectorNTT_@K@_@P@_Configuration_hol", wvl scal;
    cn "FixedVectorSubtract_@K@_FIPS204_NTT_hol", wvl subt;
    cn "VectorNTTInv_@K@_@P@_Configuration_hol", wv_nttinv ninv;
    cn (nmc "0_0_call"), wvl c0;
    cn "w1Encode_@P@_Configuration_hol", wvl w1e;
    "HBytesString_hol", wvl BALL_HBYTESSTRING;
    cn "IntVectorInfNorm_@L@_hol", wvl norm] in
  wv_chain table (wv_abstract p);;

(* ------------------------------------------------------------------------- *)
(* The result of the chain is the handwritten verification, when the hints   *)
(* decode (NTT-domain form of FIPS 204 Algorithm 8, MLDSA_VERIFY_MU_FIPS).   *)
(* ------------------------------------------------------------------------- *)

let wv_some p =
  let res = wv_chain_some p in
  let uh = wv_usehint p in
  let _ = uh in
  prove(wv_tm p
   "!pk mu sg h.
      xof_ok /\\ LENGTH pk = @PK@ /\\ LENGTH sg = @SIG@ /\\
      mldsa_hintbitunpack @K@ @OM@ (mldsa_slice @HOFF@ @HLEN@ sg) = SOME h
      ==> ML_DSA_Verify_internal_mu_@P@_Configuration_hol pk mu sg =
          lift_verify_bool (mldsa_verify_mu @HW@ pk mu sg)",
   REPEAT STRIP_TAC THEN SUBST1_TAC res THEN
   REWRITE_TAC[TOP_LIFT_VERIFY_MU] THEN AP_TERM_TAC THEN
   REWRITE_TAC[distinctness "native_bottom"; COND_CLAUSES] THEN
   MP_TAC(SPECL (map (wv_tm p)
     ["@K@"; "@L@"; "@ETA@"; "@TAU@"; "@LAM@"; "@G1@"; "@G2@"; "@OM@";
      "pk:byte list"; "mu:byte list"; "sg:byte list"])
     MLDSA_VERIFY_MU_FIPS) THEN
   ANTS_TAC THENL [MATCH_MP_TAC WV_REJ THEN ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[wv_hwdef p] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC[MLDSA_BITLEN_CLAUSES; ARITH] THEN
   CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
   REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[] THEN
   MATCH_MP_TAC(TAUT `((a <=> a') /\ (b <=> b')) ==> ((a /\ b) <=> (a' /\ b'))`) THEN
   CONJ_TAC THENL
    [MP_TAC(SPECL [wv_tm p "@L@";
                   wv_tm p "\\i j. &@G1@ - mldsa_field @C@
                              (mldsa_slice @LAM4@ @ZLEN@ sg) (256 * i + j)";
                   wv_tm p "@ZB@"] WV_NORM) THEN
     ANTS_TAC THENL
      [REPEAT STRIP_TAC THEN BETA_TAC THEN
       MP_TAC(SPECL [wv_tm p "@C@"; wv_tm p "mldsa_slice @LAM4@ @ZLEN@ sg";
                     `256 * i + j`] MLDSA_FIELD_BOUND) THEN
       CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN INT_ARITH_TAC;
       ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC[ARITH_EQ];
     MATCH_MP_TAC WV_ENC THEN X_GEN_TAC `n:num` THEN BETA_TAC THEN
     REWRITE_TAC[WV_DIVMOD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     MATCH_MP_TAC MLDSA_NTT_INV_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
     BETA_TAC THEN
     REWRITE_TAC[WV_RING; mldsa_sample_in_ball; WV_MUL8192] THEN
     ASM_SIMP_TAC[MLDSA_EXPAND_A_NTT; LENGTH_MLDSA_SLICE; ARITH]]);;

(* ... and when they do not, both sides are false.                           *)

let wv_none p =
  let (pkd,dec,sigd,_,_,_,_,_,_,_,_,_,_,_,_) = wv_thms p in
  prove(wv_tm p
   "!pk mu sg.
      xof_ok /\\ LENGTH pk = @PK@ /\\ LENGTH sg = @SIG@ /\\
      mldsa_hintbitunpack @K@ @OM@ (mldsa_slice @HOFF@ @HLEN@ sg) = NONE
      ==> ML_DSA_Verify_internal_mu_@P@_Configuration_hol pk mu sg =
          lift_verify_bool (mldsa_verify_mu @HW@ pk mu sg)",
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[wv_def p] THEN REWRITE_TAC TOP_MONAD_RULES THEN
   ASM_SIMP_TAC[pkd; ARITH; dec; LENGTH_MLDSA_SLICE; sigd] THEN
   REWRITE_TAC TOP_MONAD_RULES THEN
   ASM_SIMP_TAC[dec; LENGTH_MLDSA_SLICE; ARITH] THEN
   REWRITE_TAC TOP_MONAD_RULES THEN
   REWRITE_TAC[TOP_LIFT_VERIFY_MU; wv_hwdef p; mldsa_verify_mu_accepts] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
   REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN
   CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The statements of toplevel.ml, STMT_VERIFY_INTERNAL_MU and                *)
(* STMT_VERIFY_INTERNAL                                                      *)
(* ------------------------------------------------------------------------- *)

let wv_mu p =
  let some = wv_some p and none = wv_none p in
  prove(top_tm p STMT_VERIFY_INTERNAL_MU,
   REPEAT STRIP_TAC THEN
   MP_TAC(ISPEC (wv_tm p
     "mldsa_hintbitunpack @K@ @OM@ (mldsa_slice @HOFF@ @HLEN@ sg)")
     (cases "option")) THEN
   STRIP_TAC THENL
    [ASM_MESON_TAC[none];
     ASM_MESON_TAC[some]]);;

let EQ_VERIFY_INTERNAL_MU_FINAL_MLDSA44,
    EQ_VERIFY_INTERNAL_MU_FINAL_MLDSA65,
    EQ_VERIFY_INTERNAL_MU_FINAL_MLDSA87 =
  wv_mu "44", wv_mu "65", wv_mu "87";;

let EQ_VERIFY_INTERNAL_FINAL_MLDSA44,
    EQ_VERIFY_INTERNAL_FINAL_MLDSA65,
    EQ_VERIFY_INTERNAL_FINAL_MLDSA87 =
  let f th mu = PROVE_HYP mu (PROVE_HYP ENC_BYTES_TO_BITS_STRING th) in
  f EQ_ML_DSA_VERIFY_INTERNAL_MLDSA44 EQ_VERIFY_INTERNAL_MU_FINAL_MLDSA44,
  f EQ_ML_DSA_VERIFY_INTERNAL_MLDSA65 EQ_VERIFY_INTERNAL_MU_FINAL_MLDSA65,
  f EQ_ML_DSA_VERIFY_INTERNAL_MLDSA87 EQ_VERIFY_INTERNAL_MU_FINAL_MLDSA87;;
