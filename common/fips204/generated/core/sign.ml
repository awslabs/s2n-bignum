(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the generated ML_DSA_Sign_internal_mu_P and                      *)
(* ML_DSA_Sign_internal_P compute the handwritten mldsa_sign_mu and          *)
(* mldsa_sign_internal, for P = MLDSA44, MLDSA65, MLDSA87.                   *)
(*                                                                           *)
(*   EQ_SIGN_INTERNAL_MU_P : STMT_SIGN_INTERNAL_MU of toplevel.ml            *)
(*   EQ_SIGN_INTERNAL_P    : STMT_SIGN_INTERNAL of toplevel.ml               *)
(*                                                                           *)
(* each under xof_ok /\ LENGTH sk = 2560 | 4032 | 4896, with Nontermination  *)
(* exactly when every attempt is rejected (mldsa_sign_mu = OutOfAttempts).   *)
(* The bound of the handwritten functions is NONE, the unbounded search of   *)
(* FIPS 204. No hypotheses remain: all six theorems have hyp th = [].        *)
(*                                                                           *)
(* Method.                                                                   *)
(* 1. WIRE_SIGN_LOOP_P, WIRE_SIGNI_LOOP_P: the abstract loop lemmas, with    *)
(*    the hypotheses of TOP_SIGN_LOOP_HYPS_P and TOP_SIGNI_LOOP_HYPS_P       *)
(*    (toplevel.ml) except one: the equation for the call of sigEncode       *)
(*    (callable_0_0) is only required for the accepted attempts (acc n ==>   *)
(*    ...). An earlier version in toplevel.ml (removed) asked it for every n,     *)
(*    but sigEncode is not defined for a rejected attempt with more than     *)
(*    omega + k hints (HintBitPack writes out of bounds). Each statement and *)
(*    proof is written once (wire_loop_hyps_tmpl, wire_loop_prove) and       *)
(*    instantiated for the six (set, family) pairs from the parameter table  *)
(*    wire_params0; only the helpers of toplevel.ml (SIGN*_EXT, sign*_wi, ...),   *)
(*    the DEF theorems and two callables (s1 decoding, norm of c t0) are     *)
(*    picked by hand per set (wire_loop_helpers, wire_loop_params).          *)
(* 2. WIRE_CHAIN_P: every other hypothesis of the loop lemma, for explicit   *)
(*    "natural" values (the unreduced integer arrays that the generated      *)
(*    code computes: ysamp, wn, cs1n, cs2n, ct0n, ...), from the component   *)
(*    lemmas of the other files. Function variables with defining equations  *)
(*    keep the terms small; they are replaced by their definitions at the    *)
(*    end.                                                                   *)
(* 3. WIRE_BR_P (the bridge): with WIRE_ATT, a generic lemma on one attempt  *)
(*    of the handwritten spec, it shows that the acceptance test on the      *)
(*    natural values holds exactly when mldsa_sign_attempt is not NONE, and  *)
(*    then returns the signature of sigEncode. Reduced and unreduced         *)
(*    arrays agree up to congruence mod q (MLDSA_MODPM_CONG, ...). No use of *)
(*    the alternative low-bits check is needed: the generated code tests     *)
(*    LowBits(w - c s2) as FIPS 204 does.                                    *)
(* 4. wire_final_prove: the abstract loop lemma, the chain and the unfolding *)
(*    of mldsa_sign_mu give the statements.                                  *)
(*                                                                           *)
(* The ranges that the callers guarantee are all derived: the rejection      *)
(* test makes the entries of z and the hint count fit sigEncode.             *)
(*                                                                           *)
(* Load from the repository root after base.ml and common.ml.          *)
(* ========================================================================= *)

needs "common/fips204/generated/core/toplevel.ml";;
needs "common/fips204/generated/core/rounding.ml";;
needs "common/fips204/generated/core/sample.ml";;
needs "common/fips204/generated/core/ball.ml";;
needs "common/fips204/generated/core/hints.ml";;
needs "common/fips204/generated/core/sigcodec.ml";;
needs "common/fips204/generated/core/callables.ml";;
needs "common/fips204/generated/core/encode.ml";;
needs "common/fips204/generated/core/ntt.ml";;
needs "common/fips204/generated/core/ntt_vec.ml";;

(* ------------------------------------------------------------------------- *)
(* The parameter sets and the instantiation machinery. Template macros: @K@  *)
(* @L@ matrix dimensions, @ETA@, @C@ (bits of an s coefficient), @TAU@,      *)
(* @LAM@, @G1@ (gamma1), @CY@ (bits of a y coefficient), @YB@ (bytes of      *)
(* ExpandMask output), @G2@ (gamma2), @W1C@ (bits of a w1 coefficient),      *)
(* @CTL@ (bytes of c~), @OM@ (omega), @ZB@ = gamma1 - beta, @RB@ = gamma2 -  *)
(* beta, and offsets and lengths of the slices of sk.                        *)
(* ------------------------------------------------------------------------- *)

let wire_params0 p =
  match p with
    "44" -> ["@P@","MLDSA44"; "@HW@","mldsa44"; "@SK@","2560"; "@K@","4"; "@L@","4";
             "@ETA@","2"; "@C@","3"; "@TAU@","39"; "@LAM@","128"; "@G1@","131072";
             "@CY@","18"; "@YB@","576"; "@G2@","95232"; "@W1C@","6"; "@CTL@","32";
             "@OM@","80"; "@ZB@","130994"; "@RB@","95154";
             "@S1OFF@","128"; "@S1LEN@","384"; "@S2OFF@","512"; "@S2LEN@","384";
             "@T0OFF@","896"; "@T0LEN@","1664"]
  | "65" -> ["@P@","MLDSA65"; "@HW@","mldsa65"; "@SK@","4032"; "@K@","6"; "@L@","5";
             "@ETA@","4"; "@C@","4"; "@TAU@","49"; "@LAM@","192"; "@G1@","524288";
             "@CY@","20"; "@YB@","640"; "@G2@","261888"; "@W1C@","4"; "@CTL@","48";
             "@OM@","55"; "@ZB@","524092"; "@RB@","261692";
             "@S1OFF@","128"; "@S1LEN@","640"; "@S2OFF@","768"; "@S2LEN@","768";
             "@T0OFF@","1536"; "@T0LEN@","2496"]
  | "87" -> ["@P@","MLDSA87"; "@HW@","mldsa87"; "@SK@","4896"; "@K@","8"; "@L@","7";
             "@ETA@","2"; "@C@","3"; "@TAU@","60"; "@LAM@","256"; "@G1@","524288";
             "@CY@","20"; "@YB@","640"; "@G2@","261888"; "@W1C@","4"; "@CTL@","64";
             "@OM@","75"; "@ZB@","524168"; "@RB@","261768";
             "@S1OFF@","128"; "@S1LEN@","672"; "@S2OFF@","800"; "@S2LEN@","768";
             "@T0OFF@","1568"; "@T0LEN@","3328"]
  | _ -> failwith "wire_params";;

let wire_params p =
  let base = wire_params0 p in
  let g s = int_of_string(assoc s base) in
  base @ ["@K256@",string_of_int(256 * g "@K@"); "@L256@",string_of_int(256 * g "@L@")];;

let wire_tm p s = parse_term (top_subst (wire_params p) s);;

(* ------------------------------------------------------------------------- *)
(* Part 1: the abstract loop lemmas, with sigEncode required only for the    *)
(* accepted attempt. One template per family, instantiated for each P.       *)
(*                                                                           *)
(* The two families (fam = "mu" for ML_DSA_Sign_internal_mu_P, "internal"    *)
(* for ML_DSA_Sign_internal_P) differ only in the prefix @SG@ of the         *)
(* generated callables, in the extra premise @PRE@ (mu is computed from tr   *)
(* and M), and in the name of the message variable. The parameter sets       *)
(* differ in the dimensions K and L, the length @CTL@ of c~, the bounds      *)
(* @ZB@, @RB@, @G2@, @OM@ of the acceptance test (all from wire_params0),    *)
(* and in two places that come from the generated code: s1 is decoded by     *)
(* callable_5 for 44 but callable_6 for 65 and 87 (@S1C@), and the norm of c *)
(* t0 is callable_3 (as for z) for 44 but RqVectorInfNorm_K for 65 and 87    *)
(* (@NCTL@). The helpers that toplevel.ml defines per set (SIGN*_EXT,        *)
(* sign*_wi, sign*_Q, sign*_rej, and the same with signi) are selected by    *)
(* wire_loop_helpers; the loop proof itself is written once.                 *)
(* ------------------------------------------------------------------------- *)

let wire_loop_hyps_tmpl =
 "skDecode_@P@_Configuration_hol sk = Value (rho,K,tr,s1,s2,t0) /\\
  LENGTH rho = 32 /\\ LENGTH K = 32 /\\ LENGTH tr = 64 /\\
  @PRE@
  @SG@_Configuration_callable_@S1C@_0_call (Native_Value s1) = Value S1 /\\
  @SG@_Configuration_callable_5_0_call (Native_Value s2) = Value S2 /\\
  @SG@_Configuration_callable_5_0_call (Native_Value t0) = Value T0 /\\
  @SG@_Configuration_callable_4_0_call (Native_Value rho) = Value A /\\
  HBytesString_hol (APPEND (APPEND K rnd) mu) (&64) = Value rho2 /\\ LENGTH rho2 = 64 /\\
  (!n. ExpandMask_@P@_Configuration_hol rho2 (&(@L@ * n)) = Value (Y n)) /\\
  (!n. IntVectorToRq_@L@_body_hol (Y n) = Value (Yq n)) /\\
  (!n. VectorNTT_@L@_@P@_Configuration_hol (Yq n) = Value (Yh n)) /\\
  (!n. MatrixVectorNTT_@K@_@L@_@P@_Configuration_hol A (Yh n) = Value (Wh n)) /\\
  (!n. VectorNTTInv_@K@_@P@_Configuration_hol (Wh n) = Value (W n)) /\\
  (!n. FixedVectorHighBits_@K@_@P@_Configuration_hol (W n) = Value (W1 n)) /\\
  (!n. w1Encode_@P@_Configuration_hol (W1 n) = Value (Native_Value (W1E n))) /\\
  (!n. HBytesString_hol (APPEND mu (W1E n)) (&@CTL@) = Value (CT n)) /\\
  (!n. SampleInBall_@P@_Configuration_hol (CT n) = Value (C n)) /\\
  (!n. IntPolyToRq_hol (C n) = Value (Cq n)) /\\
  (!n. NTT_hol (Cq n) = Value (Ch n)) /\\
  (!n. ScalarVectorNTT_@L@_@P@_Configuration_hol (Ch n) S1 = Value (CS1h n)) /\\
  (!n. VectorNTTInv_@L@_@P@_Configuration_hol (CS1h n) = Value (CS1 n)) /\\
  (!n. ScalarVectorNTT_@K@_@P@_Configuration_hol (Ch n) S2 = Value (CS2h n)) /\\
  (!n. VectorNTTInv_@K@_@P@_Configuration_hol (CS2h n) = Value (CS2 n)) /\\
  (!n. RqVectorAdd_@L@_hol (Yq n) (CS1 n) = Value (Z n)) /\\
  (!n. FixedVectorSubtract_@K@_FIPS204_Time_hol (W n) (CS2 n) = Value (R n)) /\\
  (!n. FixedVectorLowBits_@K@_@P@_Configuration_hol (R n) = Value (R0 n)) /\\
  (!n. @SG@_Configuration_callable_3_0_call (Native_Value (Z n)) = Value (NZ n)) /\\
  (!n. IntVectorInfNorm_@K@_hol (R0 n) = Value (NR n)) /\\
  (!n. ScalarVectorNTT_@K@_@P@_Configuration_hol (Ch n) T0 = Value (CT0h n)) /\\
  (!n. VectorNTTInv_@K@_@P@_Configuration_hol (CT0h n) = Value (CT0 n)) /\\
  (!n. RqVectorNegate_@K@_hol (CT0 n) = Value (NCT0 n)) /\\
  (!n. RqVectorAdd_@K@_hol (R n) (CT0 n) = Value (RC n)) /\\
  (!n. FixedVectorMakeHint_@K@_@P@_Configuration_hol (NCT0 n) (RC n) = Value (HV n)) /\\
  (!n. @NCTL@ = Value (NCT n)) /\\
  (!n. @SG@_Configuration_callable_2_0_call (Native_Value (HV n)) = Value (CNT n)) /\\
  (!n. @SG@_Configuration_callable_1_0_call (Native_Value (Z n)) (&8380417) = Value (Native_Value (ZC n))) /\\
  (!n. acc n ==> @SG@_Configuration_callable_0_0_call (CT n) (Native_Value (ZC n)) (Native_Value (HV n)) = Value (SIG n)) /\\
  (!n. acc n <=> ~((&0 <= NZ n - &@ZB@ \\/ &0 <= NR n - &@RB@) \\/
                   (&0 <= NCT n - &@G2@ \\/ &0 < CNT n - &@OM@)))";;

(* The macros that depend on the family and on the generated code.           *)
let wire_loop_params p fam =
  (if p = "44" then ["@S1C@","5"; "@NCTL@","@SG@_Configuration_callable_3_0_call (Native_Value (CT0 n))"]
   else ["@S1C@","6"; "@NCTL@","RqVectorInfNorm_@K@_hol (CT0 n)"]) @
  (match fam with
     "mu" -> ["@SG@","ML_DSA_Sign_internal_mu_@P@"; "@PRE@",""; "@MSG@","mu"]
   | _ -> ["@SG@","ML_DSA_Sign_internal_@P@";
           "@PRE@","BytesToBitsString_hol tr = Value TRB /\\ H_hol (APPEND TRB M) (&64) = Value mu /\\";
           "@MSG@","M"]);;

let wire_loop_tm p fam s =
  let s' = top_subst (wire_loop_params p fam) s in
  parse_term (top_subst (wire_params p) s');;

(* Per set and family: the DEF theorems and the helpers of toplevel.ml.      *)
let wire_loop_helpers p fam =
  match fam,p with
    "mu","44" -> ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_DEF, SIGN44_EXT, sign44_wi, sign44_rej, sign44_Q
  | "mu","65" -> ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_DEF, SIGN65_EXT, sign65_wi, sign65_rej, sign65_Q
  | "mu","87" -> ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_DEF, SIGN87_EXT, sign87_wi, sign87_rej, sign87_Q
  | "internal","44" -> ML_DSA_Sign_internal_MLDSA44_Configuration_hol_DEF, SIGNI44_EXT, signi44_wi, signi44_rej, signi44_Q
  | "internal","65" -> ML_DSA_Sign_internal_MLDSA65_Configuration_hol_DEF, SIGNI65_EXT, signi65_wi, signi65_rej, signi65_Q
  | "internal","87" -> ML_DSA_Sign_internal_MLDSA87_Configuration_hol_DEF, SIGNI87_EXT, signi87_wi, signi87_rej, signi87_Q
  | _ -> failwith "wire_loop_helpers";;

let wire_decoded_sk_def p =
  match p with
    "44" -> DecodedSecretKeyStrings_4_4_MLDSA44_Configuration_body_hol_DEF
  | "65" -> DecodedSecretKeyStrings_5_6_MLDSA65_Configuration_body_hol_DEF
  | "87" -> DecodedSecretKeyStrings_7_8_MLDSA87_Configuration_body_hol_DEF
  | _ -> failwith "wire_decoded_sk_def";;

let WIRE_SIGN_LOOP_HYPS_44 = wire_loop_tm "44" "mu" wire_loop_hyps_tmpl;;
let WIRE_SIGN_LOOP_HYPS_65 = wire_loop_tm "65" "mu" wire_loop_hyps_tmpl;;
let WIRE_SIGN_LOOP_HYPS_87 = wire_loop_tm "87" "mu" wire_loop_hyps_tmpl;;
let WIRE_SIGNI_LOOP_HYPS_44 = wire_loop_tm "44" "internal" wire_loop_hyps_tmpl;;
let WIRE_SIGNI_LOOP_HYPS_65 = wire_loop_tm "65" "internal" wire_loop_hyps_tmpl;;
let WIRE_SIGNI_LOOP_HYPS_87 = wire_loop_tm "87" "internal" wire_loop_hyps_tmpl;;

let wire_loop_hyps p fam =
  match fam,p with
    "mu","44" -> WIRE_SIGN_LOOP_HYPS_44 | "mu","65" -> WIRE_SIGN_LOOP_HYPS_65
  | "mu","87" -> WIRE_SIGN_LOOP_HYPS_87 | "internal","44" -> WIRE_SIGNI_LOOP_HYPS_44
  | "internal","65" -> WIRE_SIGNI_LOOP_HYPS_65 | "internal","87" -> WIRE_SIGNI_LOOP_HYPS_87
  | _ -> failwith "wire_loop_hyps";;

(* The statement of the abstract loop lemma.                                 *)
let wire_loop_stmt p fam =
  mk_imp(wire_loop_hyps p fam,
    wire_loop_tm p fam
     "@SG@_Configuration_hol sk @MSG@ rnd =
      if ?n. acc n then Value (SIG (minimal n. acc n)) else Nontermination");;

(* The proof. After the unfolding of the generated function,                 *)
(* TOP_NATIVE_WHILE (toplevel.ml) is applied to the loop (TOP_WHILE_TAC);    *)
(* the two halves of it are the loop invariant, proved by the case splits on *)
(* the two rejection tests, and the final consequence (case on ?n. acc n,    *)
(* then native_finish and the post-loop reads of c_tilde, z, h with Q).      *)
let wire_loop_prove p fam =
  let def,ext,wi,rej,q = wire_loop_helpers p fam in
  let hyps = wire_loop_hyps p fam in
  let accth = ASSUME(wire_loop_tm p fam
    "!n. (acc:num->bool) n <=> ~((&0 <= (NZ:num->int) n - &@ZB@ \\/ &0 <= (NR:num->int) n - &@RB@) \\/ (&0 <= (NCT:num->int) n - &@G2@ \\/ &0 < (CNT:num->int) n - &@OM@))") in
  let weakth = ASSUME (find (fun c -> try is_imp(snd(dest_forall c)) with Failure _ -> false) (conjuncts hyps)) in
  let steps = [
    STRIP_TAC THEN REWRITE_TAC[def] THEN
    REWRITE_TAC TOP_MONAD_RULES THEN
    ASM_REWRITE_TAC[wire_decoded_sk_def p] THEN
    REWRITE_TAC TOP_MONAD_RULES THEN
    ASM_SIMP_TAC(TYPED_HOL_LIST_SLICE_ALL :: COMMON_VEC_INTPOLY_ID :: TOP_MONAD_RULES) THEN
    ASM_SIMP_TAC(typed_hol_bottom_sequence_extent_DEF :: TOP_MONAD_RULES);
    TOP_WHILE_TAC wi rej q THEN BETA_TAC;
    ANTS_TAC THENL [CONJ_TAC THENL [REWRITE_TAC(MULT_CLAUSES :: ext); CONJ_TAC]; ALL_TAC];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC(TYPED_HOL_SLOT_READ :: TOP_MONAD_RULES);
    REPEAT STRIP_TAC THEN REWRITE_TAC[TYPED_HOL_LET] THEN
    ASM_REWRITE_TAC(TYPED_HOL_SLOT_READ :: TOP_MONAD_RULES) THEN
    ASM_SIMP_TAC(TYPED_HOL_SEQUENCE_EXTENT :: TYPED_HOL_SLOT_READ :: TOP_MONAD_RULES);
    GEN_SIMP_TAC[TOP_BIND_COND];
    GEN_SIMP_TAC[TOP_BIND_COND; UNCURRY_DEF];
    ASM_CASES_TAC(wire_loop_tm p fam "&0 <= (NZ:num->int) n - &@ZB@ \\/ &0 <= (NR:num->int) n - &@RB@") THEN
    ASM_REWRITE_TAC[NATIVE_RESULT_INJ; STATEMENT_OUTCOME_INJ; UNWIND_THM1] THENL
    [REWRITE_TAC ext; ALL_TAC];
    REWRITE_TAC[INT_OF_NUM_ADD; NATIVE_SLOT_INJ; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ASM_CASES_TAC(wire_loop_tm p fam "&0 <= (NCT:num->int) n - &@G2@ \\/ &0 < (CNT:num->int) n - &@OM@") THEN
    ASM_REWRITE_TAC[NATIVE_RESULT_INJ; STATEMENT_OUTCOME_INJ; UNWIND_THM1] THEN
    REWRITE_TAC ext THEN
    REWRITE_TAC(INT_OF_NUM_ADD :: NATIVE_SLOT_INJ :: INT_OF_NUM_EQ ::
                TYPED_HOL_SLOT_READ :: GEN_MONAD_RULES) THEN TRY ARITH_TAC;
    (* Remaining goal: (two halves of TOP_NATIVE_WHILE) ==> native_finish (...) = *)
    (* if ?n. acc n then Value (SIG (minimal n. acc n)) else Nontermination.     *)
    STRIP_TAC THEN REWRITE_TAC[accth];
    ASM_CASES_TAC `?n. (acc:num->bool) n` THENL
     [SUBGOAL_THEN `~(!n. ~((acc:num->bool) n))` (fun nf ->
        FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_imp c && is_neg(lhand c))) THEN
        DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MP th nf))) THENL
       [POP_ASSUM MP_TAC THEN MESON_TAC[]; ALL_TAC];
      ALL_TAC];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_CLAUSES]) THEN
    ASM_REWRITE_TAC(accth :: NATIVE_FINISH :: TYPED_HOL_SLOT_READ :: TOP_MONAD_RULES);
    REWRITE_TAC[GSYM accth] THEN
    FIRST_ASSUM(fun th -> if aconv (concl th) `?n. (acc:num->bool) n` then
      let accm = CONJUNCT1(EQ_MP (BETA_RULE(ISPEC `\n. (acc:num->bool) n` MINIMAL)) th) in
      REWRITE_TAC[EQT_INTRO th; MP (SPEC `minimal n. (acc:num->bool) n` weakth) accm]
    else NO_TAC);
    SUBGOAL_THEN `!n. ~((acc:num->bool) n)` ASSUME_TAC THENL [POP_ASSUM MP_TAC THEN MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM accth] THEN ASM_REWRITE_TAC[NATIVE_FINISH];
    FIRST_X_ASSUM(fun th -> if is_imp(concl th) && aconv (lhand(concl th)) `!n. ~((acc:num->bool) n)` then MP_TAC(MP th (ASSUME `!n. ~((acc:num->bool) n)`)) else NO_TAC) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; NATIVE_FINISH])] in
  (* Each step acts on the first remaining goal only, as with e().          *)
  match List.fold_left (fun gs t -> by (VALID t) gs)
          (mk_goalstate([],wire_loop_stmt p fam)) steps with
    (_,[],f) -> f null_inst []
  | _ -> failwith "wire_loop_prove: goals remain";;

let WIRE_SIGN_LOOP_44 = wire_loop_prove "44" "mu";;
let WIRE_SIGN_LOOP_65 = wire_loop_prove "65" "mu";;
let WIRE_SIGN_LOOP_87 = wire_loop_prove "87" "mu";;
let WIRE_SIGNI_LOOP_44 = wire_loop_prove "44" "internal";;
let WIRE_SIGNI_LOOP_65 = wire_loop_prove "65" "internal";;
let WIRE_SIGNI_LOOP_87 = wire_loop_prove "87" "internal";;

(* ------------------------------------------------------------------------- *)
(* Part 2: generic lemmas on one attempt of the handwritten spec and on      *)
(* congruences mod q.                                                        *)
(* ------------------------------------------------------------------------- *)

let wire_eq_rewrite v = FIRST_ASSUM(fun th -> if (try lhs(concl th) = v with Failure _ -> false) then REWRITE_TAC[th] else NO_TAC);;
let WIRE_NTT_MUL = prove
 (`!c f. c IN ring_carrier mldsa_rq /\ f IN ring_carrier mldsa_rq
         ==> mldsa_ntt_inv (\k. (mldsa_ntt c k * mldsa_ntt f k) rem &8380417) =
             ring_mul mldsa_rq c f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:(1->num)->int`; `f:(1->num)->int`] MLDSA_NTT_INV_MUL) THEN
  ASM_REWRITE_TAC[MLDSA_ZQ]);;

let WIRE_EXPAND_A_RQ = prove
 (`!rho i j. LENGTH rho < 166 ==> mldsa_expand_a rho i j IN ring_carrier mldsa_rq`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_expand_a] THEN
  MP_TAC(ISPEC `mldsa_rej_ntt_poly (APPEND rho [word j; word i])`
    MLDSA_NTT_INV) THEN
  ANTS_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MLDSA_REJ_NTT_POLY_RANGE THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC;
    SIMP_TAC[]]);;

let WIRE_HINT_CONG = prove
 (`!k omega h h'. (!p. p < 256 * k ==> (h p <=> h' p))
        ==> mldsa_hintbitpack k omega h = mldsa_hintbitpack k omega h' /\
            mldsa_hint_count h (256 * k) = mldsa_hint_count h' (256 * k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!p. p <= 256 * k ==> mldsa_hint_count h p = mldsa_hint_count h' p`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_hint_count] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `q:num` THEN
    ASM_CASES_TAC `q < p` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `q < 256 * k` (fun th -> ASM_SIMP_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LE_REFL] THEN
  REWRITE_TAC[mldsa_hintbitpack] THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  BETA_TAC THEN
  ASM_CASES_TAC `t < omega` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN
     `!p. (p < 256 * k /\ h p /\ mldsa_hint_count h p = t) <=>
          (p < 256 * k /\ h' p /\ mldsa_hint_count h' p = t)`
     (fun th -> REWRITE_TAC[th]) THEN
    X_GEN_TAC `p:num` THEN ASM_CASES_TAC `p < 256 * k` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[LT_IMP_LE];
    SUBGOAL_THEN `256 * (t - omega + 1) <= 256 * k` (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_ARITH_TAC]);;

let WIRE_ATT_EQS = `
    y = (\i. mldsa_expand_mask g1 rho2 kappa i) /\
    w = (\i. mldsa_dot l (A i) y) /\
    w1 = (\n. mldsa_highbits g2 (coeff (n MOD 256) (w (n DIV 256)))) /\
    ct = mldsa_h (APPEND mu (mldsa_encode (mldsa_bitlen (8380416 DIV (2 * g2) - 1)) (256 * k) w1)) (lam DIV 4) /\
    c = mldsa_sample_in_ball tau ct /\
    z = (\i. ring_add mldsa_rq (y i) (ring_mul mldsa_rq c (s1 i))) /\
    r = (\i. ring_sub mldsa_rq (w i) (ring_mul mldsa_rq c (s2 i))) /\
    ct0 = (\i. ring_mul mldsa_rq c (t0 i)) /\
    hh = (\p. p < 256 * k /\ mldsa_makehint g2 (--(coeff (p MOD 256) (ct0 (p DIV 256))))
                (coeff (p MOD 256) (ring_add mldsa_rq (r (p DIV 256)) (ct0 (p DIV 256)))))`;;

let WIRE_ATT_UNFOLD = prove
 (`!k l eta tau lam g1 g2 om A s1 s2 t0 mu rho2 kappa y w w1 ct c z r ct0 hh.
    y = (\i. mldsa_expand_mask g1 rho2 kappa i) /\
    w = (\i. mldsa_dot l (A i) y) /\
    w1 = (\n. mldsa_highbits g2 (coeff (n MOD 256) (w (n DIV 256)))) /\
    ct = mldsa_h (APPEND mu (mldsa_encode (mldsa_bitlen (8380416 DIV (2 * g2) - 1)) (256 * k) w1)) (lam DIV 4) /\
    c = mldsa_sample_in_ball tau ct /\
    z = (\i. ring_add mldsa_rq (y i) (ring_mul mldsa_rq c (s1 i))) /\
    r = (\i. ring_sub mldsa_rq (w i) (ring_mul mldsa_rq c (s2 i))) /\
    ct0 = (\i. ring_mul mldsa_rq c (t0 i)) /\
    hh = (\p. p < 256 * k /\ mldsa_makehint g2 (--(coeff (p MOD 256) (ct0 (p DIV 256))))
                (coeff (p MOD 256) (ring_add mldsa_rq (r (p DIV 256)) (ct0 (p DIV 256)))))
    ==> mldsa_sign_attempt (k,l,eta,tau,lam,g1,g2,om) A s1 s2 t0 mu rho2 kappa =
        (if mldsa_vec_norm_lt l (g1 - tau * eta) z /\
            (!i j. i < k /\ j < 256
                   ==> abs(mldsa_lowbits g2 (coeff j (r i))) < &(g2 - tau * eta)) /\
            mldsa_vec_norm_lt k g2 ct0 /\
            mldsa_hint_count hh (256 * k) <= om
         then SOME (APPEND ct
                (APPEND (mldsa_encode (1 + mldsa_bitlen (g1 - 1)) (256 * l)
                          (\n. &g1 - mldsa_modpm (coeff (n MOD 256) (z (n DIV 256))) 8380417))
                        (mldsa_hintbitpack k om hh)))
         else NONE)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = v with Failure _ -> false) then SUBST_ALL_TAC th else NO_TAC))
   [`hh:num->bool`; `ct0:num->(1->num)->int`; `r:num->(1->num)->int`; `z:num->(1->num)->int`; `c:(1->num)->int`; `ct:byte list`; `w1:num->int`; `w:num->(1->num)->int`; `y:num->(1->num)->int`] THEN
  REWRITE_TAC[mldsa_sign_attempt] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BETA_TAC THEN
  REFL_TAC);;

let WIRE_ATT_STMT = `!k l eta tau lam g1 g2 om A s1 s2 t0 mu rho2 kappa y w w1 ct c z r ct0 hh hg.
    tau * eta < g1 /\ tau * eta < g2 /\
    (!i. i < l ==> s1 i IN ring_carrier mldsa_rq) /\
    (!i. i < k ==> s2 i IN ring_carrier mldsa_rq /\
                   t0 i IN ring_carrier mldsa_rq) /\
    y = (\i. mldsa_expand_mask g1 rho2 kappa i) /\
    w = (\i. mldsa_dot l (A i) y) /\
    w1 = (\n. mldsa_highbits g2 (coeff (n MOD 256) (w (n DIV 256)))) /\
    ct = mldsa_h (APPEND mu (mldsa_encode (mldsa_bitlen (8380416 DIV (2 * g2) - 1)) (256 * k) w1)) (lam DIV 4) /\
    c = mldsa_sample_in_ball tau ct /\
    z = (\i. ring_add mldsa_rq (y i) (ring_mul mldsa_rq c (s1 i))) /\
    r = (\i. ring_sub mldsa_rq (w i) (ring_mul mldsa_rq c (s2 i))) /\
    ct0 = (\i. ring_mul mldsa_rq c (t0 i)) /\
    hh = (\p. p < 256 * k /\ mldsa_makehint g2 (--(coeff (p MOD 256) (ct0 (p DIV 256))))
                (coeff (p MOD 256) (ring_add mldsa_rq (r (p DIV 256)) (ct0 (p DIV 256))))) /\
    hg = (\p. mldsa_makehint g2 (--(coeff (p MOD 256) (ct0 (p DIV 256))))
                (coeff (p MOD 256) (r (p DIV 256)) + coeff (p MOD 256) (ct0 (p DIV 256))))
    ==> (~(mldsa_sign_attempt (k,l,eta,tau,lam,g1,g2,om) A s1 s2 t0 mu rho2 kappa = NONE) <=>
         ~((&0 <= round_infnorm l (\i j. mldsa_modpm (coeff j (z i)) 8380417) - &(g1 - tau * eta) \/
            &0 <= round_infnorm k (\i j. mldsa_lowbits g2 (coeff j (r i))) - &(g2 - tau * eta)) \/
           (&0 <= round_infnorm k (\i j. mldsa_modpm (coeff j (ct0 i)) 8380417) - &g2 \/
            (&0:int) < &(mldsa_hint_count hg (256 * k)) - &om))) /\
        (~(mldsa_sign_attempt (k,l,eta,tau,lam,g1,g2,om) A s1 s2 t0 mu rho2 kappa = NONE)
         ==> mldsa_sign_attempt (k,l,eta,tau,lam,g1,g2,om) A s1 s2 t0 mu rho2 kappa =
             SOME (APPEND ct
                    (APPEND (mldsa_encode (1 + mldsa_bitlen (g1 - 1)) (256 * l)
                              (\n. &g1 - mldsa_modpm (coeff (n MOD 256) (z (n DIV 256))) 8380417))
                            (mldsa_hintbitpack k om hg))))`;;

let WIRE_CNT_LEM = prove(`!a b. (&0:int) < &a - &b <=> ~(a <= b)`, REWRITE_TAC[INT_SUB_LT; INT_OF_NUM_LT; NOT_LE]);;

let WIRE_ATT = prove(WIRE_ATT_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `l:num`; `eta:num`; `tau:num`; `lam:num`; `g1:num`; `g2:num`; `om:num`; `A:num->num->(1->num)->int`; `s1:num->(1->num)->int`; `s2:num->(1->num)->int`; `t0:num->(1->num)->int`; `mu:byte list`; `rho2:byte list`; `kappa:num`; `y:num->(1->num)->int`; `w:num->(1->num)->int`; `w1:num->int`; `ct:byte list`; `c:(1->num)->int`; `z:num->(1->num)->int`; `r:num->(1->num)->int`; `ct0:num->(1->num)->int`; `hh:num->bool`] WIRE_ATT_UNFOLD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `!i. (y:num->(1->num)->int) i IN ring_carrier mldsa_rq` (LABEL_TAC "yrq") THENL
   [GEN_TAC THEN wire_eq_rewrite `y:num->(1->num)->int` THEN REWRITE_TAC[MLDSA_EXPAND_MASK_IN_RQ]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. (w:num->(1->num)->int) i IN ring_carrier mldsa_rq` (LABEL_TAC "wrq") THENL
   [GEN_TAC THEN wire_eq_rewrite `w:num->(1->num)->int` THEN REWRITE_TAC[MLDSA_DOT_IN_RQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:(1->num)->int) IN ring_carrier mldsa_rq` (LABEL_TAC "crq") THENL
   [wire_eq_rewrite `c:(1->num)->int` THEN REWRITE_TAC[MLDSA_SAMPLE_IN_BALL_IN_RQ]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < k ==> (r:num->(1->num)->int) i IN ring_carrier mldsa_rq /\ (ct0:num->(1->num)->int) i IN ring_carrier mldsa_rq` (LABEL_TAC "rrq") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(MP (SPEC `i:num` (ASSUME `!i. i < k ==> (s2:num->(1->num)->int) i IN ring_carrier mldsa_rq /\ (t0:num->(1->num)->int) i IN ring_carrier mldsa_rq`)) (ASSUME `i:num < k`)) THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [wire_eq_rewrite `r:num->(1->num)->int` THEN BETA_TAC THEN MATCH_MP_TAC RING_SUB THEN
      CONJ_TAC THENL [USE_THEN "wrq" MATCH_ACCEPT_TAC; MATCH_MP_TAC RING_MUL THEN ASM_REWRITE_TAC[] THEN USE_THEN "crq" MATCH_ACCEPT_TAC];
      wire_eq_rewrite `ct0:num->(1->num)->int` THEN BETA_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_REWRITE_TAC[] THEN USE_THEN "crq" MATCH_ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. p < 256 * k ==> ((hh:num->bool) p <=> (hg:num->bool) p)` (LABEL_TAC "hagree") THENL
   [X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `p DIV 256 < k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "rrq" (MP_TAC o SPEC `p DIV 256`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    wire_eq_rewrite `hh:num->bool` THEN wire_eq_rewrite `hg:num->bool` THEN BETA_TAC THEN
    REWRITE_TAC[ASSUME `p < 256 * k`] THEN
    MP_TAC(MP (SPECL [`(r:num->(1->num)->int) (p DIV 256)`; `(ct0:num->(1->num)->int) (p DIV 256)`; `p MOD 256`] MLDSA_RQ_COEFF_ADD) (CONJ (ASSUME `(r:num->(1->num)->int) (p DIV 256) IN ring_carrier mldsa_rq`) (ASSUME `(ct0:num->(1->num)->int) (p DIV 256) IN ring_carrier mldsa_rq`))) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MLDSA_MAKEHINT_REM];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (SPECL [`k:num`; `om:num`; `hh:num->bool`; `hg:num->bool`] WIRE_HINT_CONG) o check (fun th -> concl th = `!p. p < 256 * k ==> ((hh:num->bool) p <=> (hg:num->bool) p)`)) THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if (try is_var(lhs(concl th)) with Failure _ -> false) then ALL_TAC else NO_TAC)) THEN
  SUBGOAL_THEN `~(g1 - tau * eta = 0) /\ ~(g2 - tau * eta = 0) /\ ~(g2 = 0)` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`l:num`; `g1 - tau * eta`; `z:num->(1->num)->int`] ROUND_INFNORM_VEC_NORM_GE) THEN
  MP_TAC(SPECL [`k:num`; `g2:num`; `ct0:num->(1->num)->int`] ROUND_INFNORM_VEC_NORM_GE) THEN
  MP_TAC(SPECL [`k:num`; `\i j. mldsa_lowbits g2 (coeff j ((r:num->(1->num)->int) i))`; `&(g2 - tau * eta):int`] ROUND_INFNORM_GE) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LT] THEN
  SUBGOAL_THEN `0 < g2 - tau * eta` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[WIRE_CNT_LEM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  ASM_MESON_TAC[]);;

let WIRE_CONG_REFL = INTEGER_RULE `!x n:int. (x == x) (mod n)`;;

let WIRE_CONG_ADD = prove
 (`!n r x c:int. (r == x) (mod n) ==> (r + c == x + c) (mod n)`,
  CONV_TAC INTEGER_RULE);;

let WIRE_REM_CONG = prove
 (`!x c. (x rem &8380417 + c == x + c) (mod &8380417)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WIRE_CONG_ADD THEN
  REWRITE_TAC[MLDSA_REM_Q]);;

let WIRE_MODPM_ADD = prove
 (`!a b. mldsa_modpm (((a rem &8380417) + b) rem &8380417) 8380417 =
         mldsa_modpm (a + b) 8380417`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MLDSA_MODPM_REM] THEN
  MATCH_MP_TAC MLDSA_MODPM_CONG THEN REWRITE_TAC[WIRE_REM_CONG]);;

let WIRE_MAKEHINT_ADD = prove
 (`!g z x c. mldsa_makehint g z (x rem &8380417 + c) <=> mldsa_makehint g z (x + c)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLDSA_MAKEHINT_CONG THEN
  REWRITE_TAC[WIRE_CONG_REFL; WIRE_REM_CONG]);;

let WIRE_NORM_RANGE = prove
 (`!k a (b:int). ~(&0 <= round_infnorm k a - b)
                 ==> !i j. i < k /\ j < 256 ==> abs(a i j) < b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `round_infnorm k a < b` MP_TAC THENL
   [ASM_INT_ARITH_TAC;
    REWRITE_TAC[ROUND_INFNORM_LT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Substitute free variables by name. wire_subst: the replacement has the    *)
(* more general type; wire_subst_opt: the variable may be absent.            *)

let wire_subst (subs:(string*term) list) tm =
  let fv = frees tm in
  let sub1 tm (nm,rep) =
    match filter (fun v -> fst(dest_var v) = nm) fv with
      [v] -> let tyi = type_match (type_of rep) (type_of v) [] in
             vsubst [inst tyi rep, v] tm
    | _ -> failwith ("wire_subst: " ^ nm) in
  rev_itlist (fun s t -> sub1 t s) subs tm;;

let wire_subst_opt (subs:(string*term) list) tm =
  itlist (fun (nm,rep) tm ->
    match filter (fun v -> fst(dest_var v) = nm) (frees tm) with
      [v] -> let tyi = type_match (type_of v) (type_of rep) [] in
             vsubst [rep, inst tyi v] (inst tyi tm)
    | _ -> tm) (rev subs) tm;;

(* The function variables of the chain (the "natural" values of the          *)
(* generated computation) and their definitions. For Sign_internal, mu is    *)
(* defined from sk and the message m.                                        *)

let wire_defs_core p =
  map (wire_tm p)
  ["sh1 = (\\(i:num). mldsa_poly (\\j. &@ETA@ - mldsa_field @C@ (mldsa_slice @S1OFF@ @S1LEN@ sk) (256 * i + j)))";
   "sh2 = (\\(i:num). mldsa_poly (\\j. &@ETA@ - mldsa_field @C@ (mldsa_slice @S2OFF@ @S2LEN@ sk) (256 * i + j)))";
   "th0 = (\\(i:num). mldsa_poly (\\j. &4096 - mldsa_field 13 (mldsa_slice @T0OFF@ @T0LEN@ sk) (256 * i + j)))";
   "rho2 = mldsa_h (APPEND (APPEND (mldsa_slice 32 32 sk) rnd) mu) 64";
   "ysamp = (\\(n:num) (i:num) (t:num). &@G1@ - mldsa_field @CY@ (mldsa_h (APPEND rho2 (bytelist_of_num 2 (@L@ * n + i))) @YB@) t)";
   "wn = (\\(n:num) (i:num) (k:num). coeff k (mldsa_ntt_inv (\\q. ntt_msum @L@ (\\j. mldsa_ntt (mldsa_expand_a (mldsa_slice 0 32 sk) i j) q * mldsa_ntt (mldsa_poly (ysamp n j)) q) rem &8380417)))";
   "ctn = (\\(n:num). mldsa_h (APPEND mu (mldsa_encode @W1C@ @K256@ (\\m. mldsa_highbits @G2@ (wn n (m DIV 256) (m MOD 256))))) @CTL@)";
   "cb = (\\(n:num). mldsa_ball_coeffs @TAU@ (shake256 (ctn n)) @TAU@)";
   "cs1n = (\\(n:num) (i:num) (k:num). coeff k (mldsa_ntt_inv (\\q. (mldsa_ntt (mldsa_poly (cb n)) q * mldsa_ntt (sh1 i) q) rem &8380417)))";
   "cs2n = (\\(n:num) (i:num) (k:num). coeff k (mldsa_ntt_inv (\\q. (mldsa_ntt (mldsa_poly (cb n)) q * mldsa_ntt (sh2 i) q) rem &8380417)))";
   "ct0n = (\\(n:num) (i:num) (k:num). coeff k (mldsa_ntt_inv (\\q. (mldsa_ntt (mldsa_poly (cb n)) q * mldsa_ntt (th0 i) q) rem &8380417)))"];;

let wire_mu_def p = wire_tm p "mu = mldsa_h (APPEND (mldsa_slice 64 64 (sk:byte list)) (m:byte list)) 64";;

let wire_defs p fam =
  (if fam = "internal" then [wire_mu_def p] else []) @ wire_defs_core p;;

let wire_nat_names fam =
  (if fam = "internal" then ["mu"] else []) @
  ["sh1";"sh2";"th0";"rho2";"ysamp";"wn";"ctn";"cb";"cs1n";"cs2n";"ct0n"];;

let wire_nat_names_core = ["sh1";"sh2";"th0";"rho2";"ysamp";"wn";"ctn";"cb";"cs1n";"cs2n";"ct0n"];;

(* The witnesses for the variables of the abstract loop lemmas.              *)

let wire_witness_strs =
 ["rho","mldsa_slice 0 32 sk";
  "K","mldsa_slice 32 32 sk";
  "tr","mldsa_slice 64 64 sk";
  "s1","lift_vec (\\i. lift_intpoly (\\j. &@ETA@ - mldsa_field @C@ (mldsa_slice @S1OFF@ @S1LEN@ sk) (256 * i + j)))";
  "s2","lift_vec (\\i. lift_intpoly (\\j. &@ETA@ - mldsa_field @C@ (mldsa_slice @S2OFF@ @S2LEN@ sk) (256 * i + j)))";
  "t0","lift_vec (\\i. lift_intpoly (\\j. &4096 - mldsa_field 13 (mldsa_slice @T0OFF@ @T0LEN@ sk) (256 * i + j)))";
  "S1","lift_vec (\\i. lift_poly (mldsa_ntt (sh1 i)))";
  "S2","lift_vec (\\i. lift_poly (mldsa_ntt (sh2 i)))";
  "T0","lift_vec (\\i. lift_poly (mldsa_ntt (th0 i)))";
  "A","Common_Mat (lift_mat (\\i j. lift_poly (mldsa_ntt (mldsa_expand_a (mldsa_slice 0 32 sk) i j))))";
  "Y","\\n. lift_vec (\\i. lift_intpoly (ysamp n i))";
  "Yq","\\n. lift_vec (\\i. lift_poly (ysamp n i))";
  "Yh","\\n. lift_vec (\\i. lift_poly (mldsa_ntt (mldsa_poly (ysamp n i))))";
  "Wh","\\n. lift_vec (\\i. lift_poly (\\q. ntt_msum @L@ (\\j. mldsa_ntt (mldsa_expand_a (mldsa_slice 0 32 sk) i j) q * mldsa_ntt (mldsa_poly (ysamp n j)) q)))";
  "W","\\n. lift_vec (\\i. lift_poly (wn n i))";
  "W1","\\n. lift_vec (\\i. lift_intpoly (\\j. mldsa_highbits @G2@ (wn n i j)))";
  "W1E","\\n. mldsa_encode @W1C@ @K256@ (\\m. mldsa_highbits @G2@ (wn n (m DIV 256) (m MOD 256)))";
  "CT","ctn";
  "C","\\n. lift_intpoly (cb n)";
  "Cq","\\n. lift_poly (cb n)";
  "Ch","\\n. lift_poly (mldsa_ntt (mldsa_poly (cb n)))";
  "CS1h","\\n. lift_vec (\\i. lift_poly (\\k. mldsa_ntt (mldsa_poly (cb n)) k * mldsa_ntt (sh1 i) k))";
  "CS1","\\n. lift_vec (\\i. lift_poly (cs1n n i))";
  "CS2h","\\n. lift_vec (\\i. lift_poly (\\k. mldsa_ntt (mldsa_poly (cb n)) k * mldsa_ntt (sh2 i) k))";
  "CS2","\\n. lift_vec (\\i. lift_poly (cs2n n i))";
  "CT0h","\\n. lift_vec (\\i. lift_poly (\\k. mldsa_ntt (mldsa_poly (cb n)) k * mldsa_ntt (th0 i) k))";
  "CT0","\\n. lift_vec (\\i. lift_poly (ct0n n i))";
  "NCT0","\\n. lift_vec (\\i. lift_poly (\\k. --(ct0n n i k)))";
  "RC","\\n. lift_vec (\\i. lift_poly (\\k. (wn n i k - cs2n n i k) + ct0n n i k))";
  "Z","\\n. lift_vec (\\i. lift_poly (\\k. ysamp n i k + cs1n n i k))";
  "R","\\n. lift_vec (\\i. lift_poly (\\k. wn n i k - cs2n n i k))";
  "R0","\\n. lift_vec (\\i. lift_intpoly (\\j. mldsa_lowbits @G2@ (wn n i j - cs2n n i j)))";
  "NZ","\\n. round_infnorm @L@ (\\i j. mldsa_modpm (ysamp n i j + cs1n n i j) 8380417)";
  "NR","\\n. round_infnorm @K@ (\\i j. mldsa_lowbits @G2@ (wn n i j - cs2n n i j))";
  "NCT","\\n. round_infnorm @K@ (\\i j. mldsa_modpm (ct0n n i j) 8380417)";
  "HV","\\n. lift_vec (\\i. lift_bitpoly (\\j. mldsa_makehint @G2@ (--(ct0n n i j)) ((wn n i j - cs2n n i j) + ct0n n i j)))";
  "CNT","\\n. (&(mldsa_hint_count (\\p. mldsa_makehint @G2@ (--(ct0n n (p DIV 256) (p MOD 256))) ((wn n (p DIV 256) (p MOD 256) - cs2n n (p DIV 256) (p MOD 256)) + ct0n n (p DIV 256) (p MOD 256))) @K256@):int)";
  "ZC","\\n. lift_vec (\\i. lift_intpoly (\\j. mldsa_modpm (ysamp n i j + cs1n n i j) 8380417))";
  "SIG","\\n. APPEND (ctn n) (APPEND (mldsa_encode @CY@ @L256@ (\\m. &@G1@ - mldsa_modpm (ysamp n (m DIV 256) (m MOD 256) + cs1n n (m DIV 256) (m MOD 256)) 8380417)) (mldsa_hintbitpack @K@ @OM@ (\\p. mldsa_makehint @G2@ (--(ct0n n (p DIV 256) (p MOD 256))) ((wn n (p DIV 256) (p MOD 256) - cs2n n (p DIV 256) (p MOD 256)) + ct0n n (p DIV 256) (p MOD 256)))))";
  "acc","\\n. ~(mldsa_sign_attempt (@K@,@L@,@ETA@,@TAU@,@LAM@,@G1@,@G2@,@OM@) (mldsa_expand_a (mldsa_slice 0 32 sk)) sh1 sh2 th0 mu rho2 (@L@ * n) = NONE)"];;

let wire_witnesses p fam =
  map (fun (n,s) -> (n, wire_tm p s)) wire_witness_strs @
  (if fam = "internal" then
     [("TRB", wire_tm p "bits_of_bytes (mldsa_slice 64 64 (sk:byte list))");
      ("M", wire_tm p "bits_of_bytes (m:byte list)")]
   else []);;

let wire_loop_thm p fam =
  match fam,p with
    "mu","44" -> WIRE_SIGN_LOOP_44 | "mu","65" -> WIRE_SIGN_LOOP_65
  | "mu","87" -> WIRE_SIGN_LOOP_87 | "internal","44" -> WIRE_SIGNI_LOOP_44
  | "internal","65" -> WIRE_SIGNI_LOOP_65 | "internal","87" -> WIRE_SIGNI_LOOP_87
  | _ -> failwith "wire_loop_thm";;

(* The conjunction of the instantiated hypotheses of the loop lemma, with    *)
(* the natural function variables left as variables.                         *)

let wire_chain_hyps p fam =
  let hy = wire_subst (wire_witnesses p fam) (wire_loop_hyps p fam) in
  rhs(concl(DEPTH_CONV BETA_CONV hy));;

let wire_find_vars names tm =
  let fv = frees tm in
  map (fun nm -> hd(filter (fun v -> fst(dest_var v) = nm) fv)) names;;

let wire_chain_stmt p fam =
  let hy = wire_chain_hyps p fam in
  let defs = wire_defs p fam in
  let ants = mk_conj(wire_tm p "xof_ok /\\ LENGTH (sk:byte list) = @SK@", list_mk_conj defs) in
  let tm = mk_imp(ants,hy) in
  let first = if fam = "internal" then ["sk";"m";"rnd"] else ["sk";"mu";"rnd"] in
  let vars = wire_find_vars (first @ wire_nat_names fam) tm in
  list_mk_forall(vars,tm);;

(* The hand-written values of the bridge.                                    *)

let wire_hdefs p =
  map (wire_tm p)
  ["yh = (\\(n:num) (i:num). mldsa_expand_mask @G1@ rho2 (@L@ * n) i)";
   "wh = (\\(n:num) (i:num). mldsa_dot @L@ (mldsa_expand_a (mldsa_slice 0 32 sk) i) (yh n))";
   "w1h = (\\(n:num) (m:num). mldsa_highbits @G2@ (coeff (m MOD 256) (wh n (m DIV 256))))";
   "cth = (\\(n:num). mldsa_h (APPEND mu (mldsa_encode (mldsa_bitlen (8380416 DIV (2 * @G2@) - 1)) (256 * @K@) (w1h n))) (@LAM@ DIV 4))";
   "ch = (\\(n:num). mldsa_sample_in_ball @TAU@ (cth n))";
   "zh = (\\(n:num) (i:num). ring_add mldsa_rq (yh n i) (ring_mul mldsa_rq (ch n) (sh1 i)))";
   "rh = (\\(n:num) (i:num). ring_sub mldsa_rq (wh n i) (ring_mul mldsa_rq (ch n) (sh2 i)))";
   "ct0h = (\\(n:num) (i:num). ring_mul mldsa_rq (ch n) (th0 i))";
   "hhh = (\\(n:num) (p:num). p < 256 * @K@ /\\ mldsa_makehint @G2@ (--(coeff (p MOD 256) (ct0h n (p DIV 256)))) (coeff (p MOD 256) (ring_add mldsa_rq (rh n (p DIV 256)) (ct0h n (p DIV 256)))))";
   "hgh = (\\(n:num) (p:num). mldsa_makehint @G2@ (--(coeff (p MOD 256) (ct0h n (p DIV 256)))) (coeff (p MOD 256) (rh n (p DIV 256)) + coeff (p MOD 256) (ct0h n (p DIV 256))))"];;

let wire_att_str = "mldsa_sign_attempt (@K@,@L@,@ETA@,@TAU@,@LAM@,@G1@,@G2@,@OM@) (mldsa_expand_a (mldsa_slice 0 32 sk)) sh1 sh2 th0 mu rho2 (@L@ * n)";;

let wire_br_stmt p fam =
  let hy = wire_chain_hyps p fam in
  let cs = conjuncts hy in
  let nc = length cs in
  let sigbody = let s = assoc "SIG" wire_witness_strs in String.sub s 4 (String.length s - 4) in
  let third = wire_tm p ("!n. ~(" ^ wire_att_str ^ " = NONE) ==> " ^ wire_att_str ^ " = SOME (" ^ sigbody ^ ")") in
  let last3 = list_mk_conj [el (nc-2) cs; el (nc-1) cs; third] in
  let defs = wire_defs_core p @ wire_hdefs p in
  let tm = mk_imp(list_mk_conj defs,last3) in
  let names = ["sk";"mu";"rnd"] @ wire_nat_names_core @ ["yh";"wh";"w1h";"cth";"ch";"zh";"rh";"ct0h";"hhh";"hgh"] in
  list_mk_forall(wire_find_vars names tm,tm);;

let wire_hand_terms p =
  let env = ref [] in
  List.iter (fun d ->
    let r' = wire_subst_opt !env (rhs d) in
    env := !env @ [(fst(dest_var(lhs d)), r')]) (wire_hdefs p);
  !env;;

(* Natural function variables replaced by their definitions.                 *)

let wire_nat_env p fam =
  let env = ref [] in
  List.iter (fun d ->
    env := !env @ [(fst(dest_var(lhs d)), wire_subst_opt !env (rhs d))]) (wire_defs p fam);
  !env;;

let wire_loop_inst p fam =
  let nat = wire_nat_env p fam in
  let ws = map (fun (n,t) -> (n, wire_subst_opt nat t)) (wire_witnesses p fam) @
           [("rho2", assoc "rho2" nat)] @ (if fam = "internal" then [("mu", assoc "mu" nat)] else []) in
  let hyps = wire_loop_hyps p fam in
  let fv = frees hyps in
  let pairs = map (fun (nm,rep) ->
    let v = hd(filter (fun v -> fst(dest_var v) = nm) fv) in
    let tyi = type_match (type_of rep) (type_of v) [] in
    (inst tyi rep, v)) ws in
  BETA_RULE (INST pairs (wire_loop_thm p fam));;

let wire_inst_chain p fam chain =
  let nat = wire_nat_env p fam in
  let natvals = map (fun nm -> assoc nm nat) (wire_nat_names fam) in
  let first = if fam = "internal" then [`sk:byte list`;`m:byte list`;`rnd:byte list`]
              else [`sk:byte list`;`mu:byte list`;`rnd:byte list`] in
  SPECL (first @ natvals) chain;;

let wire_inst_br p fam br =
  let nat = wire_nat_env p fam in
  let natvals = map (fun nm -> assoc nm nat) wire_nat_names_core in
  let hand = map (fun (nm,t) -> wire_subst_opt nat t) (wire_hand_terms p) in
  let muv = if fam = "internal" then assoc "mu" nat else `mu:byte list` in
  SPECL ([`sk:byte list`; muv; `rnd:byte list`] @ natvals @ hand) br;;
(* ------------------------------------------------------------------------- *)
(* Component lemmas per parameter set and family.                            *)
(* ------------------------------------------------------------------------- *)

let WIRE_HIGHBITS_95232 = prove
 (`!r. &0 <= mldsa_highbits 95232 r /\ mldsa_highbits 95232 r <= &43`,
  GEN_TAC THEN MP_TAC(SPECL [`95232`; `r:int`] MLDSA_DECOMPOSE_VALID) THEN
  REWRITE_TAC[MLDSA_GAMMA2_CLAUSES] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_INT_ARITH_TAC);;

let WIRE_HIGHBITS_261888 = prove
 (`!r. &0 <= mldsa_highbits 261888 r /\ mldsa_highbits 261888 r <= &15`,
  GEN_TAC THEN MP_TAC(SPECL [`261888`; `r:int`] MLDSA_DECOMPOSE_VALID) THEN
  REWRITE_TAC[MLDSA_GAMMA2_CLAUSES] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_INT_ARITH_TAC);;

let wire_call_ntt = CONJ EQ_INTPOLYTORQ EQ_NTT;;

let wire_tab p fam =
  let sel a b = if fam = "mu" then a else b in
  match p with
    "44" ->
     ["skdec",EQ_SKDECODE_MLDSA44;
      "c5s1",MP (sel EQ_SIGN_INTERNAL_MU_CALLABLE_5_0_MLDSA44 EQ_SIGN_INTERNAL_CALLABLE_5_0_MLDSA44) wire_call_ntt;
      "c5",MP (sel EQ_SIGN_INTERNAL_MU_CALLABLE_5_0_MLDSA44 EQ_SIGN_INTERNAL_CALLABLE_5_0_MLDSA44) wire_call_ntt;
      "c4",sel EQ_SIGN_INTERNAL_MU_CALLABLE_4_0_MLDSA44 EQ_SIGN_INTERNAL_CALLABLE_4_0_MLDSA44;
      "c2",sel EQ_SIGN_INTERNAL_MU_CALLABLE_2_0_MLDSA44 EQ_SIGN_INTERNAL_CALLABLE_2_0_MLDSA44;
      "c1",sel EQ_SIGN_INTERNAL_MU_CALLABLE_1_0_MLDSA44 EQ_SIGN_INTERNAL_CALLABLE_1_0_MLDSA44;
      "c3",sel EQ_SIGN_INTERNAL_MU_CALLABLE_3_0_MLDSA44 EQ_SIGN_INTERNAL_CALLABLE_3_0_MLDSA44;
      "nct",sel EQ_SIGN_INTERNAL_MU_CALLABLE_3_0_MLDSA44 EQ_SIGN_INTERNAL_CALLABLE_3_0_MLDSA44;
      "fin",sel EQ_SIGN_INTERNAL_MU_CALLABLE_0_0_FINAL_MLDSA44 EQ_SIGN_INTERNAL_CALLABLE_0_0_FINAL_MLDSA44;
      "expmask",EQ_EXPANDMASK_MLDSA44; "i2rq",EQ_INTVECTORTORQ_4_BODY; "vntt",EQ_VECTORNTT_4_MLDSA44;
      "matvec",EQ_MATRIXVECTORNTT_4_4_MLDSA44; "vinvK",EQ_VECTORNTTINV_4_MLDSA44;
      "vinvL",EQ_VECTORNTTINV_4_MLDSA44; "hib",EQ_FIXEDVECTORHIGHBITS_4_MLDSA44;
      "lowb",EQ_FIXEDVECTORLOWBITS_4_MLDSA44; "mkh",EQ_FIXEDVECTORMAKEHINT_4_MLDSA44;
      "w1enc",EQ_W1ENCODE_MLDSA44; "sib",EQ_SAMPLEINBALL_MLDSA44;
      "svL",EQ_SCALARVECTORNTT_4_MLDSA44; "svK",EQ_SCALARVECTORNTT_4_MLDSA44;
      "radL",EQ_RQVECTORADD_4; "radK",EQ_RQVECTORADD_4; "sub",EQ_FIXEDVECTORSUBTRACT_4_TIME;
      "ivin",EQ_INTVECTORINFNORM_4; "neg",EQ_RQVECTORNEGATE_4; "hirange",WIRE_HIGHBITS_95232]
  | "65" ->
     ["skdec",EQ_SKDECODE_MLDSA65;
      "c5s1",MP (sel EQ_SIGN_INTERNAL_MU_CALLABLE_6_0_MLDSA65 EQ_SIGN_INTERNAL_CALLABLE_6_0_MLDSA65) wire_call_ntt;
      "c5",MP (sel EQ_SIGN_INTERNAL_MU_CALLABLE_5_0_MLDSA65 EQ_SIGN_INTERNAL_CALLABLE_5_0_MLDSA65) wire_call_ntt;
      "c4",sel EQ_SIGN_INTERNAL_MU_CALLABLE_4_0_MLDSA65 EQ_SIGN_INTERNAL_CALLABLE_4_0_MLDSA65;
      "c2",sel EQ_SIGN_INTERNAL_MU_CALLABLE_2_0_MLDSA65 EQ_SIGN_INTERNAL_CALLABLE_2_0_MLDSA65;
      "c1",sel EQ_SIGN_INTERNAL_MU_CALLABLE_1_0_MLDSA65 EQ_SIGN_INTERNAL_CALLABLE_1_0_MLDSA65;
      "c3",sel EQ_SIGN_INTERNAL_MU_CALLABLE_3_0_MLDSA65 EQ_SIGN_INTERNAL_CALLABLE_3_0_MLDSA65;
      "nct",EQ_RQVECTORINFNORM_6;
      "fin",sel EQ_SIGN_INTERNAL_MU_CALLABLE_0_0_FINAL_MLDSA65 EQ_SIGN_INTERNAL_CALLABLE_0_0_FINAL_MLDSA65;
      "expmask",EQ_EXPANDMASK_MLDSA65; "i2rq",EQ_INTVECTORTORQ_5_BODY; "vntt",EQ_VECTORNTT_5_MLDSA65;
      "matvec",EQ_MATRIXVECTORNTT_6_5_MLDSA65; "vinvK",EQ_VECTORNTTINV_6_MLDSA65;
      "vinvL",EQ_VECTORNTTINV_5_MLDSA65; "hib",EQ_FIXEDVECTORHIGHBITS_6_MLDSA65;
      "lowb",EQ_FIXEDVECTORLOWBITS_6_MLDSA65; "mkh",EQ_FIXEDVECTORMAKEHINT_6_MLDSA65;
      "w1enc",EQ_W1ENCODE_MLDSA65; "sib",EQ_SAMPLEINBALL_MLDSA65;
      "svL",EQ_SCALARVECTORNTT_5_MLDSA65; "svK",EQ_SCALARVECTORNTT_6_MLDSA65;
      "radL",EQ_RQVECTORADD_5; "radK",EQ_RQVECTORADD_6; "sub",EQ_FIXEDVECTORSUBTRACT_6_TIME;
      "ivin",EQ_INTVECTORINFNORM_6; "neg",EQ_RQVECTORNEGATE_6; "hirange",WIRE_HIGHBITS_261888]
  | "87" ->
     ["skdec",EQ_SKDECODE_MLDSA87;
      "c5s1",MP (sel EQ_SIGN_INTERNAL_MU_CALLABLE_6_0_MLDSA87 EQ_SIGN_INTERNAL_CALLABLE_6_0_MLDSA87) wire_call_ntt;
      "c5",MP (sel EQ_SIGN_INTERNAL_MU_CALLABLE_5_0_MLDSA87 EQ_SIGN_INTERNAL_CALLABLE_5_0_MLDSA87) wire_call_ntt;
      "c4",sel EQ_SIGN_INTERNAL_MU_CALLABLE_4_0_MLDSA87 EQ_SIGN_INTERNAL_CALLABLE_4_0_MLDSA87;
      "c2",sel EQ_SIGN_INTERNAL_MU_CALLABLE_2_0_MLDSA87 EQ_SIGN_INTERNAL_CALLABLE_2_0_MLDSA87;
      "c1",sel EQ_SIGN_INTERNAL_MU_CALLABLE_1_0_MLDSA87 EQ_SIGN_INTERNAL_CALLABLE_1_0_MLDSA87;
      "c3",sel EQ_SIGN_INTERNAL_MU_CALLABLE_3_0_MLDSA87 EQ_SIGN_INTERNAL_CALLABLE_3_0_MLDSA87;
      "nct",EQ_RQVECTORINFNORM_8;
      "fin",sel EQ_SIGN_INTERNAL_MU_CALLABLE_0_0_FINAL_MLDSA87 EQ_SIGN_INTERNAL_CALLABLE_0_0_FINAL_MLDSA87;
      "expmask",EQ_EXPANDMASK_MLDSA87; "i2rq",EQ_INTVECTORTORQ_7_BODY; "vntt",EQ_VECTORNTT_7_MLDSA87;
      "matvec",EQ_MATRIXVECTORNTT_8_7_MLDSA87; "vinvK",EQ_VECTORNTTINV_8_MLDSA87;
      "vinvL",EQ_VECTORNTTINV_7_MLDSA87; "hib",EQ_FIXEDVECTORHIGHBITS_8_MLDSA87;
      "lowb",EQ_FIXEDVECTORLOWBITS_8_MLDSA87; "mkh",EQ_FIXEDVECTORMAKEHINT_8_MLDSA87;
      "w1enc",EQ_W1ENCODE_MLDSA87; "sib",EQ_SAMPLEINBALL_MLDSA87;
      "svL",EQ_SCALARVECTORNTT_7_MLDSA87; "svK",EQ_SCALARVECTORNTT_8_MLDSA87;
      "radL",EQ_RQVECTORADD_7; "radK",EQ_RQVECTORADD_8; "sub",EQ_FIXEDVECTORSUBTRACT_8_TIME;
      "ivin",EQ_INTVECTORINFNORM_8; "neg",EQ_RQVECTORNEGATE_8; "hirange",WIRE_HIGHBITS_261888]
  | _ -> failwith "wire_tab";;
(* ------------------------------------------------------------------------- *)
(* The chain lemma: every hypothesis of the abstract loop lemma, for the     *)
(* natural values, from the component lemmas.                                *)
(* ------------------------------------------------------------------------- *)

let wire_rwv nm =
  FIRST_ASSUM(fun th ->
    try if fst(dest_var(lhs(concl th))) = nm then REWRITE_TAC[th] else NO_TAC
    with Failure _ -> NO_TAC);;

let wire_ants_tac = REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC];;

let WIRE_MH_ASSOC = prove
 (`!k r m n. mldsa_h (APPEND k (APPEND r m)) n = mldsa_h (APPEND (APPEND k r) m) n`,
  REWRITE_TAC[APPEND_ASSOC]);;

let WIRE_MOD256_LT = ARITH_RULE `!n. n MOD 256 < 256`;;

(* Applying the bridge to the last goals of the chain.                       *)

let wire_br_tac p br = fun (asl,w) ->
  let allv = itlist (fun t acc -> union (frees t) acc) (w::map (concl o snd) asl) [] in
  let find nm = hd(filter (fun v -> fst(dest_var v) = nm) allv) in
  let nat = map find (["sk";"mu";"rnd"] @ wire_nat_names_core) in
  let hand = map snd (wire_hand_terms p) in
  let th = SPECL (nat @ hand) br in
  let ants = lhand (concl th) in
  (SUBGOAL_THEN ants (fun a -> MP_TAC (MP th a)) THENL
    [wire_ants_tac;
     DISCH_THEN(fun th -> let [a;b;c] = CONJUNCTS th in FIRST [ACCEPT_TAC a; ACCEPT_TAC b])]) (asl,w);;

(* NTT-inverse of the pointwise products: VectorNTTInv of a lifted vector    *)
(* of arrays reduced mod q.                                                  *)

let wire_nttinv_tac p thm nm hat =
  GEN_TAC THEN wire_rwv nm THEN
  MP_TAC(SPEC (parse_term ("\\(i:num) q. (mldsa_ntt (mldsa_poly (cb (n:num))) q * mldsa_ntt (" ^ hat ^ " i) q) rem &8380417")) thm) THEN
  REWRITE_TAC[NTT_REM_RANGE; NTT_LIFT_POLY_REM];;

let wire_chain_tacs p fam br =
  let tab = wire_tab p fam in
  let g s = assoc s tab in
  let tm s = wire_tm p s in
  let gen th = GEN_TAC THEN REWRITE_TAC[th] in
  [(* skDecode and lengths *)
   MATCH_MP_TAC (g "skdec") THEN FIRST_ASSUM ACCEPT_TAC;
   REWRITE_TAC[LENGTH_MLDSA_SLICE];
   REWRITE_TAC[LENGTH_MLDSA_SLICE];
   REWRITE_TAC[LENGTH_MLDSA_SLICE]] @
  (if fam = "internal" then
     [REWRITE_TAC[ENC_BYTES_TO_BITS_STRING];
      wire_rwv "mu" THEN REWRITE_TAC[GSYM BITS_OF_BYTES_APPEND] THEN ASM_SIMP_TAC[EQ_H_HOL]]
   else []) @
  [(* NTT of s1, s2, t0; ExpandA *)
   wire_rwv "sh1" THEN REWRITE_TAC[g "c5s1"];
   wire_rwv "sh2" THEN REWRITE_TAC[g "c5"];
   wire_rwv "th0" THEN REWRITE_TAC[g "c5"];
   MATCH_MP_TAC (SPEC `mldsa_slice 0 32 sk` (g "c4")) THEN ASM_REWRITE_TAC[LENGTH_MLDSA_SLICE];
   (* rho'' *)
   wire_rwv "rho2" THEN ASM_SIMP_TAC[BALL_HBYTESSTRING];
   FIRST_ASSUM ACCEPT_TAC;
   (* y, w, w1, c~ *)
   GEN_TAC THEN wire_rwv "ysamp" THEN ASM_SIMP_TAC[g "expmask"];
   gen (g "i2rq");
   gen (g "vntt");
   gen (g "matvec");
   GEN_TAC THEN wire_rwv "wn" THEN
   MP_TAC(SPEC (tm "\\(i:num) q. ntt_msum @L@ (\\j. mldsa_ntt (mldsa_expand_a (mldsa_slice 0 32 sk) i j) q * mldsa_ntt (mldsa_poly (ysamp (n:num) j)) q) rem &8380417") (g "vinvK")) THEN
   REWRITE_TAC[NTT_REM_RANGE; NTT_LIFT_POLY_REM];
   gen (g "hib");
   GEN_TAC THEN MP_TAC(SPEC (tm "\\(i:num) (j:num). mldsa_highbits @G2@ (wn (n:num) i j)") (g "w1enc")) THEN
     REWRITE_TAC[g "hirange"] THEN CONV_TAC NUM_REDUCE_CONV;
   GEN_TAC THEN wire_rwv "ctn" THEN ASM_SIMP_TAC[BALL_HBYTESSTRING];
   (* c *)
   GEN_TAC THEN wire_rwv "cb" THEN
   MP_TAC(SPEC `(ctn:num->byte list) (n:num)` (g "sib")) THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; wire_rwv "ctn" THEN REWRITE_TAC[BALL_LENGTH_MLDSA_H] THEN ARITH_TAC];
     DISCH_THEN ACCEPT_TAC];
   gen EQ_INTPOLYTORQ;
   gen EQ_NTT;
   (* cs1, cs2 *)
   gen (g "svL");
   wire_nttinv_tac p (g "vinvL") "cs1n" "sh1";
   gen (g "svK");
   wire_nttinv_tac p (g "vinvK") "cs2n" "sh2";
   (* z, r, r0 *)
   gen (g "radL");
   gen (g "sub");
   gen (g "lowb");
   gen (g "c3");
   gen (g "ivin");
   (* ct0 and the hints *)
   gen (g "svK");
   wire_nttinv_tac p (g "vinvK") "ct0n" "th0";
   gen (g "neg");
   gen (g "radK");
   gen (g "mkh");
   gen (g "nct");
   gen (g "c2");
   gen (g "c1");
   (* the signature and the acceptance test: from the bridge *)
   wire_br_tac p br; wire_br_tac p br];;

let wire_chain_prove p fam br =
  prove(wire_chain_stmt p fam,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `LENGTH (rho2:byte list) = 64` ASSUME_TAC THENL
     [wire_rwv "rho2" THEN REWRITE_TAC[BALL_LENGTH_MLDSA_H]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL (wire_chain_tacs p fam br));;
(* ------------------------------------------------------------------------- *)
(* The bridge: the acceptance test of the generated loop on the natural      *)
(* values is the acceptance of the handwritten attempt, and then the         *)
(* handwritten attempt returns the signature that sigEncode computes.        *)
(* ------------------------------------------------------------------------- *)

let wire_br_prove p fam =
  let br = wire_br_stmt p fam in
  let tab = wire_tab p fam in
  let g s = assoc s tab in
  let tm s = wire_tm p s in
  let br_goal = snd(dest_imp(snd(strip_forall br))) in
  let br_conjs = conjuncts br_goal in
  let acc_stmt = el 1 br_conjs and third_stmt = el 2 br_conjs in
  let att_th = SPECL (map (fun s -> parse_term (top_subst (wire_params p) s))
    ["@K@"; "@L@"; "@ETA@"; "@TAU@"; "@LAM@"; "@G1@"; "@G2@"; "@OM@";
     "mldsa_expand_a (mldsa_slice 0 32 sk)"; "sh1:num->(1->num)->int"; "sh2:num->(1->num)->int"; "th0:num->(1->num)->int";
     "mu:byte list"; "rho2:byte list"; "@L@ * n";
     "(yh:num->num->(1->num)->int) n"; "(wh:num->num->(1->num)->int) n"; "(w1h:num->num->int) n";
     "(cth:num->byte list) n"; "(ch:num->(1->num)->int) n"; "(zh:num->num->(1->num)->int) n";
     "(rh:num->num->(1->num)->int) n"; "(ct0h:num->num->(1->num)->int) n";
     "(hhh:num->num->bool) n"; "(hgh:num->num->bool) n"]) WIRE_ATT in
  let att_stmt = mk_forall(`n:num`, snd(dest_imp(concl att_th))) in
  let f5_tac nm lab =
    SUBGOAL_THEN (parse_term ("!n i k. coeff k (ring_mul mldsa_rq ((ch:num->(1->num)->int) n) ((" ^ lab ^ ":num->(1->num)->int) i)) = (" ^ nm ^ ":num->num->num->int) n i k")) (LABEL_TAC ("F5" ^ nm)) THENL
     [REPEAT GEN_TAC THEN wire_rwv nm THEN
      MP_TAC(SPECL [parse_term "(ch:num->(1->num)->int) n"; parse_term ("(" ^ lab ^ ":num->(1->num)->int) i")] WIRE_NTT_MUL) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [USE_THEN "F4" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[MLDSA_POLY_IN_RQ];
          FIRST_ASSUM MATCH_ACCEPT_TAC];
        DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN USE_THEN "F4" (fun th -> REWRITE_TAC[th])];
      ALL_TAC] in
  prove(br,
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `!i. (sh1:num->(1->num)->int) i IN ring_carrier mldsa_rq` (LABEL_TAC "sh1rq") THENL [GEN_TAC THEN wire_rwv "sh1" THEN REWRITE_TAC[MLDSA_POLY_IN_RQ]; ALL_TAC] THEN
   SUBGOAL_THEN `!i. (sh2:num->(1->num)->int) i IN ring_carrier mldsa_rq` (LABEL_TAC "sh2rq") THENL [GEN_TAC THEN wire_rwv "sh2" THEN REWRITE_TAC[MLDSA_POLY_IN_RQ]; ALL_TAC] THEN
   SUBGOAL_THEN `!i. (th0:num->(1->num)->int) i IN ring_carrier mldsa_rq` (LABEL_TAC "th0rq") THENL [GEN_TAC THEN wire_rwv "th0" THEN REWRITE_TAC[MLDSA_POLY_IN_RQ]; ALL_TAC] THEN
   (* y *)
   SUBGOAL_THEN `!n i. (yh:num->num->(1->num)->int) n i = mldsa_poly (ysamp n i)` (LABEL_TAC "F1") THENL
    [REPEAT GEN_TAC THEN MAP_EVERY wire_rwv ["yh";"ysamp"] THEN REWRITE_TAC[mldsa_expand_mask] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
     REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[];
     ALL_TAC] THEN
   (* w *)
   SUBGOAL_THEN (tm "!n i. (wh:num->num->(1->num)->int) n i = mldsa_ntt_inv (\\q. ntt_msum @L@ (\\j. mldsa_ntt (mldsa_expand_a (mldsa_slice 0 32 sk) i j) q * mldsa_ntt (mldsa_poly (ysamp n j)) q) rem &8380417)") (LABEL_TAC "F2") THENL
    [REPEAT GEN_TAC THEN wire_rwv "wh" THEN
     SUBGOAL_THEN `(\j. mldsa_ntt_inv (mldsa_ntt (mldsa_expand_a (mldsa_slice 0 32 sk) i j))) = mldsa_expand_a (mldsa_slice 0 32 sk) i` (LABEL_TAC "EA") THENL
      [ONCE_REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN
       MATCH_MP_TAC MLDSA_NTT_INV_NTT THEN MATCH_MP_TAC WIRE_EXPAND_A_RQ THEN
       REWRITE_TAC[LENGTH_MLDSA_SLICE] THEN ARITH_TAC;
       ALL_TAC] THEN
     MP_TAC(SPECL [tm "@L@"; `\j. mldsa_ntt (mldsa_expand_a (mldsa_slice 0 32 sk) i j)`; `(yh:num->num->(1->num)->int) n`] NTT_DOT_ROW) THEN
     ANTS_TAC THENL
      [REWRITE_TAC[MLDSA_NTT_BOUND] THEN REPEAT STRIP_TAC THEN USE_THEN "F1" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[MLDSA_POLY_IN_RQ];
       USE_THEN "EA" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN SUBST1_TAC THEN USE_THEN "F1" (fun th -> REWRITE_TAC[th])];
     ALL_TAC] THEN
   SUBGOAL_THEN `!n i k. coeff k ((wh:num->num->(1->num)->int) n i) = wn n i k` (LABEL_TAC "F2c") THENL
    [REPEAT GEN_TAC THEN wire_rwv "wn" THEN USE_THEN "F2" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
   SUBGOAL_THEN `!n. (cth:num->byte list) n = ctn n` (LABEL_TAC "F3") THENL
    [GEN_TAC THEN MAP_EVERY wire_rwv ["cth";"ctn";"w1h"] THEN
     CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN
     CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN USE_THEN "F2c" (fun th -> REWRITE_TAC[th]);
     ALL_TAC] THEN
   SUBGOAL_THEN `!n. (ch:num->(1->num)->int) n = mldsa_poly (cb n)` (LABEL_TAC "F4") THENL
    [GEN_TAC THEN MAP_EVERY wire_rwv ["ch";"cb"] THEN REWRITE_TAC[mldsa_sample_in_ball] THEN USE_THEN "F3" (fun th -> REWRITE_TAC[th]);
     ALL_TAC] THEN
   f5_tac "cs1n" "sh1" THEN f5_tac "cs2n" "sh2" THEN f5_tac "ct0n" "th0" THEN
   (* the handwritten attempt *)
   SUBGOAL_THEN att_stmt (LABEL_TAC "ATT") THENL
    [X_GEN_TAC `n:num` THEN MP_TAC att_th THEN
     ANTS_TAC THENL
      [REPEAT CONJ_TAC THENL
        [CONV_TAC NUM_REDUCE_CONV; CONV_TAC NUM_REDUCE_CONV;
         GEN_TAC THEN DISCH_TAC THEN USE_THEN "sh1rq" MATCH_ACCEPT_TAC;
         GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL [USE_THEN "sh2rq" MATCH_ACCEPT_TAC; USE_THEN "th0rq" MATCH_ACCEPT_TAC];
         wire_rwv "yh" THEN REWRITE_TAC[];
         wire_rwv "wh" THEN REWRITE_TAC[];
         wire_rwv "w1h" THEN REWRITE_TAC[];
         wire_rwv "cth" THEN REWRITE_TAC[];
         wire_rwv "ch" THEN REWRITE_TAC[];
         wire_rwv "zh" THEN REWRITE_TAC[];
         wire_rwv "rh" THEN REWRITE_TAC[];
         wire_rwv "ct0h" THEN REWRITE_TAC[];
         wire_rwv "hhh" THEN REWRITE_TAC[];
         wire_rwv "hgh" THEN REWRITE_TAC[]];
       DISCH_THEN ACCEPT_TAC];
     ALL_TAC] THEN
   (* coefficient facts *)
   SUBGOAL_THEN `!n. (ch:num->(1->num)->int) n IN ring_carrier mldsa_rq` (LABEL_TAC "chrq") THENL
    [GEN_TAC THEN USE_THEN "F4" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[MLDSA_POLY_IN_RQ]; ALL_TAC] THEN
   SUBGOAL_THEN `!n i. (yh:num->num->(1->num)->int) n i IN ring_carrier mldsa_rq` (LABEL_TAC "yhrq") THENL
    [REPEAT GEN_TAC THEN USE_THEN "F1" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[MLDSA_POLY_IN_RQ]; ALL_TAC] THEN
   SUBGOAL_THEN (tm "!n i j. j < 256 ==> mldsa_modpm (coeff j ((zh:num->num->(1->num)->int) n i)) 8380417 = mldsa_modpm (ysamp n i j + cs1n n i j) 8380417") (LABEL_TAC "BZ") THENL
    [REPEAT STRIP_TAC THEN wire_rwv "zh" THEN
     MP_TAC(SPECL [`(yh:num->num->(1->num)->int) n i`; `ring_mul mldsa_rq ((ch:num->(1->num)->int) n) ((sh1:num->(1->num)->int) i)`; `j:num`] MLDSA_RQ_COEFF_ADD) THEN
     ANTS_TAC THENL
      [CONJ_TAC THENL [USE_THEN "yhrq" MATCH_ACCEPT_TAC; MATCH_MP_TAC RING_MUL THEN CONJ_TAC THENL [USE_THEN "chrq" MATCH_ACCEPT_TAC; USE_THEN "sh1rq" MATCH_ACCEPT_TAC]];
       DISCH_THEN SUBST1_TAC THEN USE_THEN "F1" (fun th -> REWRITE_TAC[th; COEFF_MLDSA_POLY]) THEN
       USE_THEN "F5cs1n" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[WIRE_MODPM_ADD]];
     ALL_TAC] THEN
   SUBGOAL_THEN (tm "!n i j. coeff j ((rh:num->num->(1->num)->int) n i) = (wn n i j - cs2n n i j) rem &8380417") (LABEL_TAC "BRc") THENL
    [REPEAT GEN_TAC THEN wire_rwv "rh" THEN
     MP_TAC(SPECL [`(wh:num->num->(1->num)->int) n i`; `ring_mul mldsa_rq ((ch:num->(1->num)->int) n) ((sh2:num->(1->num)->int) i)`; `j:num`] MLDSA_RQ_COEFF_SUB) THEN
     ANTS_TAC THENL
      [CONJ_TAC THENL
        [wire_rwv "wh" THEN REWRITE_TAC[MLDSA_DOT_IN_RQ];
         MATCH_MP_TAC RING_MUL THEN CONJ_TAC THENL [USE_THEN "chrq" MATCH_ACCEPT_TAC; USE_THEN "sh2rq" MATCH_ACCEPT_TAC]];
       DISCH_THEN SUBST1_TAC THEN USE_THEN "F2c" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "F5cs2n" (fun th -> REWRITE_TAC[th])];
     ALL_TAC] THEN
   SUBGOAL_THEN `!n i k. coeff k ((ct0h:num->num->(1->num)->int) n i) = ct0n n i k` (LABEL_TAC "BCt") THENL
    [REPEAT GEN_TAC THEN wire_rwv "ct0h" THEN USE_THEN "F5ct0n" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
   SUBGOAL_THEN (tm "!n. (hgh:num->num->bool) n = (\\p. mldsa_makehint @G2@ (--(ct0n n (p DIV 256) (p MOD 256))) (wn n (p DIV 256) (p MOD 256) - cs2n n (p DIV 256) (p MOD 256) + ct0n n (p DIV 256) (p MOD 256)))") (LABEL_TAC "BH") THENL
    [GEN_TAC THEN wire_rwv "hgh" THEN REWRITE_TAC[] THEN ABS_TAC THEN
     USE_THEN "BRc" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "BCt" (fun th -> REWRITE_TAC[th]) THEN
     REWRITE_TAC[WIRE_MAKEHINT_ADD];
     ALL_TAC] THEN
   SUBGOAL_THEN (tm "!n. round_infnorm @L@ (\\i j. mldsa_modpm (coeff j ((zh:num->num->(1->num)->int) n i)) 8380417) = round_infnorm @L@ (\\i j. mldsa_modpm (ysamp n i j + cs1n n i j) 8380417)") (LABEL_TAC "NZe") THENL
    [GEN_TAC THEN MATCH_MP_TAC ROUND_INFNORM_CONG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
     USE_THEN "BZ" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   SUBGOAL_THEN (tm "!n. round_infnorm @K@ (\\i j. mldsa_lowbits @G2@ (coeff j ((rh:num->num->(1->num)->int) n i))) = round_infnorm @K@ (\\i j. mldsa_lowbits @G2@ (wn n i j - cs2n n i j))") (LABEL_TAC "NRe") THENL
    [GEN_TAC THEN MATCH_MP_TAC ROUND_INFNORM_CONG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
     USE_THEN "BRc" (fun th -> REWRITE_TAC[th; MLDSA_LOWBITS_REM]); ALL_TAC] THEN
   SUBGOAL_THEN (tm "!n. round_infnorm @K@ (\\i j. mldsa_modpm (coeff j ((ct0h:num->num->(1->num)->int) n i)) 8380417) = round_infnorm @K@ (\\i j. mldsa_modpm (ct0n n i j) 8380417)") (LABEL_TAC "NCe") THENL
    [GEN_TAC THEN MATCH_MP_TAC ROUND_INFNORM_CONG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
     USE_THEN "BCt" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
   SUBGOAL_THEN (tm "!n m. mldsa_modpm (coeff (m MOD 256) ((zh:num->num->(1->num)->int) n (m DIV 256))) 8380417 = mldsa_modpm (ysamp n (m DIV 256) (m MOD 256) + cs1n n (m DIV 256) (m MOD 256)) 8380417") (LABEL_TAC "BZ2") THENL
    [REPEAT GEN_TAC THEN USE_THEN "BZ" MATCH_MP_TAC THEN MATCH_ACCEPT_TAC WIRE_MOD256_LT; ALL_TAC] THEN
   (* acceptance and the signature in terms of the natural values *)
   SUBGOAL_THEN acc_stmt (LABEL_TAC "ACC") THENL
    [GEN_TAC THEN USE_THEN "ATT" (MP_TAC o SPEC `n:num`) THEN
     USE_THEN "NZe" (fun a -> USE_THEN "NRe" (fun b -> USE_THEN "NCe" (fun c -> USE_THEN "BH" (fun d ->
       CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[a;b;c;d] THEN STRIP_TAC THEN
       FIRST_X_ASSUM(fun th -> if is_iff(concl th) then ACCEPT_TAC th else NO_TAC)))));
     ALL_TAC] THEN
   SUBGOAL_THEN third_stmt (LABEL_TAC "SIGN") THENL
    [GEN_TAC THEN USE_THEN "ATT" (MP_TAC o SPEC `n:num`) THEN
     USE_THEN "BZ2" (fun bz -> USE_THEN "BH" (fun d -> USE_THEN "F3" (fun f3 ->
       CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
       REWRITE_TAC[bz; d; f3] THEN STRIP_TAC THEN
       FIRST_X_ASSUM(fun th -> if is_imp(concl th) then ACCEPT_TAC th else NO_TAC))));
     ALL_TAC] THEN
   REPEAT CONJ_TAC THENL
    [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
     USE_THEN "ACC" (fun acc ->
       let attn = tm "mldsa_sign_attempt (@K@,@L@,@ETA@,@TAU@,@LAM@,@G1@,@G2@,@OM@) (mldsa_expand_a (mldsa_slice 0 32 sk)) sh1 sh2 th0 mu rho2 (@L@ * (n:num)) = NONE" in
       let f = REWRITE_RULE[DE_MORGAN_THM; WIRE_CNT_LEM; NOT_CLAUSES] (EQ_MP (SPEC `n:num` acc) (ASSUME (mk_neg attn))) in
       let [f1;f2;f3;f4] = CONJUNCTS f in
       let rng = MP (SPECL [tm "@L@"; tm "\\(i:num) (j:num). mldsa_modpm (ysamp (n:num) i j + cs1n n i j) 8380417"; tm "&@ZB@:int"] WIRE_NORM_RANGE) f1 in
       MP_TAC(SPECL [`(ctn:num->byte list) n`; tm "\\(i:num) (j:num). mldsa_modpm (ysamp (n:num) i j + cs1n n i j) 8380417"; tm "\\(i:num) (j:num). mldsa_makehint @G2@ (--(ct0n (n:num) i j)) (wn n i j - cs2n n i j + ct0n n i j)"] (g "fin")) THEN
       ANTS_TAC THENL
        [CONJ_TAC THENL
          [REPEAT STRIP_TAC THEN MP_TAC(SPEC_ALL rng) THEN ASM_REWRITE_TAC[] THEN BETA_TAC THEN INT_ARITH_TAC;
           REWRITE_TAC[] THEN ACCEPT_TAC f4];
         REWRITE_TAC[]]);
     FIRST_ASSUM(fun th -> if concl th = acc_stmt then ACCEPT_TAC th else NO_TAC);
     FIRST_ASSUM(fun th -> if concl th = third_stmt then ACCEPT_TAC th else NO_TAC)]);;
(* ------------------------------------------------------------------------- *)
(* The main theorems: STMT_SIGN_INTERNAL_MU and STMT_SIGN_INTERNAL.          *)
(* ------------------------------------------------------------------------- *)

let wire_hw_def p = match p with "44" -> mldsa44 | "65" -> mldsa65 | _ -> mldsa87;;

let wire_final_prove p fam chain br =
  let ch = wire_inst_chain p fam chain in
  let lo = wire_loop_inst p fam in
  let bri = wire_inst_br p fam br in
  let stmt = top_tm p (if fam = "mu" then STMT_SIGN_INTERNAL_MU else STMT_SIGN_INTERNAL) in
  prove(stmt,
   (if fam = "mu" then
      X_GEN_TAC `sk:byte list` THEN X_GEN_TAC `mu:byte list` THEN X_GEN_TAC `rnd:byte list`
    else
      X_GEN_TAC `sk:byte list` THEN X_GEN_TAC `m:byte list` THEN X_GEN_TAC `rnd:byte list`) THEN
   STRIP_TAC THEN
   SUBGOAL_THEN (lhand(concl bri)) (fun b -> LABEL_TAC "BR3" (CONJUNCT2(CONJUNCT2(MP bri b)))) THENL [wire_ants_tac; ALL_TAC] THEN
   SUBGOAL_THEN (lhand(concl ch)) (fun a ->
     let chth = CONV_RULE(DEPTH_CONV BETA_CONV) (MP ch a) in
     MP_TAC(MP lo chth)) THENL [wire_ants_tac; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   (if fam = "internal" then REWRITE_TAC[mldsa_sign_internal] else ALL_TAC) THEN
   REWRITE_TAC[wire_hw_def p; mldsa_sign_mu; mldsa_attempt_allowed] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN
   CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[WIRE_MH_ASSOC] THEN
   COND_CASES_TAC THENL
    [USE_THEN "BR3" (fun br3 -> FIRST_ASSUM(fun c ->
       let pp = rand(concl c) in
       let accm = CONJUNCT1(EQ_MP (BETA_RULE(ISPEC pp MINIMAL)) c) in
       SIMP_TAC[MP (SPEC (mk_comb(`(minimal):(num->bool)->num`,pp)) br3) accm;
                mldsa_sign_of_option; lift_sign_internal_result]));
     SIMP_TAC[mldsa_sign_of_option; lift_sign_internal_result]]);;

(* ------------------------------------------------------------------------- *)
(* Instances.                                                                *)
(* ------------------------------------------------------------------------- *)

let WIRE_BR_44 = wire_br_prove "44" "mu";;
let WIRE_CHAIN_44 = wire_chain_prove "44" "mu" WIRE_BR_44;;
let EQ_SIGN_INTERNAL_MU_MLDSA44 = wire_final_prove "44" "mu" WIRE_CHAIN_44 WIRE_BR_44;;

let WIRE_BR_65 = wire_br_prove "65" "mu";;
let WIRE_CHAIN_65 = wire_chain_prove "65" "mu" WIRE_BR_65;;
let EQ_SIGN_INTERNAL_MU_MLDSA65 = wire_final_prove "65" "mu" WIRE_CHAIN_65 WIRE_BR_65;;

let WIRE_BR_87 = wire_br_prove "87" "mu";;
let WIRE_CHAIN_87 = wire_chain_prove "87" "mu" WIRE_BR_87;;
let EQ_SIGN_INTERNAL_MU_MLDSA87 = wire_final_prove "87" "mu" WIRE_CHAIN_87 WIRE_BR_87;;

let WIRE_BRI_44 = wire_br_prove "44" "internal";;
let WIRE_CHAINI_44 = wire_chain_prove "44" "internal" WIRE_BRI_44;;
let EQ_SIGN_INTERNAL_MLDSA44 = wire_final_prove "44" "internal" WIRE_CHAINI_44 WIRE_BRI_44;;

let WIRE_BRI_65 = wire_br_prove "65" "internal";;
let WIRE_CHAINI_65 = wire_chain_prove "65" "internal" WIRE_BRI_65;;
let EQ_SIGN_INTERNAL_MLDSA65 = wire_final_prove "65" "internal" WIRE_CHAINI_65 WIRE_BRI_65;;

let WIRE_BRI_87 = wire_br_prove "87" "internal";;
let WIRE_CHAINI_87 = wire_chain_prove "87" "internal" WIRE_BRI_87;;
let EQ_SIGN_INTERNAL_MLDSA87 = wire_final_prove "87" "internal" WIRE_CHAINI_87 WIRE_BRI_87;;

(* The theorems have no hypotheses.                                          *)

List.iter (fun th -> if hyp th <> [] then failwith "wire_sign: stray hypothesis")
 [EQ_SIGN_INTERNAL_MU_MLDSA44; EQ_SIGN_INTERNAL_MU_MLDSA65;
  EQ_SIGN_INTERNAL_MU_MLDSA87; EQ_SIGN_INTERNAL_MLDSA44;
  EQ_SIGN_INTERNAL_MLDSA65; EQ_SIGN_INTERNAL_MLDSA87];;
