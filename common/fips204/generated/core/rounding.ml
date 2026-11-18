(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Equivalence of the generated and the handwritten FIPS 204: the rounding   *)
(* functions (FIPS 204 Section 2.3 and Algorithms 35-40) and the infinity    *)
(* norms, for ML-DSA-44, -65 and -87.                                        *)
(*                                                                           *)
(*  - typed_hol_mod_pm, ReduceModQ (EQ_TYPED_HOL_MOD_PM, EQ_REDUCEMODQ).     *)
(*  - Power2Round, Decompose, HighBits, LowBits, MakeHint, UseHint of each   *)
(*    parameter set on lift_zq r, for every integer r (EQ_DECOMPOSE_MLDSA44  *)
(*    etc.), and on every element x of the generated Z_q, by its             *)
(*    representative &(residue_rep(fips204_zq_residue x)) (the _REP forms).  *)
(*  - FixedVector{HighBits,LowBits,MakeHint,UseHint,Power2Round}_k_P on      *)
(*    lifted vectors lift_vec (\i. lift_poly (a i)) of k polynomials.        *)
(*  - The norms. The handwritten spec has the bound mldsa_norm_lt b, the     *)
(*    generated InfNorm functions compute the maximum, here round_infnorm k  *)
(*    a = max {abs(a i j) | i < k, j < 256} (and 0). ROUND_INFNORM_LT and    *)
(*    ROUND_INFNORM_VEC_NORM_LT turn a comparison of it with a bound into    *)
(*    the handwritten bound predicates.                                      *)
(*  - VectorHighBits, VectorLowBits, VectorPower2Round (and _body), InfNorm  *)
(*    (and _body) on lists of any length k; the generated algorithms do not  *)
(*    call these.                                                            *)
(*  - The local copies of RqVectorCentered and of the norm in ML_DSA_Sign_   *)
(*    internal(_mu)_P (callable_1_0 and callable_3_0).                       *)
(*                                                                           *)
(* Load from the repository root after base.ml and common.ml. The      *)
(* generic lemmas are local (prefix ROUND_), so the file does not depend on  *)
(* core.ml.                                                                  *)
(* ========================================================================= *)

needs "common/fips204/generated/core/common.ml";;
needs "common/fips204/generated/core/core.ml";;

(* ------------------------------------------------------------------------- *)
(* Basic lemmas: monad, arithmetic primitives, lifts.                        *)
(* ------------------------------------------------------------------------- *)


let ROUND_ISA_INT_MOD_POS = prove
 (`!a b. &0 < b ==> isa_int_mod a b = a rem b`,
  SIMP_TAC[isa_int_mod; INT_ARITH `&0:int < b ==> ~(b < &0)`]);;

let ROUND_ISA_INT_DIV_POS = prove
 (`!a b. &0 < b ==> isa_int_div a b = a div b`,
  SIMP_TAC[isa_int_div; INT_ARITH `&0:int < b ==> ~(b < &0)`]);;

let ROUND_AOP_DISTINCT = prove
 (`~(APow = AQuot) /\ ~(APow = AMod) /\ ~(AQuot = ADiv) /\
   ~(AQuot = AMod) /\ ~(AMod = ADiv) /\ ~(AMod = AQuot)`,
  REWRITE_TAC[distinctness "aop"]);;

let ROUND_AQUOT = prove
 (`!a b. &0 < b /\ b divides a
         ==> typed_hol_int_arithmetic AQuot a b = Value (a div b)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[typed_hol_int_arithmetic_DEF; arith_faults_DEF; int_op_DEF;
               case_aop_DEF; ROUND_AOP_DISTINCT; ROUND_ISA_INT_MOD_POS;
               ROUND_ISA_INT_DIV_POS; INT_REM_EQ_0] THEN
  ASM_INT_ARITH_TAC);;

let ROUND_AMOD = prove
 (`!a b. &0 < b ==> typed_hol_int_arithmetic AMod a b = Value (a rem b)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[typed_hol_int_arithmetic_DEF; arith_faults_DEF; int_op_DEF;
               case_aop_DEF; ROUND_AOP_DISTINCT; ROUND_ISA_INT_MOD_POS] THEN
  ASM_INT_ARITH_TAC);;

let ROUND_INT_TO_BIT = prove
 (`!b. typed_hol_int_to_bit (if b then &1 else &0) = Value b`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[typed_hol_int_to_bit_DEF] THEN CONV_TAC INT_REDUCE_CONV);;

let ROUND_BIT_VALUE_EQ_1 = prove
 (`!b. ((if b then &1 else &0:int) = &1) <=> b`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN CONV_TAC INT_REDUCE_CONV);;

(* Z_q.                                                                      *)


let ROUND_REM_Q_POS = prove
 (`!x. &0 <= x rem &8380417`,
  REWRITE_TAC[INT_REM_POS_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let ROUND_RESIDUE_OF_INT_MOD_Q = prove
 (`!x. residue_rep(residue_of_int_mod x:(8380417)residue) =
       num_of_int(x rem &8380417)`,
  REWRITE_TAC[residue_of_int_mod_DEF; residue_SEL_CTR;
              DIMINDEX_Q] THEN
  SIMP_TAC[ROUND_ISA_INT_MOD_POS; INT_ARITH `&0:int < &8380417`] THEN
  REWRITE_TAC[isa_nat; ROUND_REM_Q_POS]);;

let EQ_REDUCEMODQ = prove
 (`!x. ReduceModQ_hol x = Value (lift_zq x)`,
  REWRITE_TAC[ReduceModQ_hol_DEF] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM lift_zq] THEN
  SIMP_TAC[ROUND_ISA_INT_MOD_POS; INT_ARITH `&0:int < &8380417`;
           LIFT_ZQ_REM]);;

(* mod+-.                                                                    *)

let EQ_TYPED_HOL_MOD_PM = prove
 (`!a m. typed_hol_mod_pm a m =
         if m <= &0 then Fault Bounds_Error
         else Value (mldsa_modpm a (num_of_int m))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[typed_hol_mod_pm_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_NOT_LE]) THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_LT_IMP_LE; mod_pm_int_DEF; mldsa_modpm;
               ROUND_ISA_INT_MOD_POS] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM INT_NOT_LT] THEN MESON_TAC[]);;

let EQ_TYPED_HOL_MOD_PM_NUM = prove
 (`!a m. ~(m = 0) ==> typed_hol_mod_pm a (&m) = Value (mldsa_modpm a m)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[EQ_TYPED_HOL_MOD_PM; INT_OF_NUM_LE; NUM_OF_INT_OF_NUM;
                  ARITH_RULE `m <= 0 <=> m = 0`]);;

(* ------------------------------------------------------------------------- *)
(* The scalar rounding functions. Each generated function of Z_q reads the   *)
(* representative &(residue_rep(fips204_zq_residue x)) of its argument and   *)
(* reduces it mod q, so it agrees with the handwritten function of that      *)
(* integer for every x (the _REP lemmas), and on lifted arguments with the   *)
(* handwritten function of the integer itself.                               *)
(* ------------------------------------------------------------------------- *)

let ROUND_MODPM_DIVIDES = prove
 (`!a m. ~(m = 0) ==> &m divides (a - mldsa_modpm a m)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `a:int` o
             MATCH_MP (ONCE_REWRITE_RULE[SWAP_FORALL_THM] MLDSA_MODPM)) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN CONV_TAC INTEGER_RULE);;

let ROUND_POWER2ROUND_REM = prove
 (`!r. mldsa_power2round (r rem &8380417) = mldsa_power2round r`,
  REWRITE_TAC[mldsa_power2round; INT_REM_REM]);;

let ROUND_USEHINT_REM = prove
 (`!gamma2 h r. mldsa_usehint gamma2 h (r rem &8380417) =
                mldsa_usehint gamma2 h r`,
  REWRITE_TAC[mldsa_usehint; MLDSA_HIGHBITS_REM; MLDSA_LOWBITS_REM]);;

let ROUND_FIPS204_ZQ_REP = prove
 (`!y. &(residue_rep(fips204_zq_residue
                      (FIPS204_Zq(residue_of_int_mod y)))) = y rem &8380417`,
  REWRITE_TAC[GSYM lift_zq; LIFT_ZQ_REP]);;

(* Textual substitution, to state the lemmas of the three parameter sets.    *)

let round_subst =
  let rec replace pat rep s =
    let n = String.length pat and l = String.length s in
    let b = Buffer.create l in
    let rec go i =
      if i > l - n then Buffer.add_string b (String.sub s i (l - i))
      else if String.sub s i n = pat then (Buffer.add_string b rep; go (i + n))
      else (Buffer.add_char b s.[i]; go (i + 1)) in
    go 0; Buffer.contents b in
  fun prs s -> itlist (fun (p,r) s -> replace p r s) (rev prs) s;;

let round_scalar_thms
     (p,gamma2,decompose_def,highbits_def,lowbits_def,makehint_def,
      usehint_def,power2round_def) =
  let alpha = 2 * gamma2 in
  let tm s =
    parse_term
     (round_subst ["PSET",p; "GAMMA2",string_of_int gamma2;
                   "ALPHA",string_of_int alpha;
                   "MQ",string_of_int(8380416 / alpha)] s) in
  let alpha_pos = INT_ARITH (tm "&0:int < &ALPHA")
  and alpha_div = prove(tm "&ALPHA divides &8380416:int",
    REWRITE_TAC[GSYM INT_REM_EQ_0] THEN CONV_TAC INT_REDUCE_CONV)
  and m_pos = INT_ARITH (tm "&0:int < &MQ") in
  let decompose_rep = prove
   (tm "!x. Decompose_PSET_Configuration_hol x =
            Value (mldsa_decompose GAMMA2
                    (&(residue_rep(fips204_zq_residue x))))",
    GEN_TAC THEN REWRITE_TAC[decompose_def; mldsa_decompose] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SIMP_TAC[ROUND_ISA_INT_MOD_POS; INT_ARITH `&0:int < &8380417`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[EQ_TYPED_HOL_MOD_PM_NUM; ARITH_EQ; NATIVE_BIND] THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[ROUND_AQUOT; ROUND_MODPM_DIVIDES; ARITH_EQ; alpha_pos;
                 NATIVE_BIND]) in
  let decompose = prove
   (tm "!r. Decompose_PSET_Configuration_hol (lift_zq r) =
            Value (mldsa_decompose GAMMA2 r)",
    REWRITE_TAC[decompose_rep; LIFT_ZQ_REP; MLDSA_DECOMPOSE_REM]) in
  let highbits_rep = prove
   (tm "!x. HighBits_PSET_Configuration_hol x =
            Value (mldsa_highbits GAMMA2
                    (&(residue_rep(fips204_zq_residue x))))",
    REWRITE_TAC[highbits_def; decompose_rep; NATIVE_BIND;
                mldsa_highbits]) in
  let highbits = prove
   (tm "!r. HighBits_PSET_Configuration_hol (lift_zq r) =
            Value (mldsa_highbits GAMMA2 r)",
    REWRITE_TAC[highbits_rep; LIFT_ZQ_REP; MLDSA_HIGHBITS_REM]) in
  let lowbits_rep = prove
   (tm "!x. LowBits_PSET_Configuration_hol x =
            Value (mldsa_lowbits GAMMA2
                    (&(residue_rep(fips204_zq_residue x))))",
    REWRITE_TAC[lowbits_def; decompose_rep; NATIVE_BIND;
                mldsa_lowbits]) in
  let lowbits = prove
   (tm "!r. LowBits_PSET_Configuration_hol (lift_zq r) =
            Value (mldsa_lowbits GAMMA2 r)",
    REWRITE_TAC[lowbits_rep; LIFT_ZQ_REP; MLDSA_LOWBITS_REM]) in
  let makehint_rep = prove
   (tm "!z r. MakeHint_PSET_Configuration_hol z r =
              Value (mldsa_makehint GAMMA2
                      (&(residue_rep(fips204_zq_residue z)))
                      (&(residue_rep(fips204_zq_residue r))))",
    REPEAT GEN_TAC THEN
    REWRITE_TAC[makehint_def; highbits_rep; NATIVE_BIND] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[highbits_rep; NATIVE_BIND; ROUND_FIPS204_ZQ_REP;
                MLDSA_HIGHBITS_REM; typed_hol_bit_value_DEF;
                ROUND_INT_TO_BIT; mldsa_makehint]) in
  let makehint = prove
   (tm "!z r. MakeHint_PSET_Configuration_hol (lift_zq z) (lift_zq r) =
              Value (mldsa_makehint GAMMA2 z r)",
    REWRITE_TAC[makehint_rep; LIFT_ZQ_REP; MLDSA_MAKEHINT_REM]) in
  let usehint_rep = prove
   (tm "!h x. UseHint_PSET_Configuration_hol h x =
              Value (mldsa_usehint GAMMA2 h
                      (&(residue_rep(fips204_zq_residue x))))",
    REPEAT GEN_TAC THEN
    REWRITE_TAC[usehint_def; mldsa_usehint; mldsa_highbits; mldsa_lowbits] THEN
    SIMP_TAC[ROUND_AQUOT; alpha_pos; alpha_div; NATIVE_BIND;
             decompose_rep] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV)) THEN
    REWRITE_TAC[typed_hol_bit_value_DEF; NATIVE_BIND;
                ROUND_BIT_VALUE_EQ_1] THEN
    SIMP_TAC[ROUND_AMOD; m_pos] THEN
    ASM_CASES_TAC `h:bool` THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ROUND_AMOD; m_pos; INT_ARITH `~(&0:int < x) ==> x <= &0`])
  in
  let usehint = prove
   (tm "!h r. UseHint_PSET_Configuration_hol h (lift_zq r) =
              Value (mldsa_usehint GAMMA2 h r)",
    REWRITE_TAC[usehint_rep; LIFT_ZQ_REP; ROUND_USEHINT_REM]) in
  let power2round_rep = prove
   (tm "!x. Power2Round_PSET_Configuration_hol x =
            Value (mldsa_power2round (&(residue_rep(fips204_zq_residue x))))",
    GEN_TAC THEN REWRITE_TAC[power2round_def; mldsa_power2round] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SIMP_TAC[ROUND_ISA_INT_MOD_POS; INT_ARITH `&0:int < &8380417`] THEN
    REWRITE_TAC[TYPED_HOL_INT_POW_NUM; NATIVE_BIND] THEN
    CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
    SIMP_TAC[EQ_TYPED_HOL_MOD_PM_NUM; ARITH_EQ; NATIVE_BIND] THEN
    SIMP_TAC[ROUND_AQUOT; ROUND_MODPM_DIVIDES; ARITH_EQ;
             INT_ARITH `&0:int < &8192`; NATIVE_BIND]) in
  let power2round = prove
   (tm "!r. Power2Round_PSET_Configuration_hol (lift_zq r) =
            Value (mldsa_power2round r)",
    REWRITE_TAC[power2round_rep; LIFT_ZQ_REP; ROUND_POWER2ROUND_REM]) in
  (decompose_rep,decompose,highbits_rep,highbits,lowbits_rep,lowbits,
   makehint_rep,makehint,usehint_rep,usehint,power2round_rep,power2round);;

let (EQ_DECOMPOSE_MLDSA44_REP,EQ_DECOMPOSE_MLDSA44,
     EQ_HIGHBITS_MLDSA44_REP,EQ_HIGHBITS_MLDSA44,
     EQ_LOWBITS_MLDSA44_REP,EQ_LOWBITS_MLDSA44,
     EQ_MAKEHINT_MLDSA44_REP,EQ_MAKEHINT_MLDSA44,
     EQ_USEHINT_MLDSA44_REP,EQ_USEHINT_MLDSA44,
     EQ_POWER2ROUND_MLDSA44_REP,EQ_POWER2ROUND_MLDSA44) =
  round_scalar_thms
   ("MLDSA44",95232,
    Decompose_MLDSA44_Configuration_hol_DEF,
    HighBits_MLDSA44_Configuration_hol_DEF,
    LowBits_MLDSA44_Configuration_hol_DEF,
    MakeHint_MLDSA44_Configuration_hol_DEF,
    UseHint_MLDSA44_Configuration_hol_DEF,
    Power2Round_MLDSA44_Configuration_hol_DEF);;

let (EQ_DECOMPOSE_MLDSA65_REP,EQ_DECOMPOSE_MLDSA65,
     EQ_HIGHBITS_MLDSA65_REP,EQ_HIGHBITS_MLDSA65,
     EQ_LOWBITS_MLDSA65_REP,EQ_LOWBITS_MLDSA65,
     EQ_MAKEHINT_MLDSA65_REP,EQ_MAKEHINT_MLDSA65,
     EQ_USEHINT_MLDSA65_REP,EQ_USEHINT_MLDSA65,
     EQ_POWER2ROUND_MLDSA65_REP,EQ_POWER2ROUND_MLDSA65) =
  round_scalar_thms
   ("MLDSA65",261888,
    Decompose_MLDSA65_Configuration_hol_DEF,
    HighBits_MLDSA65_Configuration_hol_DEF,
    LowBits_MLDSA65_Configuration_hol_DEF,
    MakeHint_MLDSA65_Configuration_hol_DEF,
    UseHint_MLDSA65_Configuration_hol_DEF,
    Power2Round_MLDSA65_Configuration_hol_DEF);;

let (EQ_DECOMPOSE_MLDSA87_REP,EQ_DECOMPOSE_MLDSA87,
     EQ_HIGHBITS_MLDSA87_REP,EQ_HIGHBITS_MLDSA87,
     EQ_LOWBITS_MLDSA87_REP,EQ_LOWBITS_MLDSA87,
     EQ_MAKEHINT_MLDSA87_REP,EQ_MAKEHINT_MLDSA87,
     EQ_USEHINT_MLDSA87_REP,EQ_USEHINT_MLDSA87,
     EQ_POWER2ROUND_MLDSA87_REP,EQ_POWER2ROUND_MLDSA87) =
  round_scalar_thms
   ("MLDSA87",261888,
    Decompose_MLDSA87_Configuration_hol_DEF,
    HighBits_MLDSA87_Configuration_hol_DEF,
    LowBits_MLDSA87_Configuration_hol_DEF,
    MakeHint_MLDSA87_Configuration_hol_DEF,
    UseHint_MLDSA87_Configuration_hol_DEF,
    Power2Round_MLDSA87_Configuration_hol_DEF);;

(* ------------------------------------------------------------------------- *)
(* Counted loops. The generated loops "for i from 0 to n - 1" are            *)
(* native_foldl body (native_schedule m (\i. i < &n) (\i. i + &1) (&0)) with *)
(* a fuel m > n. If the body takes the state st i to st (i + 1), the loop    *)
(* takes st 0 to st n. ROUND_FOLDL2 is the same for the doubly nested loops  *)
(* over i < k and j < 256 of the vector functions, and ROUND_MAPLOOP the     *)
(* case where the state is rep s for an array s of values, and step (i,j)    *)
(* sets s i j to f i j.                                                      *)
(* ------------------------------------------------------------------------- *)

let ROUND_FOLDL_SCHEDULE_GEN = prove
 (`!(body:int->S->(S)native_result) st d s m n.
        s + d = n /\ d < m /\
        (!i. s <= i /\ i < n ==> body (&i) (st i) = Value (st (SUC i)))
        ==> native_foldl body
             (native_schedule m (\i. i < &n) (\i. i + &1) (&s)) (st s) =
            Value (st n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `m':num` SUBST_ALL_TAC)
   (SPEC `m:num` num_CASES) THEN
  REWRITE_TAC[CONJUNCT1 LT; LT_SUC; LT_0] THEN STRIP_TAC THEN
  REWRITE_TAC[native_schedule_DEF] THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_eq o concl)) THEN
    REWRITE_TAC[ADD_CLAUSES; INT_LT_REFL; native_foldl_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `&s:int < &n` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[native_foldl_DEF] THEN
  SUBGOAL_THEN
   `(body:int->S->(S)native_result) (&s) (st s) = Value (st (SUC s))`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NATIVE_BIND; INT_OF_NUM_ADD; ADD1] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM ADD1] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let ROUND_FOLDL_SCHEDULE = prove
 (`!(body:int->S->(S)native_result) st m n.
        n < m /\ (!i. i < n ==> body (&i) (st i) = Value (st (SUC i)))
        ==> native_foldl body
             (native_schedule m (\i. i < &n) (\i. i + &1) (&0)) (st 0) =
            Value (st n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ROUND_FOLDL_SCHEDULE_GEN THEN
  EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[ADD_CLAUSES; LE_0]);;

let ROUND_FOLDL2 = prove
 (`!(body:int->int->S->(S)native_result) G k m1 m2 x y.
        k < m1 /\ 256 < m2 /\ G 0 0 = x /\ G k 0 = y /\
        (!i. i < k ==> G i 256 = G (SUC i) 0) /\
        (!i j. i < k /\ j < 256
               ==> body (&i) (&j) (G i j) = Value (G i (SUC j)))
        ==> native_foldl
             (\i. native_foldl (body i)
                   (native_schedule m2 (\j. j < &256) (\j. j + &1) (&0)))
             (native_schedule m1 (\i. i < &k) (\i. i + &1) (&0)) x =
            Value y`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXPAND_TAC ["x"; "y"] THEN
  MP_TAC(ISPECL
   [`\i. native_foldl ((body:int->int->S->(S)native_result) i)
          (native_schedule m2 (\j. j < &256) (\j. j + &1) (&0))`;
    `\i. (G:num->num->S) i 0`; `m1:num`; `k:num`] ROUND_FOLDL_SCHEDULE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `i < k`))]) THEN
  MATCH_MP_TAC ROUND_FOLDL_SCHEDULE THEN ASM_SIMP_TAC[]);;

let ROUND_MAPLOOP = prove
 (`!(rep:(num->num->A)->S) (body:int->int->S->(S)native_result) f s0 k m1 m2.
        k < m1 /\ 256 < m2 /\
        (!s s'. (!i j. i < k /\ j < 256 ==> s i j = s' i j)
                ==> rep s = rep s') /\
        (!s i j. i < k /\ j < 256
                 ==> body (&i) (&j) (rep s) =
                     Value (rep (\i' j'. if i' = i /\ j' = j then f i j
                                         else s i' j')))
        ==> native_foldl
             (\i. native_foldl (body i)
                   (native_schedule m2 (\j. j < &256) (\j. j + &1) (&0)))
             (native_schedule m1 (\i. i < &k) (\i. i + &1) (&0)) (rep s0) =
            Value (rep f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ROUND_FOLDL2 THEN
  EXISTS_TAC `\i j. (rep:(num->num->A)->S)
                    (\i' j'. if i' < i \/ i' = i /\ j' < j then f i' j'
                             else s0 i' j')` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LT];
    FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[LT] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY X_GEN_TAC [`i':num`; `j':num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `i':num = i /\ j':num = j` THEN
    ASM_REWRITE_TAC[LT_REFL; LT] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Lists: indexing, update and REPLICATE on list_of_seq.                     *)
(* ------------------------------------------------------------------------- *)


let ROUND_LIST_UPDATE_LIST_OF_SEQ = prove
 (`!(f:num->A) n i v.
        i < n ==> native_list_update (list_of_seq f n) (&i) v =
                  SOME (list_of_seq (\x. if x = i then v else f x) n)`,
  SIMP_TAC[native_list_update_DEF; INT_POS; INT_OF_NUM_LT; LENGTH_LIST_OF_SEQ;
           ISA_NAT_NUM; ISA_LIST_UPDATE_LIST_OF_SEQ]);;

let ROUND_NESTED_UPDATE_LIST_OF_SEQ = prove
 (`!(f:num->A) n i inner.
        i < n ==> typed_hol_nested_update inner (list_of_seq f n) (&i) =
                  isa_map_option
                   (\y. list_of_seq (\x. if x = i then y else f x) n)
                   (inner (f i))`,
  SIMP_TAC[typed_hol_nested_update_DEF; INT_POS; INT_OF_NUM_LT;
           LENGTH_LIST_OF_SEQ; ISA_NAT_NUM;
           ISA_LIST_UPDATE_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

(* ------------------------------------------------------------------------- *)
(* Lifted vectors and polynomials: their entries, congruence, and the        *)
(* updates of one coefficient that the vector functions perform.             *)
(* ------------------------------------------------------------------------- *)


let ROUND_INDEX_VEC = prove
 (`!(v:num->B) i.
        i < dimindex(:N)
        ==> native_list_index (common_vec_entries (lift_vec v:(N,B)common_vec))
                              (&i) = SOME (v i)`,
  SIMP_TAC[COMMON_VEC_ENTRIES_LIFT; NATIVE_LIST_INDEX_LIST_OF_SEQ]);;

let ROUND_INDEX_POLY = prove
 (`!a j. j < 256
         ==> native_list_index
               (fips204_poly_coefficients (lift_poly a:(A)fips204_poly)) (&j) =
             SOME (lift_zq (a j))`,
  SIMP_TAC[FIPS204_POLY_COEFFICIENTS_LIFT; NATIVE_LIST_INDEX_LIST_OF_SEQ]);;

let ROUND_INDEX_INTPOLY = prove
 (`!a j. j < 256
         ==> native_list_index (fips204_intpoly_coefficients (lift_intpoly a))
                               (&j) = SOME (a j)`,
  SIMP_TAC[FIPS204_INTPOLY_COEFFICIENTS_LIFT; NATIVE_LIST_INDEX_LIST_OF_SEQ]);;

let ROUND_INDEX_BITPOLY = prove
 (`!h j. j < 256
         ==> native_list_index (fips204_bitpoly_coefficients (lift_bitpoly h))
                               (&j) =
             SOME (residue_of_int_mod (if h j then &1 else &0))`,
  SIMP_TAC[FIPS204_BITPOLY_COEFFICIENTS_LIFT; NATIVE_LIST_INDEX_LIST_OF_SEQ]);;

let ROUND_BIT_REP = prove
 (`!b. &(residue_rep(residue_of_int_mod (if b then &1 else &0):(2)residue)) =
       if b then &1 else &0:int`,
  GEN_TAC THEN
  REWRITE_TAC[residue_of_int_mod_DEF; residue_SEL_CTR; DIMINDEX_2] THEN
  SIMP_TAC[ROUND_ISA_INT_MOD_POS; INT_ARITH `&0:int < &2`] THEN
  BOOL_CASES_TAC `b:bool` THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[ISA_NAT_NUM]);;

(* Congruence: the lifts depend only on the entries in range.                *)


let ROUND_LIFT_BITPOLY_CONG = prove
 (`!h g. (!i. i < 256 ==> (h i <=> g i)) ==> lift_bitpoly h = lift_bitpoly g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lift_bitpoly] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN ASM_SIMP_TAC[]);;

let ROUND_INTVEC_CONG = prove
 (`!s s'. (!i j. i < dimindex(:N) /\ j < 256 ==> s i j = s' i j)
          ==> (lift_vec (\i. lift_intpoly (s i)):
                 (N,fips204_intpoly)common_vec) =
              lift_vec (\i. lift_intpoly (s' i))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIFT_VEC_CONG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC LIFT_INTPOLY_CONG THEN ASM_SIMP_TAC[]);;

let ROUND_ZQLISTS_CONG = prove
 (`!k s s'. (!i j. i < k /\ j < 256 ==> s i j = s' i j)
            ==> list_of_seq (\i. list_of_seq (\j. lift_zq (s i j)) 256) k =
                list_of_seq (\i. list_of_seq (\j. lift_zq (s' i j)) 256) k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN ASM_SIMP_TAC[]);;

(* Initial values.                                                           *)

let ROUND_INIT_INTVEC = prove
 (`!n x. n = dimindex(:N)
         ==> Common_Vec (MAP FIPS204_IntPoly (REPLICATE n (REPLICATE 256 x))) =
             (lift_vec (\i. lift_intpoly (\j. x)):
                (N,fips204_intpoly)common_vec)`,
  SIMP_TAC[lift_vec; lift_intpoly; REPLICATE_LIST_OF_SEQ;
           MAP_LIST_OF_SEQ; o_DEF]);;

let ROUND_INIT_BITVEC = prove
 (`!n. n = dimindex(:N)
       ==> Common_Vec (MAP FIPS204_BitPoly
                        (REPLICATE n
                          (REPLICATE 256 (residue_of_int_mod (&0))))) =
           (lift_vec (\i. lift_bitpoly (\j. F)):
              (N,fips204_bitpoly)common_vec)`,
  SIMP_TAC[lift_vec; lift_bitpoly; REPLICATE_LIST_OF_SEQ;
           MAP_LIST_OF_SEQ; o_DEF]);;

let ROUND_MAP_COEFFS_LIFT_POLY = prove
 (`!a k. MAP fips204_poly_coefficients
             (list_of_seq (\i. lift_poly (a i):(A)fips204_poly) k) =
         list_of_seq (\i. list_of_seq (\j. lift_zq (a i j)) 256) k`,
  REWRITE_TAC[MAP_LIST_OF_SEQ; o_DEF; FIPS204_POLY_COEFFICIENTS_LIFT]);;

let ROUND_MAP_FIPS204_POLY = prove
 (`!a k. MAP FIPS204_Poly
             (list_of_seq (\i. list_of_seq (\j. lift_zq (a i j)) 256) k) =
         list_of_seq (\i. lift_poly (a i):(A)fips204_poly) k`,
  REWRITE_TAC[MAP_LIST_OF_SEQ; o_DEF; lift_poly]);;

(* Updates.                                                                  *)

let ROUND_UPDATE_INTVEC = prove
 (`!s i j v.
        i < dimindex(:N) /\ j < 256
        ==> typed_hol_nominal_update Common_Vec common_vec_entries
             (\l. typed_hol_nested_update
                   (typed_hol_nominal_update FIPS204_IntPoly
                     fips204_intpoly_coefficients
                     (\c. native_list_update c (&j) v)) l (&i))
             (lift_vec (\i. lift_intpoly (s i)):
                (N,fips204_intpoly)common_vec) =
            SOME (lift_vec (\i'. lift_intpoly
                                  (\j'. if i' = i /\ j' = j then v
                                        else s i' j')))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[typed_hol_nominal_update_DEF; COMMON_VEC_ENTRIES_LIFT] THEN
  ASM_SIMP_TAC[ROUND_NESTED_UPDATE_LIST_OF_SEQ; FIPS204_INTPOLY_COEFFICIENTS_LIFT;
               typed_hol_nominal_update_DEF;
               ROUND_LIST_UPDATE_LIST_OF_SEQ; isa_map_option] THEN
  REWRITE_TAC[lift_vec; lift_intpoly] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x:num = i` THEN ASM_REWRITE_TAC[ETA_AX]);;

let ROUND_UPDATE_BITVEC = prove
 (`!s i j b.
        i < dimindex(:N) /\ j < 256
        ==> typed_hol_nominal_update Common_Vec common_vec_entries
             (\l. typed_hol_nested_update
                   (typed_hol_nominal_update FIPS204_BitPoly
                     fips204_bitpoly_coefficients
                     (\c. native_list_update c (&j)
                           (residue_of_int_mod (if b then &1 else &0))))
                   l (&i))
             (lift_vec (\i. lift_bitpoly (s i)):
                (N,fips204_bitpoly)common_vec) =
            SOME (lift_vec (\i'. lift_bitpoly
                                  (\j'. if i' = i /\ j' = j then b
                                        else s i' j')))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[typed_hol_nominal_update_DEF; COMMON_VEC_ENTRIES_LIFT] THEN
  ASM_SIMP_TAC[ROUND_NESTED_UPDATE_LIST_OF_SEQ; FIPS204_BITPOLY_COEFFICIENTS_LIFT;
               typed_hol_nominal_update_DEF;
               ROUND_LIST_UPDATE_LIST_OF_SEQ; isa_map_option] THEN
  REWRITE_TAC[lift_vec; lift_bitpoly] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x:num = i` THEN ASM_REWRITE_TAC[ETA_AX] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
  X_GEN_TAC `y:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `y:num = j` THEN ASM_REWRITE_TAC[]);;

let ROUND_UPDATE_ZQLISTS = prove
 (`!s k i j x.
        i < k /\ j < 256
        ==> typed_hol_nested_update
             (\row. native_list_update row (&j) (lift_zq x))
             (list_of_seq (\i. list_of_seq (\j. lift_zq (s i j)) 256) k) (&i) =
            SOME (list_of_seq (\i'. list_of_seq
                     (\j'. lift_zq (if i' = i /\ j' = j then x else s i' j'))
                     256) k)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ROUND_NESTED_UPDATE_LIST_OF_SEQ; ROUND_LIST_UPDATE_LIST_OF_SEQ;
               isa_map_option] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
  X_GEN_TAC `y:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `y:num = i` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
  X_GEN_TAC `z:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `z:num = j` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The vector functions FixedVector{HighBits,LowBits,MakeHint,UseHint,       *)
(* Power2Round}_k_P on lifted vectors of k polynomials. Each is a loop over  *)
(* i < k and j < 256 that applies the scalar function to coefficient j of    *)
(* entry i, so it is an instance of ROUND_MAPLOOP.                           *)
(* ------------------------------------------------------------------------- *)

let ROUND_DIMINDEX_5 = DIMINDEX_CONV `dimindex(:5)`;;
let ROUND_DIMINDEX_6 = DIMINDEX_CONV `dimindex(:6)`;;
let ROUND_DIMINDEX_7 = DIMINDEX_CONV `dimindex(:7)`;;
let ROUND_DIMINDEX_8 = DIMINDEX_CONV `dimindex(:8)`;;

let ROUND_DIMINDEX_THMS =
  [DIMINDEX_4; ROUND_DIMINDEX_5; ROUND_DIMINDEX_6; ROUND_DIMINDEX_7;
   ROUND_DIMINDEX_8];;

let ROUND_BIND_VALUE = prove
 (`!m (k:A->(B)native_result) x y.
        m = Value x /\ k x = y ==> native_bind m k = y`,
  SIMP_TAC[NATIVE_BIND]);;

(* The rewrites that evaluate one step of a loop body at (&i,&j).            *)

let ROUND_STEP_THMS =
  [NATIVE_BIND; TYPED_HOL_NONNEGATIVE_NUM; typed_hol_bit_value_DEF;
   BitToInteger_hol_DEF; TYPED_HOL_INT_POW_ONE; INT_MUL_LID; INT_ADD_LID;
   ROUND_INDEX_VEC; ROUND_INDEX_POLY; ROUND_INDEX_INTPOLY; ROUND_INDEX_BITPOLY;
   NATIVE_LIST_INDEX_LIST_OF_SEQ; ROUND_BIT_REP; ROUND_INT_TO_BIT;
   TYPED_HOL_READ; ROUND_UPDATE_INTVEC; ROUND_UPDATE_BITVEC;
   ROUND_UPDATE_ZQLISTS; EQ_REDUCEMODQ; COEFFICIENT_TO_INTEGER_LIFT;
   UNCURRY_DEF; typed_hol_slot_read_DEF; case_native_slot_DEF] @
  ROUND_DIMINDEX_THMS;;

(* Prove a loop over i < k, j < 256 whose state is rep s, by ROUND_MAPLOOP.  *)

let ROUND_MAPLOOP_TAC rep cong scalars =
  MATCH_MP_TAC(BETA_RULE(ISPEC rep ROUND_MAPLOOP)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC cong THEN
    ASM_REWRITE_TAC ROUND_DIMINDEX_THMS;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC(ROUND_STEP_THMS @ scalars);;

let ROUND_UNFOLD_TAC def =
  REPEAT GEN_TAC THEN REWRITE_TAC[def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP_TAC(ROUND_INIT_INTVEC :: ROUND_INIT_BITVEC :: ROUND_DIMINDEX_THMS);;

let round_tm prs s = parse_term (round_subst prs s);;

let round_intvec_rep k =
  round_tm ["KK",string_of_int k]
   "\\s. (lift_vec (\\i. lift_intpoly (s i)):(KK,fips204_intpoly)common_vec)";;

let round_bitvec_rep k =
  round_tm ["KK",string_of_int k]
   "\\s. (lift_vec (\\i. lift_bitpoly (s i)):(KK,fips204_bitpoly)common_vec)";;

let round_intvec2_rep k =
  round_tm ["KK",string_of_int k]
   "\\s:num->num->int#int.
       (lift_vec (\\i. lift_intpoly (\\j. FST(s i j))):
          (KK,fips204_intpoly)common_vec,
        lift_vec (\\i. lift_intpoly (\\j. SND(s i j))):
          (KK,fips204_intpoly)common_vec)";;

let ROUND_INTVEC2_CONG = prove
 (`!s s':num->num->int#int.
        (!i j. i < dimindex(:N) /\ j < 256 ==> s i j = s' i j)
        ==> ((lift_vec (\i. lift_intpoly (\j. FST(s i j))):
                (N,fips204_intpoly)common_vec),
             (lift_vec (\i. lift_intpoly (\j. SND(s i j))):
                (N,fips204_intpoly)common_vec)) =
            (lift_vec (\i. lift_intpoly (\j. FST(s' i j))),
             lift_vec (\i. lift_intpoly (\j. SND(s' i j))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THEN
  MATCH_MP_TAC ROUND_INTVEC_CONG THEN ASM_SIMP_TAC[]);;

let ROUND_INIT_INTVEC2 = prove
 (`(lift_vec (\i. lift_intpoly (\j. &0)):(N,fips204_intpoly)common_vec,
    lift_vec (\i. lift_intpoly (\j. &0)):(N,fips204_intpoly)common_vec) =
   (lift_vec (\i. lift_intpoly (\j. FST((\i j. (&0:int,&0:int)) i j))),
    lift_vec (\i. lift_intpoly (\j. SND((\i j. (&0:int,&0:int)) i j))))`,
  REWRITE_TAC[]);;

let round_fixedvector_thms
     (p,gamma2,k,highbits_def,lowbits_def,makehint_def,usehint_def,
      power2round_def,eq_highbits,eq_lowbits,eq_makehint,eq_usehint,
      eq_power2round) =
  let tm = round_tm ["PSET",p; "GAMMA2",string_of_int gamma2;
                     "KK",string_of_int k] in
  let highbits = prove
   (tm "!a. FixedVectorHighBits_KK_PSET_Configuration_hol
              (lift_vec (\\i. lift_poly (a i))) =
            Value (lift_vec (\\i. lift_intpoly
                                   (\\j. mldsa_highbits GAMMA2 (a i j))))",
    ROUND_UNFOLD_TAC highbits_def THEN
    ROUND_MAPLOOP_TAC (round_intvec_rep k) ROUND_INTVEC_CONG [eq_highbits]) in
  let lowbits = prove
   (tm "!a. FixedVectorLowBits_KK_PSET_Configuration_hol
              (lift_vec (\\i. lift_poly (a i))) =
            Value (lift_vec (\\i. lift_intpoly
                                   (\\j. mldsa_lowbits GAMMA2 (a i j))))",
    ROUND_UNFOLD_TAC lowbits_def THEN
    ROUND_MAPLOOP_TAC (round_intvec_rep k) ROUND_INTVEC_CONG [eq_lowbits]) in
  let makehint = prove
   (tm "!z r. FixedVectorMakeHint_KK_PSET_Configuration_hol
                (lift_vec (\\i. lift_poly (z i)))
                (lift_vec (\\i. lift_poly (r i))) =
              Value (lift_vec (\\i. lift_bitpoly
                              (\\j. mldsa_makehint GAMMA2 (z i j) (r i j))))",
    ROUND_UNFOLD_TAC makehint_def THEN
    ROUND_MAPLOOP_TAC (round_bitvec_rep k) LIFT_BITPOLY_VEC_CONG [eq_makehint]) in
  let usehint = prove
   (tm "!h r. FixedVectorUseHint_KK_PSET_Configuration_hol
                (lift_vec (\\i. lift_bitpoly (h i)))
                (lift_vec (\\i. lift_poly (r i))) =
              Value (lift_vec (\\i. lift_intpoly
                                (\\j. mldsa_usehint GAMMA2 (h i j) (r i j))))",
    ROUND_UNFOLD_TAC usehint_def THEN
    ROUND_MAPLOOP_TAC (round_intvec_rep k) ROUND_INTVEC_CONG [eq_usehint]) in
  let power2round = prove
   (tm "!t. FixedVectorPower2Round_KK_PSET_Configuration_hol
              (lift_vec (\\i. lift_poly (t i))) =
            Value (lift_vec (\\i. lift_intpoly
                                   (\\j. FST(mldsa_power2round (t i j)))),
                   lift_vec (\\i. lift_intpoly
                                   (\\j. SND(mldsa_power2round (t i j)))))",
    ROUND_UNFOLD_TAC power2round_def THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ROUND_INIT_INTVEC2] THEN
    ROUND_MAPLOOP_TAC (round_intvec2_rep k) ROUND_INTVEC2_CONG
     [eq_power2round] THEN
    REWRITE_TAC[COND_RAND]) in
  (highbits,lowbits,makehint,usehint,power2round);;

let (EQ_FIXEDVECTORHIGHBITS_4_MLDSA44,EQ_FIXEDVECTORLOWBITS_4_MLDSA44,
     EQ_FIXEDVECTORMAKEHINT_4_MLDSA44,EQ_FIXEDVECTORUSEHINT_4_MLDSA44,
     EQ_FIXEDVECTORPOWER2ROUND_4_MLDSA44) =
  round_fixedvector_thms
   ("MLDSA44",95232,4,
    FixedVectorHighBits_4_MLDSA44_Configuration_hol_DEF,
    FixedVectorLowBits_4_MLDSA44_Configuration_hol_DEF,
    FixedVectorMakeHint_4_MLDSA44_Configuration_hol_DEF,
    FixedVectorUseHint_4_MLDSA44_Configuration_hol_DEF,
    FixedVectorPower2Round_4_MLDSA44_Configuration_hol_DEF,
    EQ_HIGHBITS_MLDSA44,EQ_LOWBITS_MLDSA44,EQ_MAKEHINT_MLDSA44,
    EQ_USEHINT_MLDSA44,EQ_POWER2ROUND_MLDSA44);;

let (EQ_FIXEDVECTORHIGHBITS_6_MLDSA65,EQ_FIXEDVECTORLOWBITS_6_MLDSA65,
     EQ_FIXEDVECTORMAKEHINT_6_MLDSA65,EQ_FIXEDVECTORUSEHINT_6_MLDSA65,
     EQ_FIXEDVECTORPOWER2ROUND_6_MLDSA65) =
  round_fixedvector_thms
   ("MLDSA65",261888,6,
    FixedVectorHighBits_6_MLDSA65_Configuration_hol_DEF,
    FixedVectorLowBits_6_MLDSA65_Configuration_hol_DEF,
    FixedVectorMakeHint_6_MLDSA65_Configuration_hol_DEF,
    FixedVectorUseHint_6_MLDSA65_Configuration_hol_DEF,
    FixedVectorPower2Round_6_MLDSA65_Configuration_hol_DEF,
    EQ_HIGHBITS_MLDSA65,EQ_LOWBITS_MLDSA65,EQ_MAKEHINT_MLDSA65,
    EQ_USEHINT_MLDSA65,EQ_POWER2ROUND_MLDSA65);;

let (EQ_FIXEDVECTORHIGHBITS_8_MLDSA87,EQ_FIXEDVECTORLOWBITS_8_MLDSA87,
     EQ_FIXEDVECTORMAKEHINT_8_MLDSA87,EQ_FIXEDVECTORUSEHINT_8_MLDSA87,
     EQ_FIXEDVECTORPOWER2ROUND_8_MLDSA87) =
  round_fixedvector_thms
   ("MLDSA87",261888,8,
    FixedVectorHighBits_8_MLDSA87_Configuration_hol_DEF,
    FixedVectorLowBits_8_MLDSA87_Configuration_hol_DEF,
    FixedVectorMakeHint_8_MLDSA87_Configuration_hol_DEF,
    FixedVectorUseHint_8_MLDSA87_Configuration_hol_DEF,
    FixedVectorPower2Round_8_MLDSA87_Configuration_hol_DEF,
    EQ_HIGHBITS_MLDSA87,EQ_LOWBITS_MLDSA87,EQ_MAKEHINT_MLDSA87,
    EQ_USEHINT_MLDSA87,EQ_POWER2ROUND_MLDSA87);;

(* ------------------------------------------------------------------------- *)
(* Norms. The handwritten specification only has the bound mldsa_norm_lt b,  *)
(* while the generated InfNorm functions compute the maximum of the absolute *)
(* values, which the callers compare with the bound. round_infnorm k a is    *)
(* that maximum over i < k, j < 256 (0 if there are none), the coefficients  *)
(* taken in the order of the generated loops (p = 256 * i + j), and          *)
(* ROUND_INFNORM_LT and ROUND_INFNORM_VEC_NORM_LT relate it to the bounds.   *)
(* ------------------------------------------------------------------------- *)

let round_maxabs = define
 `round_maxabs (a:num->num->int) 0 = &0 /\
  round_maxabs a (SUC p) =
    max (abs(a (p DIV 256) (p MOD 256))) (round_maxabs a p)`;;

let round_infnorm = new_definition
 `round_infnorm k (a:num->num->int) = round_maxabs a (256 * k)`;;

let ROUND_MAXABS_LT = prove
 (`!a b p. round_maxabs a p < b <=>
           &0 < b /\ !q. q < p ==> abs(a (q DIV 256) (q MOD 256)) < b`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[round_maxabs; CONJUNCT1 LT; INT_MAX_LT] THEN
  REWRITE_TAC[LT] THEN MESON_TAC[]);;

let ROUND_INFNORM_LT = prove
 (`!k a b. round_infnorm k a < b <=>
           &0 < b /\ !i j. i < k /\ j < 256 ==> abs(a i j) < b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[round_infnorm; ROUND_MAXABS_LT] THEN
  AP_TERM_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `256 * i + j`) THEN
    ASM_SIMP_TAC[DIV_MOD_256_SMALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[DIV256_LT; MOD_LT_EQ; ARITH_EQ]]);;

let ROUND_INFNORM_POS = prove
 (`!k a. &0 <= round_infnorm k a`,
  REWRITE_TAC[GSYM INT_NOT_LT; ROUND_INFNORM_LT; INT_LT_REFL]);;

let ROUND_INFNORM_CONG = prove
 (`!k a a'. (!i j. i < k /\ j < 256 ==> a i j = a' i j)
            ==> round_infnorm k a = round_infnorm k a'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[round_infnorm] THEN
  SUBGOAL_THEN `!p. p <= 256 * k ==> round_maxabs a p = round_maxabs a' p`
   (fun th -> MATCH_MP_TAC th THEN REWRITE_TAC[LE_REFL]) THEN
  INDUCT_TAC THEN REWRITE_TAC[round_maxabs] THEN DISCH_TAC THEN
  BINOP_TAC THENL
   [AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[DIV256_LT; MOD_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let ROUND_INFNORM_VEC_NORM_LT = prove
 (`!k b v. round_infnorm k (\i j. mldsa_modpm (coeff j (v i)) 8380417) < &b <=>
           ~(b = 0) /\ mldsa_vec_norm_lt k b v`,
  REWRITE_TAC[ROUND_INFNORM_LT; mldsa_vec_norm_lt; mldsa_norm_lt] THEN
  REWRITE_TAC[INT_OF_NUM_LT; ARITH_RULE `0 < b <=> ~(b = 0)`] THEN
  MESON_TAC[]);;

(* The comparisons in the form "&0 <= n - b" of the generated rejection      *)
(* tests.                                                                    *)

let ROUND_INFNORM_GE = prove
 (`!k a b. &0 < b
           ==> (&0 <= round_infnorm k a - b <=>
                ~(!i j. i < k /\ j < 256 ==> abs(a i j) < b))`,
  SIMP_TAC[INT_SUB_LE; GSYM INT_NOT_LT; ROUND_INFNORM_LT]);;

let ROUND_INFNORM_VEC_NORM_GE = prove
 (`!k b v. ~(b = 0)
           ==> (&0 <= round_infnorm k
                       (\i j. mldsa_modpm (coeff j (v i)) 8380417) - &b <=>
                ~mldsa_vec_norm_lt k b v)`,
  SIMP_TAC[INT_SUB_LE; GSYM INT_NOT_LT; ROUND_INFNORM_VEC_NORM_LT]);;

(* The loops computing the maximum.                                          *)

let ROUND_MAXLOOP_TAC atm extras =
  MATCH_MP_TAC ROUND_FOLDL2 THEN
  EXISTS_TAC (subst [atm,`a:num->num->int`]
                `\i j. round_maxabs (a:num->num->int) (256 * i + j)`) THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC; ARITH_TAC;
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; round_maxabs];
    REWRITE_TAC[ADD_CLAUSES];
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC(ROUND_STEP_THMS @ extras @
               [ADD_CLAUSES; round_maxabs; DIV_MOD_256_SMALL]) THEN
  AP_TERM_TAC THEN INT_ARITH_TAC;;

let ROUND_NATIVE_FINISH = prove
 (`(!(s:S) (r:S->(R)native_result).
      native_finish (Value (Continue s)) r = r s) /\
   (!(v:R) (s:S) (r:S->(R)native_result).
      native_finish (Value (Return_Value v s)) r = Value v)`,
  REWRITE_TAC[native_finish_DEF; case_native_result_DEF;
              case_statement_outcome_DEF]);;

let ROUND_SLOT_INTVEC_CONG = prove
 (`!s s'. (!i j. i < dimindex(:N) /\ j < 256 ==> s i j = s' i j)
          ==> Native_Assigned
               (lift_vec (\i. lift_intpoly (s i)):
                (N,fips204_intpoly)common_vec) =
              Native_Assigned (lift_vec (\i. lift_intpoly (s' i)))`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC ROUND_INTVEC_CONG THEN
  ASM_REWRITE_TAC[]);;

let round_slot_intvec_rep k =
  round_tm ["KK",string_of_int k]
   "\\s. Native_Assigned
          (lift_vec (\\i. lift_intpoly (s i)):
             (KK,fips204_intpoly)common_vec)";;

let ROUND_MODPM_THMS =
  [LIFT_ZQ_REP; EQ_TYPED_HOL_MOD_PM_NUM; ARITH_EQ; MLDSA_MODPM_REM];;

let round_norm_thms (k,intnorm_def,centered_def,centered_w_ext,rqnorm_def) =
  let tm = round_tm ["KK",string_of_int k] in
  let intnorm = prove
   (tm "!a. IntVectorInfNorm_KK_hol (lift_vec (\\i. lift_intpoly (a i))) =
            Value (round_infnorm KK a)",
    GEN_TAC THEN REWRITE_TAC[intnorm_def; round_infnorm] THEN
    ROUND_MAXLOOP_TAC `a:num->num->int` []) in
  let centered = prove
   (tm "!a m. RqVectorCentered_KK_hol (lift_vec (\\i. lift_poly (a i))) m =
              Value (if m = &8380417
                     then Native_Value
                           (lift_vec (\\i. lift_intpoly
                                       (\\j. mldsa_modpm (a i j) 8380417)))
                     else Native_Bottom)",
    ROUND_UNFOLD_TAC centered_def THEN
    ASM_CASES_TAC `m:int = &8380417` THEN
    ASM_REWRITE_TAC[ROUND_NATIVE_FINISH; centered_w_ext; ETA_AX] THEN
    MATCH_MP_TAC ROUND_BIND_VALUE THEN
    EXISTS_TAC (tm "Native_Assigned
                     (lift_vec (\\i. lift_intpoly
                                 (\\j. mldsa_modpm (a i j) 8380417)):
                      (KK,fips204_intpoly)common_vec)") THEN
    CONJ_TAC THENL
     [ROUND_MAPLOOP_TAC (round_slot_intvec_rep k) ROUND_SLOT_INTVEC_CONG
       ROUND_MODPM_THMS;
      REWRITE_TAC[typed_hol_slot_read_DEF; case_native_slot_DEF;
                  NATIVE_BIND]]) in
  let rqnorm = prove
   (tm "!a. RqVectorInfNorm_KK_hol (lift_vec (\\i. lift_poly (a i))) =
            Value (round_infnorm KK (\\i j. mldsa_modpm (a i j) 8380417))",
    REWRITE_TAC[rqnorm_def; centered; NATIVE_BIND;
                case_native_bottom_DEF; intnorm]) in
  (intnorm,centered,rqnorm);;

let EQ_INTVECTORINFNORM_4,EQ_RQVECTORCENTERED_4,EQ_RQVECTORINFNORM_4 =
  round_norm_thms
   (4,IntVectorInfNorm_4_hol_DEF,RqVectorCentered_4_hol_DEF,
    RqVectorCentered_4_hol_emitted_w_EXT,RqVectorInfNorm_4_hol_DEF);;

let EQ_INTVECTORINFNORM_5,EQ_RQVECTORCENTERED_5,EQ_RQVECTORINFNORM_5 =
  round_norm_thms
   (5,IntVectorInfNorm_5_hol_DEF,RqVectorCentered_5_hol_DEF,
    RqVectorCentered_5_hol_emitted_w_EXT,RqVectorInfNorm_5_hol_DEF);;

let EQ_INTVECTORINFNORM_6,EQ_RQVECTORCENTERED_6,EQ_RQVECTORINFNORM_6 =
  round_norm_thms
   (6,IntVectorInfNorm_6_hol_DEF,RqVectorCentered_6_hol_DEF,
    RqVectorCentered_6_hol_emitted_w_EXT,RqVectorInfNorm_6_hol_DEF);;

let EQ_INTVECTORINFNORM_7,EQ_RQVECTORCENTERED_7,EQ_RQVECTORINFNORM_7 =
  round_norm_thms
   (7,IntVectorInfNorm_7_hol_DEF,RqVectorCentered_7_hol_DEF,
    RqVectorCentered_7_hol_emitted_w_EXT,RqVectorInfNorm_7_hol_DEF);;

let EQ_INTVECTORINFNORM_8,EQ_RQVECTORCENTERED_8,EQ_RQVECTORINFNORM_8 =
  round_norm_thms
   (8,IntVectorInfNorm_8_hol_DEF,RqVectorCentered_8_hol_DEF,
    RqVectorCentered_8_hol_emitted_w_EXT,RqVectorInfNorm_8_hol_DEF);;

(* InfNorm and its body on lists of k polynomials (not called by the         *)
(* generated algorithms, which use the fixed-size forms above).              *)

let EQ_INFNORM = prove
 (`!a k. InfNorm_hol (list_of_seq (\i. lift_poly (a i)) k) =
         Value (round_infnorm k (\i j. mldsa_modpm (a i j) 8380417))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[InfNorm_hol_DEF; LENGTH_LIST_OF_SEQ; ISA_NAT_NUM;
              round_infnorm] THEN
  ROUND_MAXLOOP_TAC `\i j. mldsa_modpm ((a:num->num->int) i j) 8380417`
   ROUND_MODPM_THMS);;

let EQ_INFNORM_BODY = prove
 (`!a k. InfNorm_body_hol
          (list_of_seq (\i. list_of_seq (\j. lift_zq (a i j)) 256) k) =
         Value (round_infnorm k (\i j. mldsa_modpm (a i j) 8380417))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[InfNorm_body_hol_DEF; LENGTH_LIST_OF_SEQ; ISA_NAT_NUM;
              round_infnorm] THEN
  ROUND_MAXLOOP_TAC `\i j. mldsa_modpm ((a:num->num->int) i j) 8380417`
   ROUND_MODPM_THMS);;

(* ------------------------------------------------------------------------- *)
(* The vector functions on lists of k polynomials, VectorHighBits_P,         *)
(* VectorLowBits_P and VectorPower2Round_P, and their _body forms on lists   *)
(* of coefficient lists. The generated algorithms do not call them (they     *)
(* use the FixedVector forms); they hold for every length k.                 *)
(* ------------------------------------------------------------------------- *)

let ROUND_EMPTY_SLICE = prove
 (`!x:A. typed_hol_list_slice (REPLICATE (isa_nat (&0)) x) (&0) (&0) =
         SOME []`,
  REWRITE_TAC[ISA_NAT_NUM; REPLICATE; typed_hol_list_slice_DEF;
              LENGTH; INT_LE_REFL; INT_SUB_REFL; isa_drop; isa_take]);;

let ROUND_ZQLISTS2_CONG = prove
 (`!k s s':num->num->int#int.
        (!i j. i < k /\ j < 256 ==> s i j = s' i j)
        ==> (list_of_seq (\i. list_of_seq (\j. lift_zq (FST(s i j))) 256) k,
             list_of_seq (\i. list_of_seq (\j. lift_zq (SND(s i j))) 256) k) =
            (list_of_seq (\i. list_of_seq (\j. lift_zq (FST(s' i j))) 256) k,
             list_of_seq (\i. list_of_seq (\j. lift_zq (SND(s' i j))) 256) k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THEN
  MATCH_MP_TAC ROUND_ZQLISTS_CONG THEN ASM_SIMP_TAC[]);;

let ROUND_INIT_ZQLISTS2 = prove
 (`!a k. (list_of_seq (\i. list_of_seq (\j. lift_zq (a i j)) 256) k,
          list_of_seq (\i. list_of_seq (\j. lift_zq (a i j)) 256) k) =
         (list_of_seq (\i. list_of_seq (\j. lift_zq
            (FST((\i j. (a i j:int,a i j)) i j))) 256) k,
          list_of_seq (\i. list_of_seq (\j. lift_zq
            (SND((\i j. (a i j:int,a i j)) i j))) 256) k)`,
  REWRITE_TAC[]);;

let ROUND_ZQLISTS_REP =
  `\s. list_of_seq (\i. list_of_seq (\j. lift_zq ((s:num->num->int) i j)) 256)
                   k`;;

let ROUND_ZQLISTS2_REP =
  `\s:num->num->int#int.
     (list_of_seq (\i. list_of_seq (\j. lift_zq (FST(s i j))) 256) k,
      list_of_seq (\i. list_of_seq (\j. lift_zq (SND(s i j))) 256) k)`;;

let ROUND_UNFOLD_LIST_TAC def =
  REPEAT GEN_TAC THEN REWRITE_TAC[def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ROUND_EMPTY_SLICE; TYPED_HOL_READ; NATIVE_BIND;
              LENGTH_LIST_OF_SEQ; ISA_NAT_NUM;
              ROUND_MAP_COEFFS_LIFT_POLY;
              ETA_AX];;

let round_vector_thms
     (p,gamma2,highbits_body_def,highbits_def,lowbits_body_def,lowbits_def,
      power2round_body_def,power2round_def,eq_highbits,eq_lowbits,
      eq_power2round) =
  let tm = round_tm ["PSET",p; "GAMMA2",string_of_int gamma2] in
  let highbits_body = prove
   (tm "!a k. VectorHighBits_PSET_Configuration_body_hol
               (list_of_seq (\\i. list_of_seq (\\j. lift_zq (a i j)) 256) k) =
              Value (list_of_seq (\\i. list_of_seq
                       (\\j. lift_zq (mldsa_highbits GAMMA2 (a i j))) 256) k)",
    ROUND_UNFOLD_LIST_TAC highbits_body_def THEN
    ROUND_MAPLOOP_TAC ROUND_ZQLISTS_REP ROUND_ZQLISTS_CONG [eq_highbits]) in
  let lowbits_body = prove
   (tm "!a k. VectorLowBits_PSET_Configuration_body_hol
               (list_of_seq (\\i. list_of_seq (\\j. lift_zq (a i j)) 256) k) =
              Value (list_of_seq (\\i. list_of_seq
                       (\\j. lift_zq (mldsa_lowbits GAMMA2 (a i j))) 256) k)",
    ROUND_UNFOLD_LIST_TAC lowbits_body_def THEN
    ROUND_MAPLOOP_TAC ROUND_ZQLISTS_REP ROUND_ZQLISTS_CONG [eq_lowbits]) in
  let highbits = prove
   (tm "!a k. VectorHighBits_PSET_Configuration_hol
               (list_of_seq (\\i. lift_poly (a i)) k) =
              Value (list_of_seq (\\i. lift_poly
                       (\\j. mldsa_highbits GAMMA2 (a i j))) k)",
    ROUND_UNFOLD_LIST_TAC highbits_def THEN
    MATCH_MP_TAC ROUND_BIND_VALUE THEN
    EXISTS_TAC (tm "list_of_seq (\\i. list_of_seq
                  (\\j. lift_zq (mldsa_highbits GAMMA2 (a i j))) 256) k") THEN
    CONJ_TAC THENL
     [ROUND_MAPLOOP_TAC ROUND_ZQLISTS_REP ROUND_ZQLISTS_CONG [eq_highbits];
      REWRITE_TAC[ROUND_MAP_FIPS204_POLY]]) in
  let lowbits = prove
   (tm "!a k. VectorLowBits_PSET_Configuration_hol
               (list_of_seq (\\i. lift_poly (a i)) k) =
              Value (list_of_seq (\\i. lift_poly
                       (\\j. mldsa_lowbits GAMMA2 (a i j))) k)",
    ROUND_UNFOLD_LIST_TAC lowbits_def THEN
    MATCH_MP_TAC ROUND_BIND_VALUE THEN
    EXISTS_TAC (tm "list_of_seq (\\i. list_of_seq
                    (\\j. lift_zq (mldsa_lowbits GAMMA2 (a i j))) 256) k") THEN
    CONJ_TAC THENL
     [ROUND_MAPLOOP_TAC ROUND_ZQLISTS_REP ROUND_ZQLISTS_CONG [eq_lowbits];
      REWRITE_TAC[ROUND_MAP_FIPS204_POLY]]) in
  let power2round_body = prove
   (tm "!a k. VectorPower2Round_PSET_Configuration_body_hol
               (list_of_seq (\\i. list_of_seq (\\j. lift_zq (a i j)) 256) k) =
              Value (list_of_seq (\\i. list_of_seq
                       (\\j. lift_zq (FST(mldsa_power2round (a i j)))) 256) k,
                     list_of_seq (\\i. list_of_seq
                      (\\j. lift_zq (SND(mldsa_power2round (a i j)))) 256) k)",
    ROUND_UNFOLD_LIST_TAC power2round_body_def THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ROUND_INIT_ZQLISTS2] THEN
    ROUND_MAPLOOP_TAC ROUND_ZQLISTS2_REP ROUND_ZQLISTS2_CONG
     [eq_power2round] THEN
    REWRITE_TAC[COND_RAND]) in
  let power2round = prove
   (tm "!a k. VectorPower2Round_PSET_Configuration_hol
               (list_of_seq (\\i. lift_poly (a i)) k) =
              Value (list_of_seq (\\i. lift_poly
                       (\\j. FST(mldsa_power2round (a i j)))) k,
                     list_of_seq (\\i. lift_poly
                       (\\j. SND(mldsa_power2round (a i j)))) k)",
    ROUND_UNFOLD_LIST_TAC power2round_def THEN
    MATCH_MP_TAC ROUND_BIND_VALUE THEN
    EXISTS_TAC (tm "list_of_seq (\\i. list_of_seq
                      (\\j. lift_zq (FST(mldsa_power2round (a i j)))) 256) k,
                    list_of_seq (\\i. list_of_seq
                      (\\j. lift_zq (SND(mldsa_power2round (a i j)))) 256) k")
    THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ROUND_INIT_ZQLISTS2] THEN
      ROUND_MAPLOOP_TAC ROUND_ZQLISTS2_REP ROUND_ZQLISTS2_CONG
       [eq_power2round] THEN
      REWRITE_TAC[COND_RAND];
      REWRITE_TAC[UNCURRY_DEF; ROUND_MAP_FIPS204_POLY]]) in
  (highbits_body,highbits,lowbits_body,lowbits,power2round_body,power2round);;

let (EQ_VECTORHIGHBITS_BODY_MLDSA44,EQ_VECTORHIGHBITS_MLDSA44,
     EQ_VECTORLOWBITS_BODY_MLDSA44,EQ_VECTORLOWBITS_MLDSA44,
     EQ_VECTORPOWER2ROUND_BODY_MLDSA44,EQ_VECTORPOWER2ROUND_MLDSA44) =
  round_vector_thms
   ("MLDSA44",95232,
    VectorHighBits_MLDSA44_Configuration_body_hol_DEF,
    VectorHighBits_MLDSA44_Configuration_hol_DEF,
    VectorLowBits_MLDSA44_Configuration_body_hol_DEF,
    VectorLowBits_MLDSA44_Configuration_hol_DEF,
    VectorPower2Round_MLDSA44_Configuration_body_hol_DEF,
    VectorPower2Round_MLDSA44_Configuration_hol_DEF,
    EQ_HIGHBITS_MLDSA44,EQ_LOWBITS_MLDSA44,EQ_POWER2ROUND_MLDSA44);;

let (EQ_VECTORHIGHBITS_BODY_MLDSA65,EQ_VECTORHIGHBITS_MLDSA65,
     EQ_VECTORLOWBITS_BODY_MLDSA65,EQ_VECTORLOWBITS_MLDSA65,
     EQ_VECTORPOWER2ROUND_BODY_MLDSA65,EQ_VECTORPOWER2ROUND_MLDSA65) =
  round_vector_thms
   ("MLDSA65",261888,
    VectorHighBits_MLDSA65_Configuration_body_hol_DEF,
    VectorHighBits_MLDSA65_Configuration_hol_DEF,
    VectorLowBits_MLDSA65_Configuration_body_hol_DEF,
    VectorLowBits_MLDSA65_Configuration_hol_DEF,
    VectorPower2Round_MLDSA65_Configuration_body_hol_DEF,
    VectorPower2Round_MLDSA65_Configuration_hol_DEF,
    EQ_HIGHBITS_MLDSA65,EQ_LOWBITS_MLDSA65,EQ_POWER2ROUND_MLDSA65);;

let (EQ_VECTORHIGHBITS_BODY_MLDSA87,EQ_VECTORHIGHBITS_MLDSA87,
     EQ_VECTORLOWBITS_BODY_MLDSA87,EQ_VECTORLOWBITS_MLDSA87,
     EQ_VECTORPOWER2ROUND_BODY_MLDSA87,EQ_VECTORPOWER2ROUND_MLDSA87) =
  round_vector_thms
   ("MLDSA87",261888,
    VectorHighBits_MLDSA87_Configuration_body_hol_DEF,
    VectorHighBits_MLDSA87_Configuration_hol_DEF,
    VectorLowBits_MLDSA87_Configuration_body_hol_DEF,
    VectorLowBits_MLDSA87_Configuration_hol_DEF,
    VectorPower2Round_MLDSA87_Configuration_body_hol_DEF,
    VectorPower2Round_MLDSA87_Configuration_hol_DEF,
    EQ_HIGHBITS_MLDSA87,EQ_LOWBITS_MLDSA87,EQ_POWER2ROUND_MLDSA87);;

(* ------------------------------------------------------------------------- *)
(* The local norm functions of ML_DSA_Sign_internal and ML_DSA_Sign_internal *)
(* _mu: callable_1_0 is RqVectorCentered on Native_Value v, for vectors of l *)
(* polynomials, and callable_3_0 the infinity norm through it.               *)
(* ------------------------------------------------------------------------- *)

let round_sign_norm_thms (name,p,k,c1_def,c1_w_ext,c3_def,eq_intnorm) =
  let tm = round_tm ["NAME",name; "PSET",p; "KK",string_of_int k] in
  let c1 = prove
   (tm "!a m. NAME_PSET_Configuration_callable_1_0_call
                (Native_Value (lift_vec (\\i. lift_poly (a i)))) m =
              Value (if m = &8380417
                     then Native_Value
                           (lift_vec (\\i. lift_intpoly
                                       (\\j. mldsa_modpm (a i j) 8380417)))
                     else Native_Bottom)",
    ROUND_UNFOLD_TAC c1_def THEN
    ASM_CASES_TAC `m:int = &8380417` THEN
    ASM_REWRITE_TAC[ROUND_NATIVE_FINISH; c1_w_ext; ETA_AX] THEN
    MATCH_MP_TAC ROUND_BIND_VALUE THEN
    EXISTS_TAC (tm "Native_Assigned
                     (lift_vec (\\i. lift_intpoly
                                 (\\j. mldsa_modpm (a i j) 8380417)):
                      (KK,fips204_intpoly)common_vec)") THEN
    CONJ_TAC THENL
     [ROUND_MAPLOOP_TAC (round_slot_intvec_rep k) ROUND_SLOT_INTVEC_CONG
       (ROUND_MODPM_THMS @
        [case_native_bottom_DEF; typed_hol_bottom_index_DEF]);
      REWRITE_TAC[typed_hol_slot_read_DEF; case_native_slot_DEF;
                  NATIVE_BIND]]) in
  let c3 = prove
   (tm "!a. NAME_PSET_Configuration_callable_3_0_call
              (Native_Value (lift_vec (\\i. lift_poly (a i)))) =
            Value (round_infnorm KK (\\i j. mldsa_modpm (a i j) 8380417))",
    REWRITE_TAC[c3_def; c1; NATIVE_BIND; case_native_bottom_DEF;
                eq_intnorm]) in
  (c1,c3);;

let EQ_SIGN_INTERNAL_CALLABLE_1_0_MLDSA44,
    EQ_SIGN_INTERNAL_CALLABLE_3_0_MLDSA44 =
  round_sign_norm_thms
   ("ML_DSA_Sign_internal","MLDSA44",4,
    ML_DSA_Sign_internal_MLDSA44_Configuration_callable_1_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA44_Configuration_callable_1_0_emitted_w_EXT,
    ML_DSA_Sign_internal_MLDSA44_Configuration_callable_3_0_call_DEF,
    EQ_INTVECTORINFNORM_4);;

let EQ_SIGN_INTERNAL_CALLABLE_1_0_MLDSA65,
    EQ_SIGN_INTERNAL_CALLABLE_3_0_MLDSA65 =
  round_sign_norm_thms
   ("ML_DSA_Sign_internal","MLDSA65",5,
    ML_DSA_Sign_internal_MLDSA65_Configuration_callable_1_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA65_Configuration_callable_1_0_emitted_w_EXT,
    ML_DSA_Sign_internal_MLDSA65_Configuration_callable_3_0_call_DEF,
    EQ_INTVECTORINFNORM_5);;

let EQ_SIGN_INTERNAL_CALLABLE_1_0_MLDSA87,
    EQ_SIGN_INTERNAL_CALLABLE_3_0_MLDSA87 =
  round_sign_norm_thms
   ("ML_DSA_Sign_internal","MLDSA87",7,
    ML_DSA_Sign_internal_MLDSA87_Configuration_callable_1_0_call_DEF,
    ML_DSA_Sign_internal_MLDSA87_Configuration_callable_1_0_emitted_w_EXT,
    ML_DSA_Sign_internal_MLDSA87_Configuration_callable_3_0_call_DEF,
    EQ_INTVECTORINFNORM_7);;

let EQ_SIGN_INTERNAL_MU_CALLABLE_1_0_MLDSA44,
    EQ_SIGN_INTERNAL_MU_CALLABLE_3_0_MLDSA44 =
  round_sign_norm_thms
   ("ML_DSA_Sign_internal_mu","MLDSA44",4,
    ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_1_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_1_0_emitted_w_EXT,
    ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_3_0_call_DEF,
    EQ_INTVECTORINFNORM_4);;

let EQ_SIGN_INTERNAL_MU_CALLABLE_1_0_MLDSA65,
    EQ_SIGN_INTERNAL_MU_CALLABLE_3_0_MLDSA65 =
  round_sign_norm_thms
   ("ML_DSA_Sign_internal_mu","MLDSA65",5,
    ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_1_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_1_0_emitted_w_EXT,
    ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_3_0_call_DEF,
    EQ_INTVECTORINFNORM_5);;

let EQ_SIGN_INTERNAL_MU_CALLABLE_1_0_MLDSA87,
    EQ_SIGN_INTERNAL_MU_CALLABLE_3_0_MLDSA87 =
  round_sign_norm_thms
   ("ML_DSA_Sign_internal_mu","MLDSA87",7,
    ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_1_0_call_DEF,
    ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_1_0_emitted_w_EXT,
    ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_3_0_call_DEF,
    EQ_INTVECTORINFNORM_7);;
