(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the generated ML_DSA_KeyGen_internal agrees with the      *)
(* handwritten mldsa_keygen_internal of common/fips204/fips204.ml, for ML-   *)
(* DSA-44, -65 and -87, under xof_ok and LENGTH xi = 32 (statement           *)
(* STMT_KEYGEN_ INTERNAL of toplevel.ml).                                    *)
(*                                                                           *)
(* Method. toplevel.ml proves the abstract lemmas TOP_KEYGEN_ABSTRACT_44/65/87:   *)
(* the result of KeyGen_internal is (PK,SK) once one Value-equation holds    *)
(* for each component call. Here each equation is instantiated with the      *)
(* equivalence lemma of its component (ExpandA, ExpandS, IntVectorNTT,       *)
(* MatrixVectorNTT, VectorNTTInv, RqIntVectorAdd, FixedVectorPower2Round,    *)
(* pkEncode, HBytesString, skEncode, HBytes), by forward chaining with       *)
(* MATCH_MP. The lifted forms are bridged by small lemmas:                   *)
(*  - ExpandS gives lift_intpoly of the centered representatives             *)
(*    mldsa_modpm (coeff j s) q; mldsa_poly of them is s (WK_POLY_MODPM)     *)
(*    and they are in [-eta,eta] (WK_RBP_RANGE_2/4);                         *)
(*  - ExpandA gives the NTT-domain matrix mldsa_ntt (mldsa_expand_a rho i j);*)
(*    mldsa_ntt_inv (mldsa_ntt a) = a recovers the time-domain matrix of the *)
(*    handwritten code (WK_EXPA_IN_RQ), so the product A * s1 is the         *)
(*    handwritten mldsa_dot (WK_MVINV_nn);                                   *)
(*  - t = A s1 + s2 is computed in Z (coeff k (dot) + modpm (coeff k s2)),   *)
(*    not reduced; it agrees with coeff k (ring_add ..) modulo q, and        *)
(*    Power2Round only depends on the residue (WK_T_EQ);                     *)
(*  - Power2Round results are in the ranges pkEncode/skEncode need           *)
(*    (WK_P2R_RANGE).                                                        *)
(* No assumptions beyond xof_ok and LENGTH xi = 32 remain.                   *)
(*                                                                           *)
(* Load after base.ml and common.ml.                                   *)
(* ========================================================================= *)

needs "common/fips204/generated/core/core.ml";;
needs "common/fips204/generated/core/rounding.ml";;
needs "common/fips204/generated/core/sample.ml";;
needs "common/fips204/generated/core/ball.ml";;
needs "common/fips204/generated/core/encode.ml";;
needs "common/fips204/generated/core/ntt.ml";;
needs "common/fips204/generated/core/ntt_vec.ml";;
needs "common/fips204/generated/core/toplevel.ml";;

(* parameters                                                                *)
let wk_params p =
  match p with
    "44" -> ["@P@","MLDSA44"; "@HW@","mldsa44"; "@K@","4"; "@L@","4";
             "@ETA@","2"; "@C@","3"]
  | "65" -> ["@P@","MLDSA65"; "@HW@","mldsa65"; "@K@","6"; "@L@","5";
             "@ETA@","4"; "@C@","4"]
  | "87" -> ["@P@","MLDSA87"; "@HW@","mldsa87"; "@K@","8"; "@L@","7";
             "@ETA@","2"; "@C@","3"]
  | _ -> failwith "wk_params";;

let wk_tm p s = parse_term (top_subst (wk_params p) s);;

(* GEN all free variables, to use MATCH_MP                                   *)
let wk_gen th = GENL (subtract (frees (concl th)) (freesl (hyp th))) th;;

let WK_SEEDS = prove
 (`!(s:byte list). LENGTH s = 128
    ==> APPEND (mldsa_slice 0 32 s)
         (APPEND (mldsa_slice 32 64 s) (mldsa_slice 96 32 s)) = s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_APPEND; LENGTH_MLDSA_SLICE] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[EL_APPEND; LENGTH_MLDSA_SLICE] THEN
  ASM_CASES_TAC `i < 32` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[EL_MLDSA_SLICE; ADD_CLAUSES]; ALL_TAC] THEN
  ASM_CASES_TAC `i - 32 < 64` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[EL_MLDSA_SLICE] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    SUBGOAL_THEN `i - 32 - 64 < 32` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MLDSA_SLICE] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC]);;

let WK_POLY_MODPM = prove
 (`!y. y IN ring_carrier mldsa_rq
       ==> mldsa_poly (\j. mldsa_modpm (coeff j y) 8380417) = y`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLDSA_POLY_EQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`coeff i (y:(1->num)->int)`; `8380417`] MLDSA_MODPM) THEN
  ANTS_TAC THENL [ARITH_TAC; SIMP_TAC[]]);;

let WK_P2R_CONG = prove
 (`!x y. (x == y) (mod &8380417)
         ==> mldsa_power2round x = mldsa_power2round y`,
  REWRITE_TAC[GSYM INT_REM_EQ; mldsa_power2round] THEN SIMP_TAC[]);;

let WK_P2R_RANGE = prove
 (`!r. &0 <= FST(mldsa_power2round r) /\ FST(mldsa_power2round r) <= &1023 /\
       --(&4095) <= SND(mldsa_power2round r) /\
       SND(mldsa_power2round r) <= &4096`,
  GEN_TAC THEN REWRITE_TAC[mldsa_power2round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= r rem &8380417 /\ r rem &8380417 < &8380417` MP_TAC THENL
   [REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
    CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
  SPEC_TAC(`r rem &8380417`,`rp:int`) THEN GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`rp:int`; `8192`] MLDSA_MODPM) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`mldsa_modpm rp 8192`,`r0:int`) THEN GEN_TAC THEN
  REWRITE_TAC[int_congruent; int_divides] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `d:int`) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(rp - r0) div &8192 = --d` SUBST1_TAC THENL
   [MATCH_MP_TAC INT_DIV_UNIQ THEN EXISTS_TAC `&0:int` THEN
    ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN ASM_INT_ARITH_TAC);;

let WK_RBP_RANGE_2 = prove
 (`!rho j. LENGTH rho < 135
        ==> --(&2) <= mldsa_modpm (coeff j (mldsa_rej_bounded_poly 2 rho)) 8380417 /\
            mldsa_modpm (coeff j (mldsa_rej_bounded_poly 2 rho)) 8380417 <= &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[mldsa_rej_bounded_poly] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[COEFF_MLDSA_POLY; ARITH_EQ] THEN
  ASM_CASES_TAC `j < 256` THENL [ALL_TAC;
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mldsa_modpm (&0) 8380417 = &0` SUBST1_TAC THENL
     [REWRITE_TAC[mldsa_modpm] THEN CONV_TAC INT_REDUCE_CONV;
      INT_ARITH_TAC]] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`2`; `rho:byte list`; `j + 1`]
    MLDSA_REJ_BOUNDED_POLY_TERMINATES) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN DISCH_THEN(X_CHOOSE_TAC `J:num`) THEN
  MP_TAC(ISPECL
   [`\t. (val(shake256 rho (t DIV 2)) DIV 16 EXP (t MOD 2)) MOD 16 < 15`;
    `J:num`; `j:num`] SAMP_COUNT_EXISTS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SELECT_RULE o
    MATCH_MP (MESON[] `(?j. j < J /\ P j) ==> (?j. P j)`)) THEN
  W(fun (_,w) -> SPEC_TAC(find_term is_select w,`t:num`)) THEN
  GEN_TAC THEN STRIP_TAC THEN
  SPEC_TAC(`(val (shake256 rho (t DIV 2)) DIV 16 EXP (t MOD 2)) MOD 16`,
           `b:num`) THEN
  GEN_TAC THEN
  SUBGOAL_THEN `abs(&2 - &(b MOD 5):int) <= &4190208` MP_TAC THENL
   [REWRITE_TAC[SAMP_ABS_ETA2]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP SAMP_MODPM_REM th]) THEN
  MP_TAC(SPECL [`b:num`; `5`] MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ; GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE] THEN
  INT_ARITH_TAC);;

let WK_RBP_RANGE_4 = prove
 (`!rho j. LENGTH rho < 135
        ==> --(&4) <= mldsa_modpm (coeff j (mldsa_rej_bounded_poly 4 rho)) 8380417 /\
            mldsa_modpm (coeff j (mldsa_rej_bounded_poly 4 rho)) 8380417 <= &4`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[mldsa_rej_bounded_poly] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[COEFF_MLDSA_POLY; ARITH_EQ] THEN
  ASM_CASES_TAC `j < 256` THENL [ALL_TAC;
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mldsa_modpm (&0) 8380417 = &0` SUBST1_TAC THENL
     [REWRITE_TAC[mldsa_modpm] THEN CONV_TAC INT_REDUCE_CONV;
      INT_ARITH_TAC]] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`4`; `rho:byte list`; `j + 1`]
    MLDSA_REJ_BOUNDED_POLY_TERMINATES) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN DISCH_THEN(X_CHOOSE_TAC `J:num`) THEN
  MP_TAC(ISPECL
   [`\t. (val(shake256 rho (t DIV 2)) DIV 16 EXP (t MOD 2)) MOD 16 < 9`;
    `J:num`; `j:num`] SAMP_COUNT_EXISTS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SELECT_RULE o
    MATCH_MP (MESON[] `(?j. j < J /\ P j) ==> (?j. P j)`)) THEN
  W(fun (_,w) -> SPEC_TAC(find_term is_select w,`t:num`)) THEN
  GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(val (shake256 rho (t DIV 2)) DIV 16 EXP (t MOD 2)) MOD 16 < 9` THEN
  SPEC_TAC(`(val (shake256 rho (t DIV 2)) DIV 16 EXP (t MOD 2)) MOD 16`,
           `b:num`) THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(&4 - &b:int) <= &4190208` MP_TAC THENL
   [MATCH_MP_TAC SAMP_ABS_ETA4 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP SAMP_MODPM_REM th]) THEN
  UNDISCH_TAC `b < 9` THEN REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
  INT_ARITH_TAC);;


let WK_CONG_ADD = prove
 (`!a m b r n:int. (m == b) (mod n) /\ (r == a + b) (mod n)
                   ==> (a + m == r) (mod n)`,
  CONV_TAC INTEGER_RULE);;

let WK_T_EQ = prove
 (`!d s k. d IN ring_carrier mldsa_rq /\ s IN ring_carrier mldsa_rq
           ==> mldsa_power2round (coeff k d + mldsa_modpm (coeff k s) 8380417) =
               mldsa_power2round (coeff k (ring_add mldsa_rq d s))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLDSA_RQ_COEFF_ADD] THEN
  MATCH_MP_TAC WK_P2R_CONG THEN MATCH_MP_TAC WK_CONG_ADD THEN
  EXISTS_TAC `coeff k (s:(1->num)->int)` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`coeff k (s:(1->num)->int)`; `8380417`] MLDSA_MODPM) THEN
    ANTS_TAC THENL [ARITH_TAC; SIMP_TAC[]];
    MP_TAC(ISPECL [`coeff k (d:(1->num)->int) + coeff k (s:(1->num)->int)`;
                   `&8380417:int`] INT_REM_MOD_SELF) THEN
    SIMP_TAC[INT_ADD_SYM]]);;

let WK_EXPA_IN_RQ = prove
 (`!rho i j. LENGTH rho = 32 ==> mldsa_expand_a rho i j IN ring_carrier mldsa_rq`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_expand_a] THEN
  MP_TAC(ISPEC `mldsa_rej_ntt_poly (APPEND rho [word j; word i])`
    MLDSA_NTT_INV) THEN
  ANTS_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MLDSA_REJ_NTT_POLY_RANGE THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC;
    SIMP_TAC[]]);;

let WK_LEN = prove
 (`!r:byte list n. LENGTH r = 64
                   ==> LENGTH (APPEND r (bytelist_of_num 2 n)) < 135`,
  SIMP_TAC[LENGTH_APPEND; SAMP_LENGTH_BYTELIST] THEN ARITH_TAC);;

let WK_S_RANGE_2 = prove
 (`!rg:byte list n j. LENGTH rg = 64
    ==> --(&2) <= mldsa_modpm (coeff j (mldsa_rej_bounded_poly 2
                   (APPEND rg (bytelist_of_num 2 n)))) 8380417 /\
        mldsa_modpm (coeff j (mldsa_rej_bounded_poly 2
                   (APPEND rg (bytelist_of_num 2 n)))) 8380417 <= &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC WK_RBP_RANGE_2 THEN
  ASM_SIMP_TAC[WK_LEN]);;

let WK_S_RANGE_4 = prove
 (`!rg:byte list n j. LENGTH rg = 64
    ==> --(&4) <= mldsa_modpm (coeff j (mldsa_rej_bounded_poly 4
                   (APPEND rg (bytelist_of_num 2 n)))) 8380417 /\
        mldsa_modpm (coeff j (mldsa_rej_bounded_poly 4
                   (APPEND rg (bytelist_of_num 2 n)))) 8380417 <= &4`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC WK_RBP_RANGE_4 THEN
  ASM_SIMP_TAC[WK_LEN]);;

(* ------------------------------------------------------------------------- *)
(* The product A * s1 followed by NTT^-1, from the NTT-domain inputs, as in  *)
(* EQ_MATVEC_NTTINV_* of ntt.ml without the forward NTT of s1.               *)
(* ------------------------------------------------------------------------- *)

let wk_mvinv_gen p mvth vinvth =
  let tm = wk_tm p in
  prove(tm
   "!a y. (!i j k. i < @K@ /\\ j < @L@ /\\ k < 256
                   ==> &0 <= a i j k /\\ a i j k < &8380417) /\\
          (!j. j < @L@ ==> y j IN ring_carrier mldsa_rq)
          ==> native_bind
               (MatrixVectorNTT_@K@_@L@_@P@_Configuration_hol
                 (Common_Mat (lift_mat (\\i j. lift_poly (a i j))))
                 (lift_vec (\\j. lift_poly (mldsa_ntt (y j)))))
               VectorNTTInv_@K@_@P@_Configuration_hol =
              Value (lift_vec
                      (\\i. lift_poly
                            (\\k. coeff k (mldsa_dot @L@
                                   (\\j. mldsa_ntt_inv (a i j)) y))))",
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[mvth; NATIVE_BIND_VALUE] THEN
   MP_TAC(SPEC (tm "\\i q. ntt_msum @L@ (\\j. (a:num->num->num->int) i j q *
                                      mldsa_ntt ((y:num->(1->num)->int) j) q)
                      rem &8380417") vinvth) THEN
   REWRITE_TAC[NTT_REM_RANGE; NTT_LIFT_POLY_REM] THEN
   DISCH_THEN SUBST1_TAC THEN
   AP_TERM_TAC THEN MATCH_MP_TAC LIFT_VEC_CONG THEN
   REWRITE_TAC NTT_DIMS THEN REPEAT STRIP_TAC THEN
   AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
   MP_TAC(SPECL [tm "@L@"; `(a:num->num->num->int) i`;
                 `y:num->(1->num)->int`] NTT_DOT_ROW) THEN
   ASM_SIMP_TAC[]);;

let WK_MVINV_44 = wk_mvinv_gen "44" EQ_MATRIXVECTORNTT_4_4_MLDSA44 EQ_VECTORNTTINV_4_MLDSA44;;
let WK_MVINV_65 = wk_mvinv_gen "65" EQ_MATRIXVECTORNTT_6_5_MLDSA65 EQ_VECTORNTTINV_6_MLDSA65;;
let WK_MVINV_87 = wk_mvinv_gen "87" EQ_MATRIXVECTORNTT_8_7_MLDSA87 EQ_VECTORNTTINV_8_MLDSA87;;

let wk_names p =
  match p with
    "44" -> (TOP_KEYGEN_ABSTRACT_44, EQ_INTVECTORNTT_4, EQ_MATRIXVECTORNTT_4_4_MLDSA44,
             EQ_RQINTVECTORADD_4, EQ_FIXEDVECTORPOWER2ROUND_4_MLDSA44,
             EQ_PKENCODE_MLDSA44, EQ_SKENCODE_MLDSA44, EQ_EXPANDA_NTT_MLDSA44,
             EQ_EXPANDS_MLDSA44, WK_MVINV_44, WK_S_RANGE_2)
  | "65" -> (TOP_KEYGEN_ABSTRACT_65, EQ_INTVECTORNTT_5, EQ_MATRIXVECTORNTT_6_5_MLDSA65,
             EQ_RQINTVECTORADD_6, EQ_FIXEDVECTORPOWER2ROUND_6_MLDSA65,
             EQ_PKENCODE_MLDSA65, EQ_SKENCODE_MLDSA65, EQ_EXPANDA_NTT_MLDSA65,
             EQ_EXPANDS_MLDSA65, WK_MVINV_65, WK_S_RANGE_4)
  | "87" -> (TOP_KEYGEN_ABSTRACT_87, EQ_INTVECTORNTT_7, EQ_MATRIXVECTORNTT_8_7_MLDSA87,
             EQ_RQINTVECTORADD_8, EQ_FIXEDVECTORPOWER2ROUND_8_MLDSA87,
             EQ_PKENCODE_MLDSA87, EQ_SKENCODE_MLDSA87, EQ_EXPANDA_NTT_MLDSA87,
             EQ_EXPANDS_MLDSA87, WK_MVINV_87, WK_S_RANGE_2)
  | _ -> failwith "wk_names";;

(* ------------------------------------------------------------------------- *)
(* The chain of the component equations. Result: a theorem with hypotheses   *)
(* xof_ok, lengths and the equation of the seed, whose conclusion is         *)
(* KeyGen_internal xs = Value (PK, SK) with PK, SK in the explicit forms     *)
(* of the component lemmas. The variables are named xs, rh (rho), rg (rho'), *)
(* ky (key) so that they differ from the variables of the abstract lemma.    *)
(* ------------------------------------------------------------------------- *)

let wk_chain p =
  let tm = wk_tm p in
  let (abs,intvntt,mvth,rqadd,p2rth,pkth,skth,expath,expsth,mvinv,srange) =
    wk_names p in
  let th0 = wk_gen (REWRITE_RULE[GSYM IMP_IMP] abs) in
  let hx = ASSUME `xof_ok`
  and hxs = ASSUME `LENGTH (xs:byte list) = 32`
  and hr = ASSUME `LENGTH (rh:byte list) = 32`
  and hr' = ASSUME `LENGTH (rg:byte list) = 64`
  and hk = ASSUME `LENGTH (ky:byte list) = 32`
  and hs = ASSUME (tm "mldsa_h (APPEND xs [word @K@; word @L@]) 128 =
                       APPEND rh (APPEND rg ky)") in
  let ib kn = MP (SPEC (tm kn) INTEGER_TO_BYTES_1_NUM)
                 (EQT_ELIM(NUM_REDUCE_CONV (tm (kn ^ " < 256")))) in
  let th1 = if p = "44" then MATCH_MP th0 (ib "@K@")
            else MATCH_MP (MATCH_MP th0 (ib "@K@")) (ib "@L@") in
  (* H(xi || k || l, 128) *)
  let strt = tm "APPEND (APPEND xs [word @K@]) [word @L@]:byte list" in
  let len_str = EQT_ELIM((REWRITE_CONV[LENGTH_APPEND;LENGTH;hxs] THENC
                          NUM_REDUCE_CONV)
                          (mk_eq(mk_comb(`LENGTH:byte list->num`,strt),`34`))) in
  let b34 = MP (SPEC strt ENC_BYTES_TO_BITS_34) len_str in
  let hb0 = SPEC `128` (MP (SPEC strt (wk_gen EQ_HBYTES_34))
                           (CONJ hx (CONJ len_str b34))) in
  let hseed = prove(tm "mldsa_h (APPEND (APPEND xs [word @K@]) [word @L@]) 128 =
                        mldsa_h (APPEND xs [word @K@; word @L@]) 128",
                    REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]) in
  let hb = REWRITE_RULE[hseed; hs] hb0 in
  let th2 = MATCH_MP th1 hb in
  let th3 = MATCH_MP th2 (REFL (rand (concl hs))) in
  let th4 = MATCH_MP (MATCH_MP (MATCH_MP th3 hr) hr') hk in
  (* ExpandA, ExpandS *)
  let a_th = MP (SPEC `rh:byte list` expath) (CONJ hx hr) in
  let s_th = MP (SPEC `rg:byte list` expsth) (CONJ hx hr') in
  let th5 = MATCH_MP (MATCH_MP th4 a_th) s_th in
  (* S1 -> NTT *)
  let nt_th = SIMP_RULE[WK_POLY_MODPM; MLDSA_REJ_BOUNDED_POLY_IN_RQ]
    (BETA_RULE (ISPEC (tm "\\i j. mldsa_modpm (coeff j (mldsa_rej_bounded_poly
                   @ETA@ (APPEND rg (bytelist_of_num 2 i)))) 8380417") intvntt)) in
  let th6 = MATCH_MP th5 nt_th in
  (* A * s1, NTT^-1 *)
  let ya = tm "\\j. mldsa_rej_bounded_poly @ETA@ (APPEND rg (bytelist_of_num 2 j))" in
  let mv_th = BETA_RULE (ISPECL
    [`\i j. mldsa_ntt (mldsa_expand_a rh i j)`;
     tm "\\j. mldsa_ntt (mldsa_rej_bounded_poly @ETA@ (APPEND rg (bytelist_of_num 2 j)))"]
    mvth) in
  let inv0b = BETA_RULE (ISPECL [`\i j. mldsa_ntt (mldsa_expand_a rh i j)`; ya] mvinv) in
  let inv1 = MP inv0b (prove(fst(dest_imp(concl inv0b)),
    CONJ_TAC THEN MESON_TAC[MLDSA_NTT_BOUND; MLDSA_REJ_BOUNDED_POLY_IN_RQ])) in
  let inv2 = REWRITE_RULE[mv_th; NATIVE_BIND_VALUE] inv1 in
  let hexpa = MATCH_MP WK_EXPA_IN_RQ hr in
  let inv3 = SIMP_RULE[MLDSA_NTT_INV_NTT; hexpa] inv2 in
  let th7 = MATCH_MP (MATCH_MP th6 mv_th) inv3 in
  (* t = A s1 + s2 *)
  let add_th = BETA_RULE (ISPECL
    [tm "\\i k. coeff k (mldsa_dot @L@ (\\j. mldsa_expand_a rh i j) (\\j. mldsa_rej_bounded_poly @ETA@ (APPEND rg (bytelist_of_num 2 j))))";
     tm "\\i j. mldsa_modpm (coeff j (mldsa_rej_bounded_poly @ETA@ (APPEND rg (bytelist_of_num 2 (@L@ + i))))) 8380417"]
    rqadd) in
  let th8 = MATCH_MP th7 add_th in
  let ttf = tm "\\i j. coeff j (mldsa_dot @L@ (\\j. mldsa_expand_a rh i j) (\\j. mldsa_rej_bounded_poly @ETA@ (APPEND rg (bytelist_of_num 2 j)))) + mldsa_modpm (coeff j (mldsa_rej_bounded_poly @ETA@ (APPEND rg (bytelist_of_num 2 (@L@ + i))))) 8380417" in
  let p2r_th = BETA_RULE (ISPEC (tm "\\i k. coeff k (mldsa_dot @L@ (\\j. mldsa_expand_a rh i j) (\\j. mldsa_rej_bounded_poly @ETA@ (APPEND rg (bytelist_of_num 2 j)))) + mldsa_modpm (coeff k (mldsa_rej_bounded_poly @ETA@ (APPEND rg (bytelist_of_num 2 (@L@ + i))))) 8380417") p2rth) in
  let th9 = MATCH_MP th8 p2r_th in
  (* pkEncode *)
  let t1f = mk_abs(`i:num`, mk_abs(`j:num`, mk_comb(`FST:int#int->int`,
              mk_comb(`mldsa_power2round`, list_mk_comb(ttf,[`i:num`;`j:num`]))))) in
  let t0f = mk_abs(`i:num`, mk_abs(`j:num`, mk_comb(`SND:int#int->int`,
              mk_comb(`mldsa_power2round`, list_mk_comb(ttf,[`i:num`;`j:num`]))))) in
  let pk0 = BETA_RULE (ISPECL [`rh:byte list`; t1f] pkth) in
  let pk1 = MP pk0 (CONJ hr (prove(snd(dest_conj(fst(dest_imp(concl pk0)))),
                                   MESON_TAC[WK_P2R_RANGE]))) in
  let th10 = MATCH_MP th9 pk1 in
  let pkx = rand(rand(concl pk1)) in
  let tr0 = SPEC `64` (MP (SPEC pkx (wk_gen EQ_HBYTESSTRING))
                          (CONJ hx (SPEC pkx BALL_BYTES_TO_BITS_STRING))) in
  let th11 = MATCH_MP th10 tr0 in
  let hr_trx = SPECL [pkx; `64`] BALL_LENGTH_MLDSA_H in
  let th12 = MATCH_MP th11 hr_trx in
  (* skEncode *)
  let s1f = tm "\\i j. mldsa_modpm (coeff j (mldsa_rej_bounded_poly @ETA@ (APPEND rg (bytelist_of_num 2 i)))) 8380417" in
  let s2f = tm "\\i j. mldsa_modpm (coeff j (mldsa_rej_bounded_poly @ETA@ (APPEND rg (bytelist_of_num 2 (@L@ + i))))) 8380417" in
  let trx = mk_comb(mk_comb(`mldsa_h`,pkx),`64`) in
  let sk0 = BETA_RULE (ISPECL [`rh:byte list`; `ky:byte list`; trx; s1f; s2f; t0f] skth) in
  let sk_cs = conjuncts(fst(dest_imp(concl sk0))) in
  let sk_rng = prove(mk_imp(`LENGTH (rg:byte list) = 64`,
                            list_mk_conj(tl(tl(tl sk_cs)))),
     DISCH_TAC THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
     ASM_SIMP_TAC[srange; WK_P2R_RANGE]) in
  let sk1 = MP sk0 (CONJ hr (CONJ hk (CONJ hr_trx (MP sk_rng hr')))) in
  MATCH_MP th12 sk1;;

(* ------------------------------------------------------------------------- *)
(* The explicit (PK,SK) is mldsa_keygen_internal.                            *)
(* ------------------------------------------------------------------------- *)

let wk_eq p pksk =
  let tm = wk_tm p in
  let eqhyp = tm "rh = mldsa_slice 0 32 (mldsa_h (APPEND xs [word @K@; word @L@]) 128) /\\ rg = mldsa_slice 32 64 (mldsa_h (APPEND xs [word @K@; word @L@]) 128) /\\ ky = mldsa_slice 96 32 (mldsa_h (APPEND xs [word @K@; word @L@]) 128)" in
  let hw = tm "mldsa_keygen_internal @HW@ xs" in
  let eqgoal = list_mk_forall([`xs:byte list`;`rh:byte list`;`rg:byte list`;`ky:byte list`],
                              mk_imp(eqhyp, mk_eq(hw, pksk))) in
  prove(eqgoal,
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC[mldsa44; mldsa65; mldsa87; mldsa_keygen_internal] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC[WK_T_EQ; MLDSA_DOT_IN_RQ; MLDSA_REJ_BOUNDED_POLY_IN_RQ; ETA_AX] THEN
   CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[MLDSA_BITLEN_CLAUSES]);;

let wk_final p =
  let tm = wk_tm p in
  let th13 = wk_chain p in
  let pksk = rand(rand(concl th13)) in
  let eqth = wk_eq p pksk in
  let seeds = tm "mldsa_h (APPEND xi [word @K@; word @L@]) 128" in
  let rhS = tm "mldsa_slice 0 32 (mldsa_h (APPEND xi [word @K@; word @L@]) 128)"
  and rgS = tm "mldsa_slice 32 64 (mldsa_h (APPEND xi [word @K@; word @L@]) 128)"
  and kyS = tm "mldsa_slice 96 32 (mldsa_h (APPEND xi [word @K@; word @L@]) 128)" in
  let th_i = INST [`xi:byte list`,`xs:byte list`; rhS,`rh:byte list`;
                   rgS,`rg:byte list`; kyS,`ky:byte list`] th13 in
  let len_sl a n = SPECL [mk_small_numeral a; mk_small_numeral n; seeds] LENGTH_MLDSA_SLICE in
  let th_a = PROVE_HYP (len_sl 0 32) th_i in
  let th_b = PROVE_HYP (len_sl 32 64) th_a in
  let th_c = PROVE_HYP (len_sl 96 32) th_b in
  let hl = SPECL [tm "APPEND (xi:byte list) [word @K@; word @L@]"; `128`] BALL_LENGTH_MLDSA_H in
  let sd = SYM (MP (SPEC seeds WK_SEEDS) hl) in
  let th_d = PROVE_HYP sd th_c in
  let eq_i = MP (SPECL [`xi:byte list`; rhS; rgS; kyS] eqth)
                (CONJ (REFL rhS) (CONJ (REFL rgS) (REFL kyS))) in
  let th_e = REWRITE_RULE[GSYM eq_i] th_d in
  GEN `xi:byte list`
    (REWRITE_RULE[IMP_IMP] (DISCH `xof_ok` (DISCH `LENGTH (xi:byte list) = 32` th_e)));;

(* ------------------------------------------------------------------------- *)
(* The theorems, in the form of STMT_KEYGEN_INTERNAL of toplevel.ml.         *)
(* ------------------------------------------------------------------------- *)

let wk_stmt p th =
  if aconv (concl th) (top_tm p STMT_KEYGEN_INTERNAL) then th
  else failwith ("wire_keygen: statement mismatch " ^ p);;

let EQ_KEYGEN_INTERNAL_MLDSA44 = wk_stmt "44" (wk_final "44");;
let EQ_KEYGEN_INTERNAL_MLDSA65 = wk_stmt "65" (wk_final "65");;
let EQ_KEYGEN_INTERNAL_MLDSA87 = wk_stmt "87" (wk_final "87");;
