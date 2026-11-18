(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bounding the attempts of signing. An attempt of the rejection-sampling    *)
(* loop of FIPS 204 Algorithm 7 uses its counter kappa only in ExpandMask,   *)
(* whose nonce is the two bytes of kappa + r: IntegerToBytes keeps the low   *)
(* 16 bits. So attempt n (with kappa = l * n) is the same as attempt n +     *)
(* 65536 (MLDSA_SIGN_ATTEMPT_PERIODIC), and the first accepted attempt, if   *)
(* there is one, is below 65536. Hence a bound N >= 65536 on the attempts    *)
(* makes no difference to signing (MLDSA_SIGN_MU_BOUND and its versions for  *)
(* the other signing functions), and for every bound N, a signature that     *)
(* is found within the bound is the one found without it                     *)
(* (MLDSA_SIGN_MU_BOUND_SUCCESS and its versions).                           *)
(* ========================================================================= *)

needs "common/fips204/properties/sign_alt.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The counter enters the attempt only through the nonce of ExpandMask.      *)
(* ------------------------------------------------------------------------- *)

let BYTELIST_OF_NUM_2_PERIODIC = prove
 (`!x. bytelist_of_num 2 (x + 65536) = bytelist_of_num 2 x`,
  REWRITE_TAC[TWO; ONE; bytelist_of_num] THEN GEN_TAC THEN
  SUBGOAL_THEN `!y. (y + 256) MOD 256 = y MOD 256` ASSUME_TAC THENL
   [GEN_TAC THEN ONCE_REWRITE_TAC[ARITH_RULE `y + 256 = 1 * 256 + y`] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x + 65536) MOD 256 = x MOD 256` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `x + 65536 = 256 * 256 + x`] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `(x + 65536) DIV 256 = x DIV 256 + 256`]);;

let MLDSA_EXPAND_MASK_PERIODIC = prove
 (`!gamma1 rho kappa r.
        mldsa_expand_mask gamma1 rho (kappa + 65536) r =
        mldsa_expand_mask gamma1 rho kappa r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mldsa_expand_mask] THEN
  REWRITE_TAC[ARITH_RULE `(kappa + 65536) + r = (kappa + r) + 65536`;
              BYTELIST_OF_NUM_2_PERIODIC]);;

let MLDSA_SIGN_ATTEMPT_PERIODIC = prove
 (`!p A s1 s2 t0 mu rho'' kappa.
        mldsa_sign_attempt p A s1 s2 t0 mu rho'' (kappa + 65536) =
        mldsa_sign_attempt p A s1 s2 t0 mu rho'' kappa`,
  REWRITE_TAC[FORALL_PAIR_THM; mldsa_sign_attempt;
              MLDSA_EXPAND_MASK_PERIODIC]);;

let MLDSA_SIGN_ATTEMPT_PERIODIC_MUL = prove
 (`!p A s1 s2 t0 mu rho'' kappa m.
        mldsa_sign_attempt p A s1 s2 t0 mu rho'' (kappa + 65536 * m) =
        mldsa_sign_attempt p A s1 s2 t0 mu rho'' kappa`,
  REPEAT GEN_TAC THEN SPEC_TAC(`m:num`,`m:num`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES];
    REWRITE_TAC[ARITH_RULE `kappa + 65536 * SUC m =
                            (kappa + 65536 * m) + 65536`;
                MLDSA_SIGN_ATTEMPT_PERIODIC] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The search of signing for a periodic sequence of attempts.                *)
(* ------------------------------------------------------------------------- *)

let SEARCH_MINIMAL_BOUND = prove
 (`!P N. (?n. n < N /\ P n)
         ==> (minimal n. n < N /\ P n) = (minimal n. P n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n:num. n < N /\ P n`; `P:num->bool`] MINIMAL_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE(SPEC `\n:num. n < N /\ P n` MINIMAL))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE(SPEC `P:num->bool` MINIMAL))) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  MATCH_MP_TAC MINIMAL_UNIQUE THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `minimal n. n < N /\ P n` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[ETA_AX];
    X_GEN_TAC `k:num` THEN REWRITE_TAC[ETA_AX] THEN DISCH_TAC THEN
    ASM_MESON_TAC[]]);;

let SIGN_SEARCH_PERIODIC_BOUND = prove
 (`!att:num->(byte list)option N.
        (!n. att(n + 65536) = att n) /\ 65536 <= N
        ==> (if ?n. mldsa_attempt_allowed (SOME N) n /\ ~(att n = NONE)
             then att(minimal n. mldsa_attempt_allowed (SOME N) n /\
                                 ~(att n = NONE))
             else NONE) =
            (if ?n. mldsa_attempt_allowed NONE n /\ ~(att n = NONE)
             then att(minimal n. mldsa_attempt_allowed NONE n /\
                                 ~(att n = NONE))
             else NONE)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_attempt_allowed] THEN
  SUBGOAL_THEN `!q r. (att:num->(byte list)option)(r + 65536 * q) = att r`
   ASSUME_TAC THENL
   [INDUCT_TAC THEN GEN_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES;
      ARITH_RULE `r + 65536 * SUC q = (r + 65536 * q) + 65536`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(?n. ~((att:num->(byte list)option) n = NONE))
                ==> ?n. n < N /\ ~(att n = NONE)` ASSUME_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    EXISTS_TAC `n MOD 65536` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `65536` THEN
      ASM_REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPECL [`n DIV 65536`; `n MOD 65536`]) THEN
      REWRITE_TAC[ARITH_RULE `n MOD 65536 + 65536 * n DIV 65536 = n`] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `?n. ~((att:num->(byte list)option) n = NONE)` THENL
   [SUBGOAL_THEN `?n. n < N /\ ~((att:num->(byte list)option) n = NONE)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`\n. ~((att:num->(byte list)option) n = NONE)`;
                   `N:num`] SEARCH_MINIMAL_BOUND)) THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(?n. n < N /\ ~((att:num->(byte list)option) n = NONE))`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

let SIGN_SEARCH_BOUND_SUCCESS = prove
 (`!att:num->(byte list)option N sg.
        (if ?n. mldsa_attempt_allowed (SOME N) n /\ ~(att n = NONE)
         then att(minimal n. mldsa_attempt_allowed (SOME N) n /\
                             ~(att n = NONE))
         else NONE) = SOME sg
        ==> (if ?n. mldsa_attempt_allowed NONE n /\ ~(att n = NONE)
             then att(minimal n. mldsa_attempt_allowed NONE n /\
                                 ~(att n = NONE))
             else NONE) = SOME sg`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mldsa_attempt_allowed] THEN
  ASM_CASES_TAC `?n. n < N /\ ~((att:num->(byte list)option) n = NONE)` THENL
   [SUBGOAL_THEN `?n. ~((att:num->(byte list)option) n = NONE)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\n. ~((att:num->(byte list)option) n = NONE)`;
                   `N:num`] SEARCH_MINIMAL_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ASM_REWRITE_TAC[distinctness "option"]]);;

(* ------------------------------------------------------------------------- *)
(* Signing. LET_TAC names the search over the attempts att.                  *)
(* ------------------------------------------------------------------------- *)

let SIGN_MU_ATT_PERIODIC = prove
 (`!(att:num->(byte list)option) l p A s1 s2 t0 mu rho''.
        att = (\n. mldsa_sign_attempt p A s1 s2 t0 mu rho'' (l * n))
        ==> !n. att(n + 65536) = att n`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `l * (n + 65536) = l * n + 65536 * l`;
              MLDSA_SIGN_ATTEMPT_PERIODIC_MUL]);;

let MLDSA_SIGN_MU_BOUND = prove
 (`!p N sk mu rnd.
        65536 <= N
        ==> mldsa_sign_mu p (SOME N) sk mu rnd =
            mldsa_sign_mu p NONE sk mu rnd`,
  REWRITE_TAC[FORALL_PAIR_THM; mldsa_sign_mu] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT LET_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SIGN_SEARCH_PERIODIC_BOUND THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(ACCEPT_TAC o MATCH_MP SIGN_MU_ATT_PERIODIC o SYM));;

let MLDSA_SIGN_MU_BOUND_SUCCESS = prove
 (`!p N sk mu rnd sg.
        mldsa_sign_mu p (SOME N) sk mu rnd = MLDSA_Sign_Success sg
        ==> mldsa_sign_mu p NONE sk mu rnd = MLDSA_Sign_Success sg`,
  REWRITE_TAC[FORALL_PAIR_THM; mldsa_sign_mu] THEN
  REPEAT GEN_TAC THEN REPEAT LET_TAC THEN
  SPEC_TAC(`att:num->(byte list)option`,`att:num->(byte list)option`) THEN
  GEN_TAC THEN
  SUBGOAL_THEN
   `!x y:(byte list)option.
        (x = SOME sg ==> y = SOME sg)
        ==> mldsa_sign_of_option x = MLDSA_Sign_Success sg
            ==> mldsa_sign_of_option y = MLDSA_Sign_Success sg` MP_TAC THENL
   [REWRITE_TAC[FORALL_OPTION_THM; mldsa_sign_of_option] THEN
    REWRITE_TAC[injectivity "mldsa_sign_result"; injectivity "option";
                distinctness "mldsa_sign_result"; distinctness "option"] THEN
    MESON_TAC[];
    DISCH_THEN MATCH_MP_TAC THEN MATCH_ACCEPT_TAC SIGN_SEARCH_BOUND_SUCCESS]);;

(* ------------------------------------------------------------------------- *)
(* The same for the functions that call mldsa_sign_mu.                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_SIGN_INTERNAL_BOUND = prove
 (`!p N sk m rnd.
        65536 <= N
        ==> mldsa_sign_internal p (SOME N) sk m rnd =
            mldsa_sign_internal p NONE sk m rnd`,
  SIMP_TAC[mldsa_sign_internal; MLDSA_SIGN_MU_BOUND]);;

let MLDSA_SIGN_INTERNAL_BOUND_SUCCESS = prove
 (`!p N sk m rnd sg.
        mldsa_sign_internal p (SOME N) sk m rnd = MLDSA_Sign_Success sg
        ==> mldsa_sign_internal p NONE sk m rnd = MLDSA_Sign_Success sg`,
  REWRITE_TAC[mldsa_sign_internal; MLDSA_SIGN_MU_BOUND_SUCCESS]);;

let MLDSA_SIGN_BOUND = prove
 (`!p N sk m ctx rnd.
        65536 <= N
        ==> mldsa_sign p (SOME N) sk m ctx rnd =
            mldsa_sign p NONE sk m ctx rnd`,
  SIMP_TAC[mldsa_sign; MLDSA_SIGN_INTERNAL_BOUND]);;

let MLDSA_SIGN_BOUND_SUCCESS = prove
 (`!p N sk m ctx rnd sg.
        mldsa_sign p (SOME N) sk m ctx rnd = MLDSA_Sign_Success sg
        ==> mldsa_sign p NONE sk m ctx rnd = MLDSA_Sign_Success sg`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mldsa_sign] THEN
  ASM_CASES_TAC `255 < LENGTH(ctx:byte list)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_ACCEPT_TAC MLDSA_SIGN_INTERNAL_BOUND_SUCCESS);;

let MLDSA_HASH_SIGN_BOUND = prove
 (`!p N sk oid ph ctx rnd.
        65536 <= N
        ==> hash_mldsa_sign p (SOME N) sk oid ph ctx rnd =
            hash_mldsa_sign p NONE sk oid ph ctx rnd`,
  SIMP_TAC[hash_mldsa_sign; MLDSA_SIGN_INTERNAL_BOUND]);;

let MLDSA_HASH_SIGN_BOUND_SUCCESS = prove
 (`!p N sk oid ph ctx rnd sg.
        hash_mldsa_sign p (SOME N) sk oid ph ctx rnd = MLDSA_Sign_Success sg
        ==> hash_mldsa_sign p NONE sk oid ph ctx rnd = MLDSA_Sign_Success sg`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hash_mldsa_sign] THEN
  ASM_CASES_TAC `255 < LENGTH(ctx:byte list)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_ACCEPT_TAC MLDSA_SIGN_INTERNAL_BOUND_SUCCESS);;

type_invention_error := false;;
