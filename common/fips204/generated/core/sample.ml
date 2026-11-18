(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Equivalence of the sampling functions of the generated FIPS 204           *)
(* specification (common/fips204/generated/fips204_generated.ml) with        *)
(* common/fips204/fips204.ml: CoeffFromThreeBytes, CoeffFromHalfByte,        *)
(* RejNTTPoly, RejBoundedPoly, ExpandA and ExpandS (FIPS 204 Algorithms 14,  *)
(* 15, 30-33), under xof_ok.                                                 *)
(*                                                                           *)
(* The generated samplers are while loops, which give Nontermination if they *)
(* never finish. They finish for seeds of one SHAKE block, by the            *)
(* termination results MLDSA_REJ_NTT_POLY_TERMINATES and                     *)
(* MLDSA_REJ_BOUNDED_POLY_TERMINATES of                                      *)
(* common/fips204/properties/terminates.ml, and then compute the "first      *)
(* accepted values" of the handwritten definitions.                          *)
(*                                                                           *)
(* Load after base.ml and common.ml.                                   *)
(* ========================================================================= *)

needs "common/fips204/generated/core/common.ml";;
needs "common/fips204/generated/core/core.ml";;

(* ------------------------------------------------------------------------- *)
(* Generic facts about the generated monad and loops (local versions).       *)
(* ------------------------------------------------------------------------- *)


let SAMP_CONTINUE_BIND = prove
 (`(!(s:S) (rest:S->((S,R)statement_outcome)native_result).
        native_continue_bind (Value (Continue s)) rest = rest s) /\
   (!(v:R) (s:S) (rest:S->((S,R)statement_outcome)native_result).
        native_continue_bind (Value (Return_Value v s)) rest =
        Value (Return_Value v s))`,
  REWRITE_TAC[native_continue_bind_DEF; case_native_result_DEF;
              case_statement_outcome_DEF]);;

(* hol_light_iterate is deterministic: once it gives a result, more fuel     *)
(* gives the same result, so native_iter gives it too.                       *)

let SAMP_ITERATE_MONO = prove
 (`!n (step:S->((S,A)iteration_outcome)native_result) s m.
        ~(hol_light_iterate n step s = Nontermination) /\ n <= m
        ==> hol_light_iterate m step s = hol_light_iterate n step s`,
  INDUCT_TAC THEN REWRITE_TAC[hol_light_iterate_DEF] THEN
  X_GEN_TAC `step:S->((S,A)iteration_outcome)native_result` THEN
  X_GEN_TAC `s:S` THEN INDUCT_TAC THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n <= 0)`; LE_SUC; hol_light_iterate_DEF] THEN
  STRUCT_CASES_TAC
   (ISPEC `(step:S->((S,A)iteration_outcome)native_result) s`
          (cases "native_result")) THEN
  REWRITE_TAC[case_native_result_DEF] THEN
  STRUCT_CASES_TAC (ISPEC `a:(S,A)iteration_outcome`
                          (cases "iteration_outcome")) THEN
  REWRITE_TAC[case_iteration_outcome_DEF] THEN ASM_MESON_TAC[]);;

let SAMP_NATIVE_ITER_EQ = prove
 (`!(step:S->((S,A)iteration_outcome)native_result) s n.
        ~(hol_light_iterate n step s = Nontermination)
        ==> native_iter step s = hol_light_iterate n step s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[native_iter_DEF] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN
  W(fun (_,w) -> SPEC_TAC(find_term is_select w,`p:num`)) THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `step:S->((S,A)iteration_outcome)native_result`;
                 `s:S`; `n + p:num`] SAMP_ITERATE_MONO) THEN
  MP_TAC(ISPECL [`p:num`; `step:S->((S,A)iteration_outcome)native_result`;
                 `s:S`; `n + p:num`] SAMP_ITERATE_MONO) THEN
  ASM_REWRITE_TAC[LE_ADD; LE_ADDR] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN REWRITE_TAC[]);;

(* An iteration with an invariant P n after n steps that finishes after N    *)
(* steps with an answer satisfying R.                                        *)

let SAMP_NATIVE_ITER_INV = prove
 (`!(step:S->((S,A)iteration_outcome)native_result) (P:num->S->bool) N
    (R:A->bool) s0.
        P 0 s0 /\
        (!n s. n < N /\ P n s
               ==> ?s'. step s = Value(Again s') /\ P (SUC n) s') /\
        (!s. P N s ==> ?a. step s = Value(Finished a) /\ R a)
        ==> ?a. native_iter step s0 = Value a /\ R a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "step") (LABEL_TAC "fin"))) THEN
  SUBGOAL_THEN
   `!d n (s:S). n + d = N /\ P n s
            ==> ?a:A. hol_light_iterate (SUC d)
                        (step:S->((S,A)iteration_outcome)native_result) s =
                      Value a /\ R a`
  MP_TAC THENL
   [INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
     [REMOVE_THEN "fin" (MP_TAC o SPEC `s:S`) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN EXISTS_TAC `a:A` THEN
      ASM_REWRITE_TAC[hol_light_iterate_DEF; case_native_result_DEF;
                      case_iteration_outcome_DEF];
      REMOVE_THEN "step" (MP_TAC o SPECL [`n:num`; `s:S`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `s':S` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`SUC n`; `s':S`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
       [CONJUNCT2 hol_light_iterate_DEF] THEN
      ASM_REWRITE_TAC[case_native_result_DEF; case_iteration_outcome_DEF]];
    DISCH_THEN(MP_TAC o SPECL [`N:num`; `0`; `s0:S`]) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`step:S->((S,A)iteration_outcome)native_result`;
                   `s0:S`; `SUC N`] SAMP_NATIVE_ITER_EQ) THEN
    ASM_REWRITE_TAC[distinctness "native_result"]]);;

(* A while loop with an invariant P n after n iterations, whose test holds   *)
(* for n < N and fails at N; R holds of the final state.                     *)

let SAMP_NATIVE_WHILE_INV = prove
 (`!(test:S->(bool)native_result)
    (body:S->((S,R)statement_outcome)native_result) (P:num->S->bool) N
    (Q:S->bool) s0.
        P 0 s0 /\
        (!n s. n < N /\ P n s
               ==> test s = Value T /\
                   ?s'. body s = Value(Continue s') /\ P (SUC n) s') /\
        (!s. P N s ==> test s = Value F /\ Q s)
        ==> ?s. native_while (\s. Value(Continue s)) test body s0 =
                Value(Continue s) /\ Q s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[native_while_DEF] THEN
  MP_TAC(ISPECL
   [`native_while_step (\s. Value(Continue s)) (test:S->(bool)native_result)
                       (body:S->((S,R)statement_outcome)native_result)`;
    `P:num->S->bool`; `N:num`;
    `\a:(S,R)statement_outcome. ?s. a = Continue s /\ Q s`; `s0:S`]
   SAMP_NATIVE_ITER_INV) THEN
  REWRITE_TAC[native_while_step_DEF; case_native_result_DEF;
              case_statement_outcome_DEF] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:S`] o
        check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[case_native_result_DEF; case_statement_outcome_DEF] THEN
      EXISTS_TAC `s':S` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `s:S`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[case_native_result_DEF] THEN
      EXISTS_TAC `Continue s:(S,R)statement_outcome` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `s:S` THEN ASM_REWRITE_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `s:S` THEN
    ASM_REWRITE_TAC[]]);;

(* Counted loops over the schedule 0, 1, ..., n - 1.                         *)


let SAMP_FOLDL_INV = prove
 (`!(body:int->S->(S)native_result) (P:num->S->bool) n s0.
        P 0 s0 /\
        (!k s. k < n /\ P k s ==> ?s'. body (&k) s = Value s' /\ P (SUC k) s')
        ==> ?s. native_foldl body (list_of_seq (\k. &k) n) s0 = Value s /\
                P n s`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; native_foldl_DEF] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s0:S`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:S` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:S`]) THEN
  ASM_REWRITE_TAC[LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':S` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s':S` THEN
  ASM_REWRITE_TAC[NATIVE_FOLDL_APPEND; NATIVE_BIND_VALUE; native_foldl_DEF] THEN
  REWRITE_TAC[native_foldl_DEF; NATIVE_BIND_VALUE]);;

(* ------------------------------------------------------------------------- *)
(* Counting accepted candidates.                                             *)
(* ------------------------------------------------------------------------- *)

let SAMP_CARD_SUC = prove
 (`!p n. CARD {j | j < SUC n /\ p j} =
         CARD {j | j < n /\ p j} + (if p n then 1 else 0)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `FINITE {j | j < n /\ p j}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j < n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `{j | j < SUC n /\ p j} = n INSERT {j | j < n /\ p j}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM; LT] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[CARD_CLAUSES; IN_ELIM_THM; LT_REFL] THEN ARITH_TAC];
    REWRITE_TAC[ADD_CLAUSES] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; LT] THEN ASM_MESON_TAC[]]);;

let SAMP_CARD_MONO = prove
 (`!p m n. m <= n ==> CARD {j | j < m /\ p j} <= CARD {j | j < n /\ p j}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[LTE_TRANS];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j < n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]]);;

let SAMP_COUNT_INJ = prove
 (`!p (c:num->num).
        (!m. c(SUC m) = c m + (if p m then 1 else 0)) /\
        (!m n. m <= n ==> c m <= c n)
        ==> !j n. p j /\ p n /\ c j = c n ==> j = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM; GSYM NOT_LT] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`SUC n`; `j:num`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`SUC j`; `n:num`])] THEN
  ASM_REWRITE_TAC[LE_SUC_LT] THEN ASM_ARITH_TAC);;

let SAMP_SELECT_COUNT = prove
 (`!p n. p n
         ==> (@j. p j /\
                  CARD {j' | j' < j /\ p j'} = CARD {j' | j' < n /\ p j'}) =
             n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `j:num` THEN EQ_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`p:num->bool`; `\m. CARD {j | j < m /\ p j}`]
    SAMP_COUNT_INJ) THEN
  REWRITE_TAC[SAMP_CARD_SUC; SAMP_CARD_MONO] THEN ASM_MESON_TAC[]);;

let SAMP_COUNT_EXISTS = prove
 (`!p J K. K < CARD {j | j < J /\ p j}
           ==> ?j. j < J /\ p j /\ CARD {j' | j' < j /\ p j'} = K`,
  SUBGOAL_THEN
   `!p (c:num->num).
        c 0 = 0 /\ (!m. c(SUC m) = c m + (if p m then 1 else 0))
        ==> !J K. K < c J ==> ?j. j < J /\ p j /\ c j = K`
   (fun th -> REPEAT GEN_TAC THEN
              MP_TAC(ISPECL [`p:num->bool`; `\m. CARD {j | j < m /\ p j}`]
                            th) THEN
              REWRITE_TAC[SAMP_CARD_SUC; CONJUNCT1 LT; EMPTY_GSPEC;
                          CARD_CLAUSES] THEN
              MESON_TAC[]) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[CONJUNCT1 LT] THEN GEN_TAC THEN
  ASM_CASES_TAC `K < (c:num->num) J` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `K:num`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[LT];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[ADD_CLAUSES] THENL
   [DISCH_TAC THEN EXISTS_TAC `J:num` THEN ASM_REWRITE_TAC[LT] THEN
    ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

let SAMP_MINIMAL_REACH = prove
 (`!(f:num->num) K. (?J. K <= f J) ==> ?N. K <= f N /\ !n. n < N ==> f n < K`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN
  MESON_TAC[NOT_LE]);;

(* ------------------------------------------------------------------------- *)
(* The XOF context: G (SHAKE128) and H (SHAKE256) after absorbing a byte     *)
(* string and squeezing whole bytes. The context is (input,(phase,offset)).  *)
(* ------------------------------------------------------------------------- *)


let SAMP_EMPTY_SLICE = prove
 (`!x:A. typed_hol_list_slice (REPLICATE 0 x) (&0) (&0) = SOME []`,
  REWRITE_TAC[typed_hol_list_slice_DEF; ISA_NAT_NUM; REPLICATE; LENGTH;
              INT_LE_REFL; INT_SUB_REFL; isa_take; isa_drop]);;

let SAMP_G_ABSORB = prove
 (`!input off str. G_Absorb_hol (input,(Absorbing,off)) str =
                   Value(APPEND input str,(Absorbing,off))`,
  REWRITE_TAC[G_Absorb_hol_DEF; SHAKE_Absorb_semantic_DEF; UNCURRY_DEF]);;

let SAMP_G_SQUEEZE = prove
 (`!input ph off n.
        xof_ok
        ==> G_Squeeze_hol (input,(ph,off)) (&n) =
            Value((input,(Squeezing,off + n)),
                  list_of_seq (\k. shake128 input (off + k)) n)`,
  REWRITE_TAC[xof_ok] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[G_Squeeze_hol_DEF] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ISA_NAT_NUM; SAMP_EMPTY_SLICE; TYPED_HOL_READ_SOME;
              NATIVE_BIND_VALUE] THEN
  REWRITE_TAC[SHAKE128_Squeeze_semantic_DEF; UNCURRY_DEF] THEN
  REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_LT; LT; ISA_NAT_NUM] THEN
  SIMP_TAC[MOD_MULT; DIV_MULT; ARITH_EQ] THEN
  ASM_REWRITE_TAC[ISA_UPT_ADD; MAP_LIST_OF_SEQ; o_DEF]);;

(* ------------------------------------------------------------------------- *)
(* CoeffFromThreeBytes (Algorithm 14) and CoeffFromHalfByte (Algorithm 15).  *)
(* ------------------------------------------------------------------------- *)

let EQ_COEFFFROMTHREEBYTES = prove
 (`!b0 b1 b2:byte.
        CoeffFromThreeBytes_hol b0 b1 b2 =
        Value(if val b0 + 256 * val b1 + 65536 * (val b2 MOD 128) < 8380417
              then Native_Value
                    (lift_zq(&(val b0 + 256 * val b1 +
                               65536 * (val b2 MOD 128))))
              else Native_Bottom)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CoeffFromThreeBytes_hol_DEF; typed_hol_byte_value_DEF;
              typed_hol_int_arithmetic_DEF; lift_zq] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[NATIVE_BIND_VALUE; ISA_NAT_NUM] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[NATIVE_BIND_VALUE] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_CASES_TAC `128 <= val(b2:byte)` THENL
   [SUBGOAL_THEN `val(b2:byte) MOD 128 = val b2 - 128` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; INT_ARITH
     `&128:int <= x ==> &0 < x - &127`; INT_OF_NUM_LE] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_LT;
                GSYM INT_OF_NUM_SUB] THEN
    ASM_SIMP_TAC[INT_OF_NUM_SUB] THEN
    REWRITE_TAC[INT_ARITH `a + b + c:int = (c + b) + a`] THEN
    REWRITE_TAC[INT_MUL_SYM] THEN COND_CASES_TAC THEN REWRITE_TAC[];
    SUBGOAL_THEN `val(b2:byte) MOD 128 = val b2` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[INT_ARITH `~(&128:int <= x) ==> ~(&0 < x - &127)`;
                 INT_OF_NUM_LE] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL;
                GSYM INT_OF_NUM_LT] THEN
    REWRITE_TAC[INT_ARITH `a + b + c:int = (c + b) + a`] THEN
    REWRITE_TAC[INT_MUL_SYM] THEN COND_CASES_TAC THEN REWRITE_TAC[]]);;

let EQ_COEFFFROMHALFBYTE_MLDSA44 = prove
 (`!b. CoeffFromHalfByte_MLDSA44_Configuration_hol (&b) =
       Value(if b < 15 then Native_Value(&2 - &(b MOD 5):int)
             else Native_Bottom)`,
  REWRITE_TAC[CoeffFromHalfByte_MLDSA44_Configuration_hol_DEF; isa_int_mod] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_LT; INT_OF_NUM_REM] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN MESON_TAC[]);;

let EQ_COEFFFROMHALFBYTE_MLDSA65 = prove
 (`!b. CoeffFromHalfByte_MLDSA65_Configuration_hol (&b) =
       Value(if b < 9 then Native_Value(&4 - &b:int) else Native_Bottom)`,
  REWRITE_TAC[CoeffFromHalfByte_MLDSA65_Configuration_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_LT] THEN MESON_TAC[]);;

let EQ_COEFFFROMHALFBYTE_MLDSA87 = prove
 (`!b. CoeffFromHalfByte_MLDSA87_Configuration_hol (&b) =
       Value(if b < 15 then Native_Value(&2 - &(b MOD 5):int)
             else Native_Bottom)`,
  REWRITE_TAC[CoeffFromHalfByte_MLDSA87_Configuration_hol_DEF; isa_int_mod] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_LT; INT_OF_NUM_REM] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* RejNTTPoly (Algorithm 30). The loop invariant after n iterations: the     *)
(* context has absorbed rho and squeezed 3 * n bytes, j is the number of     *)
(* accepted candidates among the first n, and the entries below j are the    *)
(* accepted candidates (FIPS 204 has no bound on the iterations; the loop    *)
(* finishes since there are 256 of them, by MLDSA_REJ_NTT_POLY_TERMINATES).  *)
(* ------------------------------------------------------------------------- *)

let SAMP_IS_WHILE t =
  is_comb t &&
  (try fst(dest_const(fst(strip_comb t))) = "native_while" &&
       length(snd(strip_comb t)) = 4
   with Failure _ -> false);;

let SAMP_RNP_STATE = [RejNTTPoly_hol_emitted_tmp0_update_EXT;
  RejNTTPoly_hol_emitted_ctx_update_EXT; RejNTTPoly_hol_emitted_s_update_EXT;
  RejNTTPoly_hol_emitted_tmp2_update_EXT;
  RejNTTPoly_hol_emitted_a_NTT_update_EXT;
  RejNTTPoly_hol_emitted_j_update_EXT; RejNTTPoly_hol_emitted_state_make_DEF] @
  RejNTTPoly_hol_emitted_state_SELECTORS;;

let EQ_REJNTTPOLY = prove
 (`!rho. xof_ok /\ LENGTH rho < 168
         ==> RejNTTPoly_hol rho = Value(lift_poly(mldsa_rej_ntt_poly rho))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[RejNTTPoly_hol_DEF; RejNTTPoly_hol_core_storage_functional_DEF;
              typed_hol_algorithm_DEF; RejNTTPoly_hol_native_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC(NATIVE_BIND_VALUE :: ISA_NAT_NUM :: SAMP_EMPTY_SLICE ::
              TYPED_HOL_READ_SOME :: SAMP_RNP_STATE) THEN
  REWRITE_TAC[UNCURRY_DEF; G_INIT; SAMP_G_ABSORB; APPEND;
              NATIVE_BIND_VALUE] THEN
  ABBREV_TAC
   `c = \j. val(shake128 rho (3 * j)) + 256 * val(shake128 rho (3 * j + 1)) +
            65536 * (val(shake128 rho (3 * j + 2)) MOD 128)` THEN
  SUBGOAL_THEN
   `!j. val(shake128 rho (3 * j)) + 256 * val(shake128 rho (3 * j + 1)) +
        65536 * (val(shake128 rho (3 * j + 2)) MOD 128) = c j`
  ASSUME_TAC THENL [EXPAND_TAC "c" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mldsa_rej_ntt_poly rho =
    \i. &(c (@j. c j < 8380417 /\ CARD {j' | j' < j /\ c j' < 8380417} = i))`
  SUBST1_TAC THENL
   [REWRITE_TAC[mldsa_rej_ntt_poly] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`rho:byte list`; `256`] MLDSA_REJ_NTT_POLY_TERMINATES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (BETA_RULE(SPECL
   [`\n. CARD {j | j < n /\ c j < 8380417}`; `256`] SAMP_MINIMAL_REACH))) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  W(fun (asl,w) ->
    let wt = find_term SAMP_IS_WHILE w in
    let [pre;test;body;s0] = snd(strip_comb wt) in
    MP_TAC(ISPECL [test; body;
     `\n st. ?x1 ph x3 x4 l.
         st = RejNTTPoly_hol_emitted_state_ext x1
                (Native_Assigned (rho,(ph,3 * n))) x3 x4 (Native_Assigned l)
                (Native_Assigned (&(CARD {j | j < n /\ c j < 8380417}))) /\
         LENGTH l = 256 /\
         !i. i < CARD {j | j < n /\ c j < 8380417}
             ==> EL i l =
                 Native_Value (lift_zq (&(c (@j. c j < 8380417 /\
                       CARD {j' | j' < j /\ c j' < 8380417} = i))))`;
     `N:num`;
     `\st. ?l. RejNTTPoly_hol_emitted_a_NTT st = Native_Assigned l /\
               l = list_of_seq (\i. Native_Value (lift_zq (&(c (@j.
                     c j < 8380417 /\
                     CARD {j' | j' < j /\ c j' < 8380417} = i))))) 256`;
     s0] SAMP_NATIVE_WHILE_INV)) THEN
  ANTS_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT CONJ_TAC THENL
     [(*** The initial state ***)
      MAP_EVERY EXISTS_TAC
       [`Native_Unassigned:ty_native_slot_7`; `Absorbing`;
        `Native_Assigned []:ty_native_slot_8`;
        `Native_Unassigned:(ty_native_bottom_1)native_slot`] THEN
      REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; EMPTY_GSPEC; CARD_CLAUSES;
                  LENGTH_MAP; LENGTH_REPLICATE] THEN
      REWRITE_TAC[RejNTTPoly_hol_emitted_state_EXT_INJECT;
                  injectivity "native_slot"; UNWIND_THM1; LENGTH_MAP;
                  LENGTH_REPLICATE];
      (*** One iteration ***)
      MAP_EVERY X_GEN_TAC [`n:num`; `st:RejNTTPoly_hol_emitted_state`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
      SUBGOAL_THEN `CARD {j | j < n /\ c j < 8380417} < 256` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ABBREV_TAC `m = CARD {j | j < n /\ c j < 8380417}` THEN
      ASM_SIMP_TAC(SAMP_RNP_STATE @
        [TYPED_HOL_SLOT_READ_ASSIGNED; NATIVE_BIND_VALUE; SAMP_G_SQUEEZE; INT_OF_NUM_LT]) THEN
      ASM_SIMP_TAC[TYPED_HOL_NONNEGATIVE_NUM; NATIVE_BIND_VALUE; NATIVE_LIST_INDEX_LIST_OF_SEQ;
                   ARITH; TYPED_HOL_READ_SOME; ADD_CLAUSES] THEN
      REWRITE_TAC[EQ_COEFFFROMTHREEBYTES; NATIVE_BIND_VALUE] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `m < LENGTH(l:ty_list_1)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC(SAMP_RNP_STATE @
        [NATIVE_LIST_UPDATE_LT; TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE; native_if_DEF;
         TYPED_HOL_SLOT_READ_ASSIGNED; NATIVE_LIST_INDEX_LT; LENGTH_ISA_LIST_UPDATE;
         EL_ISA_LIST_UPDATE]) THEN
      ASM_CASES_TAC `(c:num->num) n < 8380417` THEN
      ASM_REWRITE_TAC[SAMP_CARD_SUC; distinctness "native_bottom";
                      injectivity "native_result";
                      injectivity "statement_outcome"; UNWIND_THM1] THEN
      REWRITE_TAC[RejNTTPoly_hol_emitted_state_EXT_INJECT;
                  injectivity "native_slot"; PAIR_EQ] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
                  EXISTS_REFL; GSYM CONJ_ASSOC] THEN
      ASM_SIMP_TAC[LENGTH_ISA_LIST_UPDATE; EL_ISA_LIST_UPDATE;
                   ARITH_RULE `3 * n + 3 = 3 * SUC n`; ADD_CLAUSES;
                   INT_OF_NUM_ADD] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      (SUBGOAL_THEN `i < LENGTH(l:ty_list_1)` ASSUME_TAC THENL
        [ASM_ARITH_TAC; ALL_TAC]) THEN
      ASM_SIMP_TAC[EL_ISA_LIST_UPDATE; LT_REFL] THENL
       [COND_CASES_TAC THENL
         [FIRST_X_ASSUM SUBST_ALL_TAC THEN
          MP_TAC(BETA_RULE(ISPECL [`\j. (c:num->num) j < 8380417`; `n:num`]
            SAMP_SELECT_COUNT)) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
        ASM_SIMP_TAC[ARITH_RULE `i < m ==> ~(i = m)`]];
      (*** The exit ***)
      X_GEN_TAC `st:RejNTTPoly_hol_emitted_state` THEN
      DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
      ASM_SIMP_TAC(SAMP_RNP_STATE @
        [TYPED_HOL_SLOT_READ_ASSIGNED; NATIVE_BIND_VALUE; INT_OF_NUM_LT;
         ARITH_RULE `256 <= n ==> ~(n < 256)`; injectivity "native_slot";
         UNWIND_THM1; injectivity "native_result"]) THEN
      REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `st:RejNTTPoly_hol_emitted_state`
     (CONJUNCTS_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `l:ty_list_1` STRIP_ASSUME_TAC o BETA_RULE))) THEN
    ASM_REWRITE_TAC[SAMP_CONTINUE_BIND; TYPED_HOL_SLOT_READ_ASSIGNED; NATIVE_BIND_VALUE;
                    case_native_result_DEF; case_statement_outcome_DEF;
                    map_native_result_DEF] THEN
    REWRITE_TAC[lift_poly; MAP_LIST_OF_SEQ; o_DEF;
                native_bottom_payload_DEF]]);;

(* ------------------------------------------------------------------------- *)
(* RejBoundedPoly (Algorithm 31), for the three parameter sets. The          *)
(* generated function returns the integer coefficients in [-eta,eta], the    *)
(* handwritten one the element of R_q, so the lemmas relate the generated    *)
(* result to the centered representatives mldsa_modpm (coeff i f) q. The     *)
(* loop invariant after n iterations (n bytes squeezed, nibbles t < 2 * n    *)
(* seen): j is the number of accepted nibbles, at most 256, and the entries  *)
(* below j are the values of the accepted nibbles.                           *)
(* ------------------------------------------------------------------------- *)

let SAMP_DIV2 = prove
 (`!n. (2 * n) DIV 2 = n /\ (2 * n) MOD 2 = 0 /\
       (2 * n + 1) DIV 2 = n /\ (2 * n + 1) MOD 2 = 1`,
  GEN_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `n:num`;
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `1`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `n:num`] THEN
  ARITH_TAC);;

let SAMP_UPDATE_SEL = prove
 (`!p (f:num->B) l m t.
        LENGTH l = 256 /\ m < 256 /\ p t /\ CARD {u | u < t /\ p u} = m /\
        (!i. i < m ==> EL i l = f (@u. p u /\ CARD {u' | u' < u /\ p u'} = i))
        ==> LENGTH (isa_list_update l m (f t)) = 256 /\
            !i. i < m + 1
                ==> EL i (isa_list_update l m (f t)) =
                    f (@u. p u /\ CARD {u' | u' < u /\ p u'} = i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_ISA_LIST_UPDATE] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < LENGTH(l:B list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`p:num->bool`; `t:num`] SAMP_SELECT_COUNT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let SAMP_MODPM_REM = prove
 (`!x. abs x <= &4190208 ==> mldsa_modpm (x rem &8380417) 8380417 = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_modpm; INT_REM_REM] THEN
  ASM_CASES_TAC `&0 <= x:int` THENL
   [SUBGOAL_THEN `x rem &8380417 = x` SUBST1_TAC THENL
     [MATCH_MP_TAC INT_REM_LT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_INT_ARITH_TAC;
    SUBGOAL_THEN `x rem &8380417 = x + &8380417` SUBST1_TAC THENL
     [REWRITE_TAC[INT_REM_UNIQUE] THEN CONJ_TAC THENL
       [ASM_INT_ARITH_TAC; INTEGER_TAC];
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_INT_ARITH_TAC]);;

let SAMP_ABS_ETA2 = prove
 (`!k. abs(&2 - &(k MOD 5):int) <= &4190208`,
  GEN_TAC THEN MP_TAC(SPECL [`k:num`; `5`] MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ; GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let SAMP_ABS_ETA4 = prove
 (`!k. k < 16 ==> abs(&4 - &k:int) <= &4190208`,
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let SAMP_MIN_RULES =
 [ARITH_RULE `m + 1 < 256 ==> MIN ((m + 1) + 1) 256 = (m + 1) + 1`;
  ARITH_RULE `m < 256 /\ ~(m + 1 < 256) ==> MIN ((m + 1) + 1) 256 = m + 1`;
  ARITH_RULE `m < 256 ==> MIN (m + 1) 256 = m + 1`;
  ARITH_RULE `m < 256 ==> MIN m 256 = m`];;

(* The new state after one iteration and the invariant for SUC n.            *)

let SAMP_RBP_FINISH_TAC ext_inject =
  REWRITE_TAC[injectivity "native_result"; injectivity "statement_outcome";
              UNWIND_THM1] THEN
  REWRITE_TAC[ext_inject; injectivity "native_slot"; PAIR_EQ] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; UNWIND_THM1;
              EXISTS_REFL; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC n = SUC(SUC(2 * n))`] THEN
  REWRITE_TAC[SAMP_CARD_SUC] THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * n) = 2 * n + 1`; ADD1] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES];;

(* Storing the value f t of an accepted nibble t at index m.                 *)

let SAMP_RBP_SEL_TAC p f l m t =
  MP_TAC(BETA_RULE(ISPECL [p; f; l; m; t] SAMP_UPDATE_SEL)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[GSYM ADD1; SAMP_CARD_SUC] THEN
        ASM_REWRITE_TAC[ADD1; ADD_CLAUSES] THEN NO_TAC) THEN
    ASM_ARITH_TAC;
    STRIP_TAC];;

(* The four cases of acceptance of the two nibbles 2 * n and 2 * n + 1 of    *)
(* byte n (and whether there is room for the second one).                    *)

let SAMP_RBP_CASES_TAC state_ths ext_inject p f v0 =
  let l = `l:ty_list_2` and m = `m:num` and m1 = `m + 1`
  and t0 = `2 * n` and t1 = `2 * n + 1` in
  let l1 = list_mk_comb
   (`isa_list_update:ty_list_2->num->(int)native_bottom->ty_list_2`,
    [l; m; v0]) in
  let fin = TRY(COND_CASES_TAC) THEN SAMP_RBP_FINISH_TAC ext_inject THEN
            ASM_SIMP_TAC SAMP_MIN_RULES in
  let close = REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC in
  ASM_CASES_TAC (rhs(concl(BETA_CONV(mk_comb(p,t0))))) THEN
  ASM_CASES_TAC (rhs(concl(BETA_CONV(mk_comb(p,t1))))) THEN
  ASM_SIMP_TAC(state_ths @
        [NATIVE_LIST_UPDATE_LT; TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE; native_if_DEF;
         TYPED_HOL_SLOT_READ_ASSIGNED; LENGTH_ISA_LIST_UPDATE; SAMP_CONTINUE_BIND;
         distinctness "native_bottom"; INT_OF_NUM_ADD; INT_OF_NUM_LT]) THENL
   [fin THEN SAMP_RBP_SEL_TAC p f l m t0 THEN
    TRY(SAMP_RBP_SEL_TAC p f l1 m1 t1) THEN close;
    fin THEN SAMP_RBP_SEL_TAC p f l m t0 THEN close;
    fin THEN SAMP_RBP_SEL_TAC p f l m t1 THEN close;
    fin THEN close];;

(* The whole proof, for parameter set cfg with bound eta, acceptance         *)
(* b < k and coefficient fval(b).                                            *)

let SAMP_REJBOUNDEDPOLY_PROVE
      cfg eta k fval defs state_ths ext_inject coeff_th =
  let pt s = parse_term s in
  let sel = Printf.sprintf
    "(@t. b t < %d /\\ CARD {t' | t' < t /\\ b t' < %d} = i)" k k in
  let state = "RejBoundedPoly_"^cfg^"_Configuration_hol_emitted_state" in
  let stmt = pt(Printf.sprintf
   "!rho. xof_ok /\\ LENGTH rho < 135
          ==> RejBoundedPoly_%s_Configuration_hol rho =
              Value(lift_intpoly(\\i. mldsa_modpm
                (coeff i (mldsa_rej_bounded_poly %d rho)) 8380417))"
   cfg eta) in
  let inv = pt(Printf.sprintf
   "\\n st. ?x1 ph x3 x4 x5 l.
       st = %s_ext x1 (Native_Assigned (rho,(ph,n))) x3 x4 x5
              (Native_Assigned l)
              (Native_Assigned
                (&(MIN (CARD {t | t < 2 * n /\\ b t < %d}) 256))) /\\
       LENGTH l = 256 /\\
       !i. i < MIN (CARD {t | t < 2 * n /\\ b t < %d}) 256
           ==> EL i l = Native_Value (%s)"
   state k k (fval sel)) in
  let fin = pt(Printf.sprintf
   "\\st. ?l. RejBoundedPoly_%s_Configuration_hol_emitted_a st =
              Native_Assigned l /\\
              l = list_of_seq (\\i. Native_Value (%s)) 256"
   cfg (fval sel)) in
  let p = pt(Printf.sprintf "\\t. (b:num->num) t < %d" k)
  and f = pt("\\t. Native_Value("^fval "t:num"^"):(int)native_bottom")
  and v0 = pt("Native_Value("^fval "2 * n"^"):(int)native_bottom")
  and stv = mk_var("st",mk_type(state,[])) in
  prove(stmt,
  REPEAT STRIP_TAC THEN REWRITE_TAC defs THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC(NATIVE_BIND_VALUE :: ISA_NAT_NUM :: SAMP_EMPTY_SLICE ::
              TYPED_HOL_READ_SOME :: state_ths) THEN
  REWRITE_TAC[UNCURRY_DEF; H_INIT; H_ABSORB_ABSORBING; APPEND;
              NATIVE_BIND_VALUE] THEN
  ABBREV_TAC
   `b = \t. (val(shake256 rho (t DIV 2)) DIV 16 EXP (t MOD 2)) MOD 16` THEN
  SUBGOAL_THEN
   `!n. val(shake256 rho n) MOD 16 = b(2 * n) /\
        val(shake256 rho n) DIV 16 = b(2 * n + 1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN GEN_TAC THEN REWRITE_TAC[SAMP_DIV2] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `shake256 rho n` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. (val(shake256 rho (t DIV 2)) DIV 16 EXP (t MOD 2)) MOD 16 = b t`
  ASSUME_TAC THENL [EXPAND_TAC "b" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. (b:num->num) t < 16` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN (pt(Printf.sprintf
   "mldsa_rej_bounded_poly %d rho = mldsa_poly (\\i. %s)" eta (fval sel)))
  SUBST1_TAC THENL
   [REWRITE_TAC[mldsa_rej_bounded_poly] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[ARITH_EQ];
    ALL_TAC] THEN
  MP_TAC(SPECL [mk_small_numeral eta; `rho:byte list`; `256`]
    MLDSA_REJ_BOUNDED_POLY_TERMINATES) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(X_CHOOSE_TAC `TT:num`) THEN
  MP_TAC(BETA_RULE(SPECL
   [pt(Printf.sprintf "\\n. CARD {t | t < 2 * n /\\ b t < %d}" k); `256`]
   SAMP_MINIMAL_REACH)) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `TT:num` THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (pt(Printf.sprintf "CARD {t | t < TT /\\ b t < %d}" k)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SAMP_CARD_MONO THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  W(fun (asl,w) ->
    let wt = find_term SAMP_IS_WHILE w in
    let test,body,s0 = match snd(strip_comb wt) with
       [_;t;b;s] -> t,b,s | _ -> failwith "SAMP_REJBOUNDEDPOLY_PROVE" in
    MP_TAC(ISPECL [test; body; inv; `N:num`; fin; s0]
     SAMP_NATIVE_WHILE_INV)) THEN
  ANTS_TAC THENL
   [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT CONJ_TAC THENL
     [(*** The initial state ***)
      MAP_EVERY EXISTS_TAC
       [`Native_Unassigned:ty_native_slot_7`; `Absorbing`;
        `Native_Assigned []:ty_native_slot_8`;
        `Native_Unassigned:ty_native_slot_9`;
        `Native_Unassigned:ty_native_slot_9`] THEN
      REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; EMPTY_GSPEC; CARD_CLAUSES;
                  LENGTH_MAP; LENGTH_REPLICATE; ARITH_RULE `MIN 0 n = 0`] THEN
      REWRITE_TAC[ext_inject; injectivity "native_slot"; UNWIND_THM1;
                  LENGTH_MAP; LENGTH_REPLICATE];
      (*** One iteration ***)
      MAP_EVERY X_GEN_TAC [`n:num`; stv] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
      SUBGOAL_THEN
       (pt(Printf.sprintf "CARD {t | t < 2 * n /\\ b t < %d} < 256" k))
      ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ABBREV_TAC
       (pt(Printf.sprintf "m = CARD {t | t < 2 * n /\\ b t < %d}" k)) THEN
      RULE_ASSUM_TAC(fun th -> if concl th = `m < 256` then th else
        SIMP_RULE[ASSUME `m < 256`; ARITH_RULE `m < 256 ==> MIN m 256 = m`]
         th) THEN
      ASM_SIMP_TAC[ARITH_RULE `m < 256 ==> MIN m 256 = m`] THEN
      ASM_SIMP_TAC(state_ths @
        [TYPED_HOL_SLOT_READ_ASSIGNED; NATIVE_BIND_VALUE; H_SQUEEZE_XOF_OK; INT_OF_NUM_LT]) THEN
      ASM_SIMP_TAC[TYPED_HOL_NONNEGATIVE_NUM; NATIVE_BIND_VALUE; NATIVE_LIST_INDEX_LIST_OF_SEQ;
                   ARITH; TYPED_HOL_READ_SOME; ADD_CLAUSES;
                   typed_hol_byte_value_DEF] THEN
      REWRITE_TAC[isa_int_mod; INT_OF_NUM_REM; typed_hol_int_arithmetic_DEF;
                  arith_faults_DEF; int_op_DEF; case_aop_DEF;
                  distinctness "aop"; isa_int_div; INT_OF_NUM_DIV;
                  INT_OF_NUM_EQ; INT_POS; INT_OF_NUM_LT; ARITH_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[NATIVE_BIND_VALUE] THEN
      REWRITE_TAC[coeff_th; NATIVE_BIND_VALUE] THEN
      SUBGOAL_THEN `m < LENGTH(l:ty_list_2)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SAMP_RBP_CASES_TAC state_ths ext_inject p f v0;
      (*** The exit ***)
      X_GEN_TAC stv THEN
      DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
      SUBGOAL_THEN
       (pt(Printf.sprintf
         "MIN (CARD {t | t < 2 * N /\\ b t < %d}) 256 = 256" k))
      ASSUME_TAC THENL
       [ASM_SIMP_TAC[ARITH_RULE `256 <= m ==> MIN m 256 = 256`]; ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                              REWRITE_TAC[th]) THEN
      ASM_SIMP_TAC(state_ths @
        [TYPED_HOL_SLOT_READ_ASSIGNED; NATIVE_BIND_VALUE; INT_OF_NUM_LT; LT_REFL;
         injectivity "native_slot"; UNWIND_THM1;
         injectivity "native_result"]) THEN
      REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ]];
    DISCH_THEN(X_CHOOSE_THEN stv
     (CONJUNCTS_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `l:ty_list_2` STRIP_ASSUME_TAC o BETA_RULE))) THEN
    ASM_REWRITE_TAC[SAMP_CONTINUE_BIND; TYPED_HOL_SLOT_READ_ASSIGNED; NATIVE_BIND_VALUE;
                    case_native_result_DEF; case_statement_outcome_DEF;
                    map_native_result_DEF] THEN
    REWRITE_TAC[lift_intpoly; MAP_LIST_OF_SEQ; o_DEF;
                native_bottom_payload_DEF; injectivity "native_result";
                injectivity "fips204_intpoly"] THEN
    REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
    SIMP_TAC[EL_LIST_OF_SEQ; COEFF_MLDSA_POLY] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SAMP_MODPM_REM THEN
    ASM_SIMP_TAC[SAMP_ABS_ETA2; SAMP_ABS_ETA4]]);;

let EQ_REJBOUNDEDPOLY_MLDSA44 = SAMP_REJBOUNDEDPOLY_PROVE "MLDSA44" 2 15
  (fun x -> "&2 - &(b ("^x^") MOD 5)")
  [RejBoundedPoly_MLDSA44_Configuration_hol_DEF;
   RejBoundedPoly_MLDSA44_Configuration_hol_core_storage_functional_DEF;
   typed_hol_algorithm_DEF; RejBoundedPoly_MLDSA44_Configuration_hol_native_DEF]
  ([RejBoundedPoly_MLDSA44_Configuration_hol_emitted_tmp0_update_EXT;
    RejBoundedPoly_MLDSA44_Configuration_hol_emitted_ctx_update_EXT;
    RejBoundedPoly_MLDSA44_Configuration_hol_emitted_z_update_EXT;
    RejBoundedPoly_MLDSA44_Configuration_hol_emitted_z0_update_EXT;
    RejBoundedPoly_MLDSA44_Configuration_hol_emitted_z1_update_EXT;
    RejBoundedPoly_MLDSA44_Configuration_hol_emitted_a_update_EXT;
    RejBoundedPoly_MLDSA44_Configuration_hol_emitted_j_update_EXT;
    RejBoundedPoly_MLDSA44_Configuration_hol_emitted_state_make_DEF] @
   RejBoundedPoly_MLDSA44_Configuration_hol_emitted_state_SELECTORS)
  RejBoundedPoly_MLDSA44_Configuration_hol_emitted_state_EXT_INJECT
  EQ_COEFFFROMHALFBYTE_MLDSA44;;

let EQ_REJBOUNDEDPOLY_MLDSA65 = SAMP_REJBOUNDEDPOLY_PROVE "MLDSA65" 4 9
  (fun x -> "&4 - &(b ("^x^"))")
  [RejBoundedPoly_MLDSA65_Configuration_hol_DEF;
   RejBoundedPoly_MLDSA65_Configuration_hol_core_storage_functional_DEF;
   typed_hol_algorithm_DEF; RejBoundedPoly_MLDSA65_Configuration_hol_native_DEF]
  ([RejBoundedPoly_MLDSA65_Configuration_hol_emitted_tmp0_update_EXT;
    RejBoundedPoly_MLDSA65_Configuration_hol_emitted_ctx_update_EXT;
    RejBoundedPoly_MLDSA65_Configuration_hol_emitted_z_update_EXT;
    RejBoundedPoly_MLDSA65_Configuration_hol_emitted_z0_update_EXT;
    RejBoundedPoly_MLDSA65_Configuration_hol_emitted_z1_update_EXT;
    RejBoundedPoly_MLDSA65_Configuration_hol_emitted_a_update_EXT;
    RejBoundedPoly_MLDSA65_Configuration_hol_emitted_j_update_EXT;
    RejBoundedPoly_MLDSA65_Configuration_hol_emitted_state_make_DEF] @
   RejBoundedPoly_MLDSA65_Configuration_hol_emitted_state_SELECTORS)
  RejBoundedPoly_MLDSA65_Configuration_hol_emitted_state_EXT_INJECT
  EQ_COEFFFROMHALFBYTE_MLDSA65;;

let EQ_REJBOUNDEDPOLY_MLDSA87 = SAMP_REJBOUNDEDPOLY_PROVE "MLDSA87" 2 15
  (fun x -> "&2 - &(b ("^x^") MOD 5)")
  [RejBoundedPoly_MLDSA87_Configuration_hol_DEF;
   RejBoundedPoly_MLDSA87_Configuration_hol_core_storage_functional_DEF;
   typed_hol_algorithm_DEF; RejBoundedPoly_MLDSA87_Configuration_hol_native_DEF]
  ([RejBoundedPoly_MLDSA87_Configuration_hol_emitted_tmp0_update_EXT;
    RejBoundedPoly_MLDSA87_Configuration_hol_emitted_ctx_update_EXT;
    RejBoundedPoly_MLDSA87_Configuration_hol_emitted_z_update_EXT;
    RejBoundedPoly_MLDSA87_Configuration_hol_emitted_z0_update_EXT;
    RejBoundedPoly_MLDSA87_Configuration_hol_emitted_z1_update_EXT;
    RejBoundedPoly_MLDSA87_Configuration_hol_emitted_a_update_EXT;
    RejBoundedPoly_MLDSA87_Configuration_hol_emitted_j_update_EXT;
    RejBoundedPoly_MLDSA87_Configuration_hol_emitted_state_make_DEF] @
   RejBoundedPoly_MLDSA87_Configuration_hol_emitted_state_SELECTORS)
  RejBoundedPoly_MLDSA87_Configuration_hol_emitted_state_EXT_INJECT
  EQ_COEFFFROMHALFBYTE_MLDSA87;;

(* ------------------------------------------------------------------------- *)
(* IntegerToBytes for the indices of ExpandA (one byte) and ExpandS (two     *)
(* bytes), and other small facts used by the counted loops.                  *)
(* ------------------------------------------------------------------------- *)

let SAMP_FOLDL_NIL = prove
 (`!(body:I->S->(S)native_result). native_foldl body [] = Value`,
  REWRITE_TAC[FUN_EQ_THM; native_foldl_DEF]);;

let SAMP_REPLICATE_2 = prove
 (`!x:A. REPLICATE 2 x = [x; x]`,
  REWRITE_TAC[TWO; ONE; REPLICATE]);;

let SAMP_BYTELIST_2 = prove
 (`!r. bytelist_of_num 2 r = [word(r MOD 256); word((r DIV 256) MOD 256)]`,
  REWRITE_TAC[TWO; ONE; bytelist_of_num]);;

let SAMP_INT_TO_BYTE = prove
 (`!n. n < 256 ==> typed_hol_int_to_byte(&n) = Value(word n)`,
  SIMP_TAC[typed_hol_int_to_byte_DEF; INT_POS; INT_OF_NUM_LT; WORD_IWORD]);;

let SAMP_DIV_256 = prove
 (`!n. typed_hol_int_arithmetic ADiv (&n) (&256) = Value(&(n DIV 256))`,
  REWRITE_TAC[typed_hol_int_arithmetic_DEF; arith_faults_DEF; int_op_DEF;
              case_aop_DEF; distinctness "aop"; isa_int_div; INT_OF_NUM_DIV;
              INT_OF_NUM_EQ; INT_POS; INT_OF_NUM_LT; ARITH_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[INT_OF_NUM_DIV]);;

let SAMP_ISA_TAKE_ALL = prove
 (`!(l:A list) n. LENGTH l <= n ==> isa_take n l = l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[isa_take; LENGTH] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ASM_ARITH_TAC;
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let SAMP_DIVMOD = prove
 (`!k j n. j < n ==> (k * n + j) DIV n = k /\ (k * n + j) MOD n = j`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `j:num`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `k:num`] THEN
  ASM_REWRITE_TAC[]);;

(* native_schedule (n + 1) (\i. i < &n) (\i. i + &1) (&0) for a numeral n.   *)

let SAMP_SCHEDULE_CONV tm =
  match tm with
    Comb(Comb(Comb(Comb(Const("native_schedule",_),m),_),_),_) ->
      let n = dest_small_numeral m - 1 in
      let th = SPEC (mk_small_numeral n) NATIVE_SCHEDULE_COUNT in
      let th' = CONV_RULE (LAND_CONV(RATOR_CONV(RATOR_CONV(RATOR_CONV
                  (RAND_CONV NUM_SUC_CONV))))) th in
      if aconv (lhs(concl th')) tm then th' else failwith "SAMP_SCHEDULE_CONV"
  | _ -> failwith "SAMP_SCHEDULE_CONV";;

let SAMP_IS_FOLDL t =
  is_comb t &&
  (try fst(dest_const(fst(strip_comb t))) = "native_foldl" &&
       length(snd(strip_comb t)) = 3
   with Failure _ -> false);;

let SAMP_FOLDL_INV_TAC inv n =
  W(fun (asl,w) ->
    let ft = find_term SAMP_IS_FOLDL w in
    let body,_,s0 = match snd(strip_comb ft) with
        [a;b;c] -> a,b,c | _ -> failwith "SAMP_FOLDL_INV_TAC" in
    MP_TAC(ISPECL [body; inv; mk_small_numeral n; s0] SAMP_FOLDL_INV)) THEN
  ANTS_TAC THENL [CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONJ_TAC; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* ExpandA (Algorithm 32). The generated function returns the NTT-domain     *)
(* matrix A^ as a flat list in row-major order: entry (r,s), sampled from    *)
(* rho || IntegerToBytes(s,1) || IntegerToBytes(r,1), is at index r * l + s, *)
(* which is the order of lift_mat (rows dimindex(:R) = k, columns            *)
(* dimindex(:C) = l). The handwritten mldsa_expand_a is the inverse NTT of   *)
(* the same entries; see MLDSA_EXPAND_A_NTT below.                           *)
(* ------------------------------------------------------------------------- *)

let SAMP_EXPANDA_PROVE cfg k l def =
  let pt = parse_term and kl = k * l in
  let mat = Printf.sprintf "(%d,%d,ty_fips204_poly_1)common_mat" k l in
  let stmt = pt(Printf.sprintf
   "!rho. xof_ok /\\ LENGTH rho = 32
          ==> ExpandA_%s_Configuration_hol rho =
              Value(Common_Mat(lift_mat(\\i j. lift_poly(mldsa_rej_ntt_poly
                     (APPEND rho [word j; word i])))))" cfg) in
  let entry = Printf.sprintf
   "lift_poly (mldsa_rej_ntt_poly (APPEND rho [word (idx MOD %d);
                                                word (idx DIV %d)]))" l l in
  let outer = pt(Printf.sprintf
   "\\r (A:%s). ?v. A = Common_Mat (FIPS_Matrix v) /\\ LENGTH v = %d /\\
                   !idx. idx < r * %d ==> EL idx v = %s" mat kl l entry)
  and inner = pt(Printf.sprintf
   "\\s (A:%s). ?v. A = Common_Mat (FIPS_Matrix v) /\\ LENGTH v = %d /\\
                   !idx. idx < k * %d + s ==> EL idx v = %s" mat kl l entry)
  and av = mk_var("A",parse_type mat) and a1 = mk_var("A1",parse_type mat)
  and vv = `v:(ty_fips204_poly_1)list` and v0 = `v0:(ty_fips204_poly_1)list` in
  let idx_bound = pt(Printf.sprintf
    "k * %d + j < LENGTH(v:(ty_fips204_poly_1)list)" l) in
  prove(stmt,
  REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ISA_NAT_NUM; SAMP_EMPTY_SLICE; TYPED_HOL_READ_SOME;
              NATIVE_BIND_VALUE] THEN
  CONV_TAC(DEPTH_CONV SAMP_SCHEDULE_CONV) THEN
  SAMP_FOLDL_INV_TAC outer k THENL
   [(*** Initial matrix ***)
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; injectivity "common_mat";
                fips_matrix_INJECT] THEN
    REWRITE_TAC[UNWIND_THM1; LENGTH_MAP; LENGTH_REPLICATE];
    (*** Row k ***)
    MAP_EVERY X_GEN_TAC [`k:num`; av] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN v0 STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (is_var o lhs o concl)) THEN
    SAMP_FOLDL_INV_TAC inner l THENL
     [EXISTS_TAC v0 THEN ASM_REWRITE_TAC[ADD_CLAUSES];
      (*** Entry (k,j) ***)
      MAP_EVERY X_GEN_TAC [`j:num`; av] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN vv STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (is_var o lhs o concl)) THEN
      SUBGOAL_THEN `j < 256 /\ k < 256` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[INTEGER_TO_BYTES_1_NUM; NATIVE_BIND_VALUE] THEN
      ASM_SIMP_TAC[TYPED_HOL_LIST_SLICE_ALL; LENGTH_APPEND; LENGTH; ARITH;
                   TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE; typed_hol_bit_value_DEF;
                   TYPED_HOL_INT_POW_ONE] THEN
      REWRITE_TAC[INT_MUL_RZERO; INT_ADD_RID; INT_MUL_LID; INT_ADD_LID;
                  INT_OF_NUM_MUL; INT_OF_NUM_ADD; TYPED_HOL_NONNEGATIVE_NUM;
                  NATIVE_BIND_VALUE; ADD_CLAUSES] THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      ASM_SIMP_TAC[EQ_REJNTTPOLY; LENGTH_APPEND; LENGTH; ARITH;
                   NATIVE_BIND_VALUE] THEN
      REWRITE_TAC[typed_hol_nominal_update_DEF; common_mat_entries_DEF;
                  fips_matrix_SEL_CTR] THEN
      SUBGOAL_THEN idx_bound ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[NATIVE_LIST_UPDATE_LT; isa_map_option; TYPED_HOL_READ_SOME;
                   injectivity "native_result"; UNWIND_THM1;
                   injectivity "common_mat"; fips_matrix_INJECT;
                   LENGTH_ISA_LIST_UPDATE] THEN
      X_GEN_TAC `idx:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `idx < LENGTH(v:(ty_fips204_poly_1)list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN COND_CASES_TAC THENL
       [ASM_SIMP_TAC[SAMP_DIVMOD] THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN a1
        (CONJUNCTS_THEN2 SUBST1_TAC (MP_TAC o BETA_RULE))) THEN
      REWRITE_TAC[injectivity "native_result"; UNWIND_THM1; MULT_CLAUSES]];
    (*** The result ***)
    DISCH_THEN(X_CHOOSE_THEN av
     (CONJUNCTS_THEN2 SUBST1_TAC (X_CHOOSE_THEN vv STRIP_ASSUME_TAC o
                                  BETA_RULE))) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (is_var o lhs o concl)) THEN
    REWRITE_TAC[lift_mat; injectivity "native_result";
                injectivity "common_mat"; fips_matrix_INJECT] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let EQ_EXPANDA_MLDSA44 =
  SAMP_EXPANDA_PROVE "MLDSA44" 4 4 ExpandA_MLDSA44_Configuration_hol_DEF;;

let EQ_EXPANDA_MLDSA65 =
  SAMP_EXPANDA_PROVE "MLDSA65" 6 5 ExpandA_MLDSA65_Configuration_hol_DEF;;

let EQ_EXPANDA_MLDSA87 =
  SAMP_EXPANDA_PROVE "MLDSA87" 8 7 ExpandA_MLDSA87_Configuration_hol_DEF;;

(* ------------------------------------------------------------------------- *)
(* ExpandS (Algorithm 33): s1 and s2 from rho' || IntegerToBytes(r,2) and    *)
(* rho' || IntegerToBytes(r + l,2), as in mldsa_keygen_internal. As for      *)
(* RejBoundedPoly, the entries are the centered coefficients of the          *)
(* handwritten polynomials.                                                  *)
(* ------------------------------------------------------------------------- *)

let SAMP_LENGTH_BYTELIST = prove
 (`!k n. LENGTH(bytelist_of_num k n) = k`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[bytelist_of_num; LENGTH]);;

let SAMP_EXPANDS_PROVE cfg eta k l def rbp_th =
  let pt = parse_term in
  let entry off = Printf.sprintf
   "lift_intpoly(\\j. mldsa_modpm (coeff j (mldsa_rej_bounded_poly %d
       (APPEND rho (bytelist_of_num 2 (%s))))) 8380417)" eta off in
  let stmt = pt(Printf.sprintf
   "!rho. xof_ok /\\ LENGTH rho = 64
          ==> ExpandS_%s_Configuration_hol rho =
              Value(lift_vec(\\i. %s),lift_vec(\\i. %s))"
   cfg (entry "i") (entry (Printf.sprintf "%d + i" l))) in
  let vec n = Printf.sprintf "(%d,fips204_intpoly)common_vec" n in
  let inv n off = pt(Printf.sprintf
   "\\r (V:%s). ?v. V = Common_Vec v /\\ LENGTH v = %d /\\
                   !i. i < r ==> EL i v = %s" (vec n) n (entry off)) in
  let inv1 = inv l "i" and inv2 = inv k (Printf.sprintf "i + %d" l) in
  let vv = `v:(fips204_intpoly)list` in
  let body_tac n =
    MAP_EVERY X_GEN_TAC [`r:num`; mk_var("V",parse_type(vec n))] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN vv STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (is_var o lhs o concl)) THEN
    REWRITE_TAC[TYPED_HOL_NONNEGATIVE_NUM; NATIVE_BIND_VALUE; INT_OF_NUM_ADD;
                INTEGER_TO_BYTES_2_NUM] THEN
    ASM_SIMP_TAC[TYPED_HOL_LIST_SLICE_ALL; LENGTH_APPEND; SAMP_LENGTH_BYTELIST;
                 ARITH; TYPED_HOL_READ_SOME; NATIVE_BIND_VALUE] THEN
    ASM_SIMP_TAC[rbp_th; LENGTH_APPEND; SAMP_LENGTH_BYTELIST; ARITH;
                 NATIVE_BIND_VALUE] THEN
    REWRITE_TAC[typed_hol_nominal_update_DEF; common_vec_SEL_CTR] THEN
    SUBGOAL_THEN `r < LENGTH(v:(fips204_intpoly)list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[NATIVE_LIST_UPDATE_LT; isa_map_option; TYPED_HOL_READ_SOME;
                 injectivity "native_result"; UNWIND_THM1; common_vec_INJECT;
                 LENGTH_ISA_LIST_UPDATE] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `i < LENGTH(v:(fips204_intpoly)list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_ISA_LIST_UPDATE] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC in
  let init_tac =
    REWRITE_TAC[CONJUNCT1 LT; common_vec_INJECT] THEN
    REWRITE_TAC[UNWIND_THM1; LENGTH_MAP; LENGTH_REPLICATE] in
  prove(stmt,
  REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV SAMP_SCHEDULE_CONV) THEN
  SAMP_FOLDL_INV_TAC inv1 l THENL
   [init_tac;
    body_tac l;
    DISCH_THEN(X_CHOOSE_THEN (mk_var("s1",parse_type(vec l)))
     (CONJUNCTS_THEN2 SUBST1_TAC (X_CHOOSE_THEN `v1:(fips204_intpoly)list`
        STRIP_ASSUME_TAC o BETA_RULE))) THEN
    REWRITE_TAC[NATIVE_BIND_VALUE] THEN
    SAMP_FOLDL_INV_TAC inv2 k THENL
     [init_tac;
      body_tac k;
      DISCH_THEN(X_CHOOSE_THEN (mk_var("s2",parse_type(vec k)))
       (CONJUNCTS_THEN2 SUBST1_TAC (X_CHOOSE_THEN `v2:(fips204_intpoly)list`
          STRIP_ASSUME_TAC o BETA_RULE))) THEN
      REWRITE_TAC[NATIVE_BIND_VALUE] THEN
      REPEAT(FIRST_X_ASSUM(SUBST1_TAC o check (is_var o lhs o concl))) THEN
      REWRITE_TAC[lift_vec; injectivity "native_result"; PAIR_EQ;
                  common_vec_INJECT] THEN
      CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
      REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
      REFL_TAC]]);;

let EQ_EXPANDS_MLDSA44 =
  SAMP_EXPANDS_PROVE "MLDSA44" 2 4 4 ExpandS_MLDSA44_Configuration_hol_DEF
   EQ_REJBOUNDEDPOLY_MLDSA44;;

let EQ_EXPANDS_MLDSA65 =
  SAMP_EXPANDS_PROVE "MLDSA65" 4 6 5 ExpandS_MLDSA65_Configuration_hol_DEF
   EQ_REJBOUNDEDPOLY_MLDSA65;;

let EQ_EXPANDS_MLDSA87 =
  SAMP_EXPANDS_PROVE "MLDSA87" 2 8 7 ExpandS_MLDSA87_Configuration_hol_DEF
   EQ_REJBOUNDEDPOLY_MLDSA87;;

(* ------------------------------------------------------------------------- *)
(* The form of ExpandA for the callers that use the handwritten matrix A:    *)
(* the sampled entries are in [0,q) (for seeds of fewer than 168 bytes), so  *)
(* they are the NTT of the entries of mldsa_expand_a.                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_REJ_NTT_POLY_RANGE = prove
 (`!rho i. LENGTH rho < 168
           ==> &0 <= mldsa_rej_ntt_poly rho i /\
               mldsa_rej_ntt_poly rho i < &8380417`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_rej_ntt_poly] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN
  MP_TAC(SPECL [`rho:byte list`; `i + 1`] MLDSA_REJ_NTT_POLY_TERMINATES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `J:num`) THEN
  MP_TAC(ISPECL
   [`\j. val(shake128 rho (3 * j)) + 256 * val(shake128 rho (3 * j + 1)) +
         65536 * (val(shake128 rho (3 * j + 2)) MOD 128) < 8380417`;
    `J:num`; `i:num`] SAMP_COUNT_EXISTS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SELECT_RULE o
    MATCH_MP (MESON[] `(?j. j < J /\ P j) ==> (?j. P j)`)) THEN
  SIMP_TAC[]);;

let MLDSA_EXPAND_A_NTT = prove
 (`!rho i j k.
        LENGTH rho < 166 /\ k < 256
        ==> mldsa_ntt (mldsa_expand_a rho i j) k =
            mldsa_rej_ntt_poly (APPEND rho [word j; word i]) k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_expand_a] THEN
  MP_TAC(ISPEC `mldsa_rej_ntt_poly (APPEND rho [word j; word i])`
    MLDSA_NTT_INV) THEN
  ANTS_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MLDSA_REJ_NTT_POLY_RANGE THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[]]);;

let SAMP_EXPANDA_NTT_TAC th =
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[th] THEN
  REPLICATE_TAC 3 AP_TERM_TAC THEN ABS_TAC THEN ABS_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC LIFT_POLY_CONG THEN
  ASM_SIMP_TAC[MLDSA_EXPAND_A_NTT; ARITH_RULE `n = 32 ==> n < 166`];;

let EQ_EXPANDA_NTT_MLDSA44 = prove
 (`!rho. xof_ok /\ LENGTH rho = 32
         ==> ExpandA_MLDSA44_Configuration_hol rho =
             Value(Common_Mat(lift_mat(\i j.
                lift_poly(mldsa_ntt(mldsa_expand_a rho i j)))))`,
  SAMP_EXPANDA_NTT_TAC EQ_EXPANDA_MLDSA44);;

let EQ_EXPANDA_NTT_MLDSA65 = prove
 (`!rho. xof_ok /\ LENGTH rho = 32
         ==> ExpandA_MLDSA65_Configuration_hol rho =
             Value(Common_Mat(lift_mat(\i j.
                lift_poly(mldsa_ntt(mldsa_expand_a rho i j)))))`,
  SAMP_EXPANDA_NTT_TAC EQ_EXPANDA_MLDSA65);;

let EQ_EXPANDA_NTT_MLDSA87 = prove
 (`!rho. xof_ok /\ LENGTH rho = 32
         ==> ExpandA_MLDSA87_Configuration_hol rho =
             Value(Common_Mat(lift_mat(\i j.
                lift_poly(mldsa_ntt(mldsa_expand_a rho i j)))))`,
  SAMP_EXPANDA_NTT_TAC EQ_EXPANDA_MLDSA87);;
