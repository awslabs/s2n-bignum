(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Core lemmas for the equivalence proof: the result monad of the generated  *)
(* code, its statement blocks and loops, the Isabelle list and integer       *)
(* helpers of fips_hol_prelude.ml, residues and the lifts of common.ml, and  *)
(* the XOF model (H/G Init, Absorb, Squeeze).                                *)
(*                                                                           *)
(* Main entry points for the other components:                               *)
(*                                                                           *)
(*   GEN_MONAD_RULES       rewrites for the monad, options, slots, lists,    *)
(*                         integer literals and the selectors of the types   *)
(*   GEN_SIMP_TAC ths      ASM_SIMP_TAC with these and ths, plus reduction   *)
(*                         of numeral arithmetic, repeated                   *)
(*   NATIVE_SCHEDULE_CONV  native_schedule n (\i. i < b) (\i. i + &1) a      *)
(*                         --> list_of_seq (\k. a + &k) m                    *)
(*   NATIVE_FOLDL_LIST_OF_SEQ, NATIVE_FOLD_LIST_OF_SEQ: counted loops from   *)
(*                         a sequence of states st 0, st 1, ...              *)
(*   NATIVE_ITER, NATIVE_WHILE, NATIVE_LOOP, NATIVE_INDEXED_WHILE: one-step  *)
(*                         unfolding of the while loops, and the _STEPS,     *)
(*                         _EXIT, _DIVERGE and _VARIANT forms                *)
(*   LENGTH_LIFT_*, EL_LIFT_*, LIFT_*_EQ: the coefficient lists of the lifts *)
(*                         of common.ml and when two lifts are equal         *)
(*   EQ_H_HOL, EQ_H_SQUEEZE, EQ_G_SQUEEZE, EQ_H_INIT_ABSORB_SQUEEZE: the     *)
(*                         XOFs under xof_ok, as mldsa_h and as slices of    *)
(*                         shake256 / shake128                               *)
(*                                                                           *)
(* Note: a fips204_zq need not be reduced (Residue wraps any natural), so    *)
(* all the residue lemmas here are about values built by residue_of_int_mod, *)
(* which is what lift_zq uses. A lifted matrix as a (R,C,E)common_mat is     *)
(* Common_Mat (lift_mat m); common.ml has no lift for common_mat.            *)
(* ========================================================================= *)

needs "common/fips204/generated/core/common.ml";;

(* ------------------------------------------------------------------------- *)
(* Constructors of the generated datatypes.                                  *)
(* ------------------------------------------------------------------------- *)

let NATIVE_RESULT_DISTINCT = distinctness "native_result";;
let NATIVE_RESULT_INJ = injectivity "native_result";;
let NATIVE_RESULT_CASES = cases "native_result";;

let STATEMENT_OUTCOME_DISTINCT = distinctness "statement_outcome";;
let STATEMENT_OUTCOME_INJ = injectivity "statement_outcome";;
let STATEMENT_OUTCOME_CASES = cases "statement_outcome";;

let ITERATION_OUTCOME_DISTINCT = distinctness "iteration_outcome";;
let ITERATION_OUTCOME_INJ = injectivity "iteration_outcome";;
let ITERATION_OUTCOME_CASES = cases "iteration_outcome";;

let NATIVE_SLOT_DISTINCT = distinctness "native_slot";;
let NATIVE_SLOT_INJ = injectivity "native_slot";;

let NATIVE_BOTTOM_DISTINCT = distinctness "native_bottom";;
let NATIVE_BOTTOM_INJ = injectivity "native_bottom";;

let FAULT_DISTINCT = distinctness "fault";;
let XOF_PHASE_DISTINCT = distinctness "xof_phase";;

let FIPS204_ZQ_INJ = injectivity "fips204_zq";;
let FIPS204_INTPOLY_INJ = injectivity "fips204_intpoly";;
let FIPS204_BITPOLY_INJ = injectivity "fips204_bitpoly";;

(* Case splits on a term of type (A)native_result, (S,R)statement_outcome    *)
(* and (S,A)iteration_outcome.                                               *)

let NATIVE_CASES_TAC tm =
  STRUCT_CASES_TAC (ISPEC tm NATIVE_RESULT_CASES);;

let OUTCOME_CASES_TAC tm =
  STRUCT_CASES_TAC (ISPEC tm STATEMENT_OUTCOME_CASES);;

let ITERATION_CASES_TAC tm =
  STRUCT_CASES_TAC (ISPEC tm ITERATION_OUTCOME_CASES);;

(* ------------------------------------------------------------------------- *)
(* The result monad.                                                         *)
(* ------------------------------------------------------------------------- *)

let NATIVE_BIND = prove
 (`(!x (f:A->(B)native_result). native_bind (Value x) f = f x) /\
   (!e (f:A->(B)native_result). native_bind (Fault e) f = Fault e) /\
   (!f:A->(B)native_result. native_bind Nontermination f = Nontermination)`,
  REWRITE_TAC[native_bind_DEF; case_native_result_DEF]);;

let NATIVE_BIND_ASSOC = prove
 (`!m (f:A->(B)native_result) (g:B->(C)native_result).
     native_bind (native_bind m f) g = native_bind m (\x. native_bind (f x) g)`,
  GEN_TAC THEN NATIVE_CASES_TAC `m:(A)native_result` THEN
  REWRITE_TAC[NATIVE_BIND]);;

let NATIVE_BIND_RETURN = prove
 (`!m:(A)native_result. native_bind m Value = m /\
                        native_bind m (\x. Value x) = m`,
  GEN_TAC THEN NATIVE_CASES_TAC `m:(A)native_result` THEN
  REWRITE_TAC[NATIVE_BIND]);;

let NATIVE_BIND_EQ_VALUE = prove
 (`!m (f:A->(B)native_result) y.
     native_bind m f = Value y <=> ?x. m = Value x /\ f x = Value y`,
  GEN_TAC THEN NATIVE_CASES_TAC `m:(A)native_result` THEN
  REWRITE_TAC[NATIVE_BIND; NATIVE_RESULT_DISTINCT; NATIVE_RESULT_INJ] THEN
  MESON_TAC[]);;

let NATIVE_BIND_NO_VALUE = prove
 (`!(m:(A)native_result) (g:A->(A)native_result).
     (!x. ~(m = Value x)) ==> native_bind m g = m`,
  GEN_TAC THEN NATIVE_CASES_TAC `m:(A)native_result` THEN
  REWRITE_TAC[NATIVE_BIND] THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[]);;

let NATIVE_BIND_CONG = prove
 (`!m (f:A->(B)native_result) g.
     (!x. m = Value x ==> f x = g x) ==> native_bind m f = native_bind m g`,
  GEN_TAC THEN NATIVE_CASES_TAC `m:(A)native_result` THEN
  REWRITE_TAC[NATIVE_BIND; NATIVE_RESULT_DISTINCT; NATIVE_RESULT_INJ] THEN
  MESON_TAC[]);;

let MAP_NATIVE_RESULT = prove
 (`(!(f:A->B) x. map_native_result f (Value x) = Value (f x)) /\
   (!(f:A->B) e. map_native_result f (Fault e) = Fault e) /\
   (!f:A->B. map_native_result f Nontermination = Nontermination)`,
  REWRITE_TAC[map_native_result_DEF]);;

let MAP_NATIVE_RESULT_AS_BIND = prove
 (`!(f:A->B) m. map_native_result f m = native_bind m (\x. Value (f x))`,
  REPEAT GEN_TAC THEN NATIVE_CASES_TAC `m:(A)native_result` THEN
  REWRITE_TAC[map_native_result_DEF; NATIVE_BIND]);;

(* ------------------------------------------------------------------------- *)
(* Options, reads, slots and bottom.                                         *)
(* ------------------------------------------------------------------------- *)

let TYPED_HOL_READ = prove
 (`(!x:A. typed_hol_read (SOME x) = Value x) /\
   typed_hol_read (NONE:(A)option) = Fault Bounds_Error`,
  REWRITE_TAC[typed_hol_read_DEF; isa_case_option]);;

let TYPED_HOL_READ_MAP_OPTION = prove
 (`!(f:A->B) x.
     typed_hol_read (isa_map_option f x) =
     map_native_result f (typed_hol_read x)`,
  GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[isa_map_option; TYPED_HOL_READ; MAP_NATIVE_RESULT]);;

let TYPED_HOL_SLOT_READ = prove
 (`(!x:A. typed_hol_slot_read (Native_Assigned x) = Value x) /\
   typed_hol_slot_read (Native_Unassigned:(A)native_slot) =
   Fault Bounds_Error`,
  REWRITE_TAC[typed_hol_slot_read_DEF; case_native_slot_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Statement blocks: native_finish, native_continue_bind, native_seq,        *)
(* native_if, typed_hol_let, typed_hol_algorithm.                            *)
(* ------------------------------------------------------------------------- *)

let NATIVE_FINISH = prove
 (`(!(s:S) (r:S->(R)native_result).
      native_finish (Value (Continue s)) r = r s) /\
   (!(v:R) (s:S) r. native_finish (Value (Return_Value v s)) r = Value v) /\
   (!e (r:S->(R)native_result). native_finish (Fault e) r = Fault e) /\
   (!r:S->(R)native_result. native_finish Nontermination r = Nontermination)`,
  REWRITE_TAC[native_finish_DEF; case_native_result_DEF;
              case_statement_outcome_DEF]);;

let NATIVE_CONTINUE_BIND = prove
 (`(!(s:S) (rest:S->((S,R)statement_outcome)native_result).
      native_continue_bind (Value (Continue s)) rest = rest s) /\
   (!(v:R) (s:S) rest.
      native_continue_bind (Value (Return_Value v s)) rest =
      Value (Return_Value v s)) /\
   (!e (rest:S->((S,R)statement_outcome)native_result).
      native_continue_bind (Fault e) rest = Fault e) /\
   (!rest:S->((S,R)statement_outcome)native_result.
      native_continue_bind Nontermination rest = Nontermination)`,
  REWRITE_TAC[native_continue_bind_DEF; case_native_result_DEF;
              case_statement_outcome_DEF]);;

let NATIVE_CONTINUE_BIND_ASSOC = prove
 (`!(m:((S,R)statement_outcome)native_result) f g.
     native_continue_bind (native_continue_bind m f) g =
     native_continue_bind m (\s. native_continue_bind (f s) g)`,
  GEN_TAC THEN NATIVE_CASES_TAC `m:((S,R)statement_outcome)native_result` THEN
  REWRITE_TAC[NATIVE_CONTINUE_BIND] THEN
  TRY(OUTCOME_CASES_TAC `a:(S,R)statement_outcome`) THEN
  REWRITE_TAC[NATIVE_CONTINUE_BIND]);;

let NATIVE_CONTINUE_BIND_CONTINUE = prove
 (`!m:((S,R)statement_outcome)native_result.
     native_continue_bind m (\s. Value (Continue s)) = m`,
  GEN_TAC THEN NATIVE_CASES_TAC `m:((S,R)statement_outcome)native_result` THEN
  REWRITE_TAC[NATIVE_CONTINUE_BIND] THEN
  TRY(OUTCOME_CASES_TAC `a:(S,R)statement_outcome`) THEN
  REWRITE_TAC[NATIVE_CONTINUE_BIND]);;

let NATIVE_CONTINUE_BIND_NO_CONTINUE = prove
 (`!(m:((S,R)statement_outcome)native_result) rest.
     (!s. ~(m = Value (Continue s))) ==> native_continue_bind m rest = m`,
  GEN_TAC THEN NATIVE_CASES_TAC `m:((S,R)statement_outcome)native_result` THEN
  REWRITE_TAC[NATIVE_CONTINUE_BIND] THEN
  OUTCOME_CASES_TAC `a:(S,R)statement_outcome` THEN
  REWRITE_TAC[NATIVE_CONTINUE_BIND; NATIVE_RESULT_INJ;
              STATEMENT_OUTCOME_INJ] THEN
  MESON_TAC[]);;

let NATIVE_SEQ = prove
 (`!(first:S->((S,R)statement_outcome)native_result) rest s.
     native_seq first rest s = native_continue_bind (first s) rest`,
  REWRITE_TAC[native_seq_DEF]);;

let NATIVE_IF = prove
 (`!(test:S->(bool)native_result)
    (thn:S->((S,R)statement_outcome)native_result) els s.
     native_if test thn els s =
     native_bind (test s) (\b. if b then thn s else els s)`,
  REWRITE_TAC[native_if_DEF]);;

let NATIVE_IF_VALUE = prove
 (`!(test:S->(bool)native_result)
    (thn:S->((S,R)statement_outcome)native_result) els s b.
     test s = Value b
     ==> native_if test thn els s = if b then thn s else els s`,
  SIMP_TAC[native_if_DEF; NATIVE_BIND]);;

let TYPED_HOL_LET = prove
 (`!(value:S->(A)native_result)
    (rest:A->S->((S,R)statement_outcome)native_result) s.
     typed_hol_let value rest s = native_bind (value s) (\a. rest a s)`,
  REWRITE_TAC[typed_hol_let_DEF; native_bind_DEF]);;

let TYPED_HOL_ALGORITHM = prove
 (`!(d:R) (native:S->((S,R)statement_outcome)native_result) s.
     typed_hol_algorithm d native s = native_finish (native s) (\x. Value d)`,
  REWRITE_TAC[typed_hol_algorithm_DEF; native_finish_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Integers and naturals: isa_nat, isa_int_div, isa_int_mod.                 *)
(* ------------------------------------------------------------------------- *)

let ISA_NAT_NUM = prove
 (`!n. isa_nat (&n) = n`,
  REWRITE_TAC[isa_nat; INT_POS; NUM_OF_INT_OF_NUM]);;

let ISA_NAT_POS = prove
 (`!x. &0 <= x ==> isa_nat x = num_of_int x`,
  SIMP_TAC[isa_nat]);;

let ISA_NAT_NEG = prove
 (`!x. x <= &0 ==> isa_nat x = 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[isa_nat] THEN COND_CASES_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `x:int = &0` SUBST1_TAC THENL
   [ASM_INT_ARITH_TAC; REWRITE_TAC[NUM_OF_INT_OF_NUM]]);;

let INT_OF_NUM_ISA_NAT = prove
 (`!x. &(isa_nat x) = if &0 <= x then x else &0`,
  GEN_TAC THEN REWRITE_TAC[isa_nat] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT]);;

let ISA_INT_DIV_POS = prove
 (`!a b. &0 <= b ==> isa_int_div a b = a div b`,
  SIMP_TAC[isa_int_div; INT_ARITH `&0:int <= b ==> ~(b < &0)`]);;

let ISA_INT_MOD_POS = prove
 (`!a b. &0 <= b ==> isa_int_mod a b = a rem b`,
  SIMP_TAC[isa_int_mod; INT_ARITH `&0:int <= b ==> ~(b < &0)`]);;

let ISA_INT_DIV_NUM = prove
 (`!a n. isa_int_div a (&n) = a div &n`,
  SIMP_TAC[ISA_INT_DIV_POS; INT_POS]);;

let ISA_INT_MOD_NUM = prove
 (`!a n. isa_int_mod a (&n) = a rem &n`,
  SIMP_TAC[ISA_INT_MOD_POS; INT_POS]);;

(* a < b gives b - a = SUC of b - (a + 1), else b - a is 0 as a natural.     *)

let ISA_NAT_SUB_SUC = prove
 (`!a b:int. a < b ==> isa_nat (b - a) = SUC (isa_nat (b - (a + &1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0:int <= b - a /\ &0 <= b - (a + &1)` STRIP_ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ISA_NAT_POS] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_SUC] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT] THEN INT_ARITH_TAC);;

let ISA_NAT_SUB_0 = prove
 (`!a b:int. ~(a < b) ==> isa_nat (b - a) = 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ISA_NAT_NEG THEN ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Typed integer, bit and byte operations.                                   *)
(* ------------------------------------------------------------------------- *)

let TYPED_HOL_NONNEGATIVE = prove
 (`(!n. typed_hol_nonnegative (&n) = Value (&n)) /\
   (!x. &0 <= x ==> typed_hol_nonnegative x = Value x) /\
   (!x. x < &0 ==> typed_hol_nonnegative x = Fault Bounds_Error)`,
  REWRITE_TAC[typed_hol_nonnegative_DEF; INT_POS] THEN
  SIMP_TAC[GSYM INT_NOT_LT]);;

let TYPED_HOL_BIT_VALUE = prove
 (`!b. typed_hol_bit_value b = Value (if b then &1 else &0)`,
  REWRITE_TAC[typed_hol_bit_value_DEF]);;

let TYPED_HOL_BYTE_VALUE = prove
 (`!b:byte. typed_hol_byte_value b = Value (&(val b))`,
  REWRITE_TAC[typed_hol_byte_value_DEF]);;

let TYPED_HOL_INT_TO_BIT = prove
 (`typed_hol_int_to_bit (&0) = Value F /\
   typed_hol_int_to_bit (&1) = Value T /\
   (!n. typed_hol_int_to_bit n =
        if &0 <= n /\ n < &2 then Value (n = &1) else Fault Bounds_Error)`,
  REWRITE_TAC[typed_hol_int_to_bit_DEF] THEN CONV_TAC INT_REDUCE_CONV);;

let TYPED_HOL_INT_TO_BYTE_NUM = prove
 (`!n. typed_hol_int_to_byte (&n) =
       if n < 256 then Value (word n) else Fault Bounds_Error`,
  REWRITE_TAC[typed_hol_int_to_byte_DEF; INT_POS; INT_OF_NUM_LT;
              GSYM WORD_IWORD]);;

let TYPED_HOL_INT_TO_BYTE = prove
 (`!n. typed_hol_int_to_byte n =
       if &0 <= n /\ n < &256 then Value (word (num_of_int n))
       else Fault Bounds_Error`,
  GEN_TAC THEN REWRITE_TAC[typed_hol_int_to_byte_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WORD_IWORD; INT_OF_NUM_OF_INT]);;

let TYPED_HOL_INT_ARITHMETIC = prove
 (`(!a b. typed_hol_int_arithmetic AAdd a b = Value (a + b)) /\
   (!a b. typed_hol_int_arithmetic ASub a b = Value (a - b)) /\
   (!a b. typed_hol_int_arithmetic AMul a b = Value (a * b)) /\
   (!a b. typed_hol_int_arithmetic ADiv a b =
          if b = &0 then Fault Bounds_Error else Value (isa_int_div a b)) /\
   (!a b. typed_hol_int_arithmetic AQuot a b =
          if b = &0 \/ ~(isa_int_mod a b = &0) then Fault Bounds_Error
          else Value (isa_int_div a b)) /\
   (!a b. typed_hol_int_arithmetic AMod a b =
          if b = &0 \/ b < &0 then Fault Bounds_Error
          else Value (isa_int_mod a b)) /\
   (!a b. typed_hol_int_arithmetic APow a b =
          if b < &0 then Fault Bounds_Error else Value (a pow isa_nat b))`,
  REWRITE_TAC[typed_hol_int_arithmetic_DEF; arith_faults_DEF; int_op_DEF;
              case_aop_DEF; distinctness "aop"]);;

(* For a positive divisor, the Isabelle div and mod are HOL Light's.         *)

let TYPED_HOL_INT_ARITHMETIC_POS = prove
 (`(!a b. &0 < b ==> typed_hol_int_arithmetic ADiv a b = Value (a div b)) /\
   (!a b. &0 < b ==> typed_hol_int_arithmetic AMod a b = Value (a rem b)) /\
   (!a n. typed_hol_int_arithmetic APow a (&n) = Value (a pow n))`,
  REWRITE_TAC[TYPED_HOL_INT_ARITHMETIC; ISA_NAT_NUM; INT_ARITH `~(&n:int < &0)`] THEN
  SIMP_TAC[INT_ARITH `&0:int < b ==> ~(b = &0) /\ ~(b < &0) /\ &0 <= b`;
           ISA_INT_DIV_POS; ISA_INT_MOD_POS; INT_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* The Isabelle list functions as HOL Light lists.                           *)
(* ------------------------------------------------------------------------- *)

let LIST_OF_SEQ_EQ = prove
 (`!(f:num->A) g n.
     (!i. i < n ==> f i = g i) ==> list_of_seq f n = list_of_seq g n`,
  SIMP_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let LIST_OF_SEQ_ADD = prove
 (`!(f:num->A) m n.
     list_of_seq f (m + n) =
     APPEND (list_of_seq f m) (list_of_seq (\i. f (m + i)) n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; list_of_seq; APPEND_NIL; APPEND_ASSOC]);;

let LENGTH_ISA_LIST_UPDATE = prove
 (`!(xs:A list) i a. LENGTH (isa_list_update xs i a) = LENGTH xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[isa_list_update] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH]);;

let EL_ISA_LIST_UPDATE = prove
 (`!(xs:A list) i a j.
     j < LENGTH xs
     ==> EL j (isa_list_update xs i a) = if j = i then a else EL j xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  REWRITE_TAC[isa_list_update] THEN REPEAT GEN_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[EL_CONS] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  ASM_SIMP_TAC[ARITH_RULE `j < SUC n /\ ~(j = 0) ==> j - 1 < n`] THEN
  ASM_ARITH_TAC);;

let ISA_LIST_UPDATE_LIST_OF_SEQ = prove
 (`!(f:num->A) n i a.
     isa_list_update (list_of_seq f n) i a =
     list_of_seq (\j. if j = i then a else f j) n`,
  REWRITE_TAC[LIST_EQ; LENGTH_ISA_LIST_UPDATE; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_ISA_LIST_UPDATE; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let LENGTH_ISA_TAKE = prove
 (`!n (xs:A list). LENGTH (isa_take n xs) = MIN n (LENGTH xs)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[isa_take; LENGTH] THENL [ARITH_TAC; ALL_TAC] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC);;

let EL_ISA_TAKE = prove
 (`!n (xs:A list) i. i < MIN n (LENGTH xs) ==> EL i (isa_take n xs) = EL i xs`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[isa_take; LENGTH] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `MIN 0 n = 0`; CONJUNCT1 LT] THEN
  REWRITE_TAC[EL_CONS] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let ISA_TAKE = prove
 (`!n (xs:A list). isa_take n xs = list_of_seq (\i. EL i xs) (MIN n (LENGTH xs))`,
  SIMP_TAC[LIST_EQ; LENGTH_ISA_TAKE; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ;
           EL_ISA_TAKE]);;

let LENGTH_ISA_DROP = prove
 (`!n (xs:A list). LENGTH (isa_drop n xs) = LENGTH xs - n`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[isa_drop; LENGTH; SUB_0] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC);;

let EL_ISA_DROP = prove
 (`!n (xs:A list) i. i < LENGTH xs - n ==> EL i (isa_drop n xs) = EL (n + i) xs`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[isa_drop; LENGTH; SUB_0; CONJUNCT1 LT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LENGTH; ADD_CLAUSES] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n - 1`; `i:num`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `n + i = SUC(n - 1 + i)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[EL; TL]]);;

let ISA_DROP = prove
 (`!n (xs:A list).
     isa_drop n xs = list_of_seq (\i. EL (n + i) xs) (LENGTH xs - n)`,
  SIMP_TAC[LIST_EQ; LENGTH_ISA_DROP; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ;
           EL_ISA_DROP]);;

let ISA_UPT = prove
 (`!i j. isa_upt i j = list_of_seq (\k. i + k) (j - i)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[isa_upt; SUB_0; list_of_seq] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[ARITH_RULE `i <= j ==> SUC j - i = SUC(j - i)`] THEN
    REWRITE_TAC[list_of_seq] THEN AP_TERM_TAC THEN
    REWRITE_TAC[CONS_11] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE `~(i <= j) ==> SUC j - i = 0`; list_of_seq]]);;

let LENGTH_ISA_UPT = prove
 (`!i j. LENGTH (isa_upt i j) = j - i`,
  REWRITE_TAC[ISA_UPT; LENGTH_LIST_OF_SEQ]);;

let MAP_ISA_UPT = prove
 (`!(f:num->A) i j. MAP f (isa_upt i j) = list_of_seq (\k. f (i + k)) (j - i)`,
  REWRITE_TAC[ISA_UPT; MAP_LIST_OF_SEQ; o_DEF]);;

let ISA_CONCAT = prove
 (`!l:(A list)list. isa_concat l = ITLIST APPEND l []`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[isa_concat; ITLIST]);;

let ISA_CONCAT_APPEND = prove
 (`!l1 l2:(A list)list.
     isa_concat (APPEND l1 l2) = APPEND (isa_concat l1) (isa_concat l2)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[isa_concat; APPEND; APPEND_ASSOC]);;

let LENGTH_ISA_CONCAT_CONST = prove
 (`!m (l:(A list)list).
     ALL (\x. LENGTH x = m) l ==> LENGTH (isa_concat l) = m * LENGTH l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[isa_concat; ALL; LENGTH; LENGTH_APPEND; MULT_CLAUSES] THEN
  ARITH_TAC);;

let EL_ISA_CONCAT_CONST = prove
 (`!m (l:(A list)list) i j.
     ALL (\x. LENGTH x = m) l /\ i < LENGTH l /\ j < m
     ==> EL (m * i + j) (isa_concat l) = EL j (EL i l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  REWRITE_TAC[ALL; isa_concat] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; EL; HD; TL; EL_APPEND] THEN
  ASM_SIMP_TAC[ARITH_RULE `~((a + b) + c < a)`;
               ARITH_RULE `((a + b) + c) - a = b + c`] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Indexing, update and slices on in-range indices.                          *)
(* ------------------------------------------------------------------------- *)

let NATIVE_LIST_INDEX_NUM = prove
 (`!(xs:A list) i.
     native_list_index xs (&i) =
     if i < LENGTH xs then SOME (EL i xs) else NONE`,
  REWRITE_TAC[native_list_index_DEF; INT_POS; INT_OF_NUM_LT; ISA_NAT_NUM]);;

let NATIVE_LIST_INDEX = prove
 (`!(xs:A list) i.
     native_list_index xs i =
     if &0 <= i /\ i < &(LENGTH xs) then SOME (EL (num_of_int i) xs)
     else NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[native_list_index_DEF] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[ISA_NAT_POS]);;

let NATIVE_LIST_UPDATE_NUM = prove
 (`!(xs:A list) i a.
     native_list_update xs (&i) a =
     if i < LENGTH xs then SOME (isa_list_update xs i a) else NONE`,
  REWRITE_TAC[native_list_update_DEF; INT_POS; INT_OF_NUM_LT; ISA_NAT_NUM]);;

let TYPED_HOL_LIST_SLICE_NUM = prove
 (`!(xs:A list) l u.
     typed_hol_list_slice xs (&l) (&u) =
     if l <= u /\ u <= LENGTH xs
     then SOME (list_of_seq (\i. EL (l + i) xs) (u - l))
     else NONE`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[typed_hol_list_slice_DEF; INT_POS; INT_OF_NUM_LE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB; ISA_NAT_NUM; ISA_TAKE; ISA_DROP;
               LENGTH_LIST_OF_SEQ] THEN
  REWRITE_TAC[option_INJ] THEN
  SUBGOAL_THEN `MIN (u - l) (LENGTH(xs:A list) - l) = u - l` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC EL_LIST_OF_SEQ THEN ASM_ARITH_TAC);;

let TYPED_HOL_NESTED_UPDATE_NUM = prove
 (`!(inner:A->(A)option) xs i.
     typed_hol_nested_update inner xs (&i) =
     if i < LENGTH xs
     then isa_map_option (\y. isa_list_update xs i y) (inner (EL i xs))
     else NONE`,
  REWRITE_TAC[typed_hol_nested_update_DEF; INT_POS; INT_OF_NUM_LT;
              ISA_NAT_NUM]);;

let TYPED_HOL_SEQUENCE_EXTENT = prove
 (`!n (xs:A list). LENGTH xs = n ==> typed_hol_sequence_extent n xs = Value xs`,
  SIMP_TAC[typed_hol_sequence_extent_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Counted loops. A schedule is the list of indices of a FOR loop.           *)
(* ------------------------------------------------------------------------- *)

let NATIVE_SCHEDULE_INT = prove
 (`!n a b.
     native_schedule n (\i. i < b) (\i. i + &1) a =
     list_of_seq (\k. a + &k) (MIN n (isa_nat (b - a)))`,
  INDUCT_TAC THEN REWRITE_TAC[native_schedule_DEF] THEN
  REWRITE_TAC[ARITH_RULE `MIN 0 n = 0`; list_of_seq] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[ISA_NAT_SUB_SUC; ARITH_RULE `MIN (SUC n) (SUC m) = SUC(MIN n m)`;
                 LIST_OF_SEQ; CONS_11] THEN
    CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC;
    ASM_SIMP_TAC[ISA_NAT_SUB_0; ARITH_RULE `MIN n 0 = 0`; list_of_seq]]);;

let MIN_SUC_SELF = prove
 (`!n. MIN (SUC n) n = n`,
  ARITH_TAC);;

let NATIVE_SCHEDULE_UPTO = prove
 (`!a b. native_schedule (SUC (isa_nat (b - a))) (\i. i < b) (\i. i + &1) a =
         list_of_seq (\k. a + &k) (isa_nat (b - a))`,
  REWRITE_TAC[NATIVE_SCHEDULE_INT; MIN_SUC_SELF]);;

let NATIVE_SCHEDULE_NUM = prove
 (`!n m. m <= n
         ==> native_schedule n (\(i:int). i < &m) (\i. i + &1) (&0) =
             list_of_seq (\k. &k:int) m`,
  SIMP_TAC[NATIVE_SCHEDULE_INT; INT_SUB_RZERO; ISA_NAT_NUM; INT_ADD_LID;
           ARITH_RULE `m <= n ==> MIN n m = m`; ETA_AX]);;

(* The conversion: the bound in the schedule as a numeral or the obvious     *)
(* term, and the start &0 dropped from a + &k.                               *)

let NATIVE_SCHEDULE_CONV =
  let bound_conv =
    REWRITE_CONV[INT_SUB_RZERO; ISA_NAT_NUM; MIN_SUC_SELF] THENC
    DEPTH_CONV INT_RED_CONV THENC
    REWRITE_CONV[ISA_NAT_NUM; MIN_SUC_SELF] THENC
    (fun tm -> if is_numeral (rand tm) && is_numeral (lhand tm)
               then (REWRITE_CONV[MIN] THENC NUM_REDUCE_CONV THENC
                     REWRITE_CONV[]) tm
               else REFL tm) in
  GEN_REWRITE_CONV I [NATIVE_SCHEDULE_INT] THENC
  RAND_CONV bound_conv THENC
  LAND_CONV (ABS_CONV (TRY_CONV (REWR_CONV INT_ADD_LID)));;

(* native_foldl and native_fold over appended lists.                         *)

let NATIVE_FOLDL_APPEND = prove
 (`!(body:I->S->(S)native_result) l1 l2 s.
     native_foldl body (APPEND l1 l2) s =
     native_bind (native_foldl body l1 s) (native_foldl body l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; native_foldl_DEF; NATIVE_BIND; NATIVE_BIND_ASSOC] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  ASM_REWRITE_TAC[]);;

let NATIVE_FOLD_APPEND = prove
 (`!(body:I->S->((S,R)statement_outcome)native_result) l1 l2 s.
     native_fold body (APPEND l1 l2) s =
     native_continue_bind (native_fold body l1 s) (native_fold body l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; native_fold_DEF; NATIVE_SEQ; NATIVE_CONTINUE_BIND;
                  NATIVE_CONTINUE_BIND_ASSOC] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  ASM_REWRITE_TAC[]);;

(* A counted loop whose k-th step maps state st k to st (k + 1).             *)

let NATIVE_FOLDL_LIST_OF_SEQ = prove
 (`!(body:I->S->(S)native_result) (f:num->I) n (st:num->S).
     (!k. k < n ==> body (f k) (st k) = Value (st (SUC k)))
     ==> native_foldl body (list_of_seq f n) (st 0) = Value (st n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; native_foldl_DEF] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[NATIVE_FOLDL_APPEND] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `st:num->S`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `k < n ==> k < SUC n`]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[NATIVE_BIND; native_foldl_DEF; ARITH_RULE `n < SUC n`]);;

(* The same with an invariant P k s of the state after k steps.              *)

let NATIVE_FOLDL_INVARIANT = prove
 (`!(body:I->S->(S)native_result) (f:num->I) n P s0.
     P 0 s0 /\
     (!k s. k < n /\ P k s ==> ?s'. body (f k) s = Value s' /\ P (SUC k) s')
     ==> ?s. native_foldl body (list_of_seq f n) s0 = Value s /\ P n s`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; native_foldl_DEF; NATIVE_RESULT_INJ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[NATIVE_FOLDL_APPEND] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`P:num->S->bool`; `s0:S`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `k < n ==> k < SUC n`]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:S` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[NATIVE_BIND; native_foldl_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:S`]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `n < SUC n`] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':S` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[NATIVE_BIND; native_foldl_DEF; NATIVE_RESULT_INJ] THEN
  ASM_MESON_TAC[]);;

(* A counted loop whose step m (m < n) does not return a value.              *)

let NATIVE_FOLDL_LIST_OF_SEQ_EXIT = prove
 (`!(body:I->S->(S)native_result) (f:num->I) n m (st:num->S).
     (!k. k < m ==> body (f k) (st k) = Value (st (SUC k))) /\ m < n /\
     (!x. ~(body (f m) (st m) = Value x))
     ==> native_foldl body (list_of_seq f n) (st 0) = body (f m) (st m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n = SUC m + (n - SUC m)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LIST_OF_SEQ_ADD; NATIVE_FOLDL_APPEND] THEN
  REWRITE_TAC[list_of_seq; NATIVE_FOLDL_APPEND] THEN
  MP_TAC(ISPECL [`body:I->S->(S)native_result`; `f:num->I`; `m:num`;
                 `st:num->S`] NATIVE_FOLDL_LIST_OF_SEQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NATIVE_BIND; native_foldl_DEF; NATIVE_BIND_ASSOC] THEN
  MATCH_MP_TAC NATIVE_BIND_NO_VALUE THEN ASM_REWRITE_TAC[]);;

let NATIVE_FOLD_LIST_OF_SEQ = prove
 (`!(body:I->S->((S,R)statement_outcome)native_result) (f:num->I) n
    (st:num->S).
     (!k. k < n ==> body (f k) (st k) = Value (Continue (st (SUC k))))
     ==> native_fold body (list_of_seq f n) (st 0) = Value (Continue (st n))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; native_fold_DEF] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[NATIVE_FOLD_APPEND] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `st:num->S`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `k < n ==> k < SUC n`]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[NATIVE_CONTINUE_BIND; native_fold_DEF; NATIVE_SEQ;
               ARITH_RULE `n < SUC n`]);;

(* A counted statement loop that returns, faults or diverges in step m.      *)

let NATIVE_FOLD_LIST_OF_SEQ_EXIT = prove
 (`!(body:I->S->((S,R)statement_outcome)native_result) (f:num->I) n m
    (st:num->S).
     (!k. k < m ==> body (f k) (st k) = Value (Continue (st (SUC k)))) /\
     m < n /\ (!s. ~(body (f m) (st m) = Value (Continue s)))
     ==> native_fold body (list_of_seq f n) (st 0) = body (f m) (st m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n = SUC m + (n - SUC m)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LIST_OF_SEQ_ADD; NATIVE_FOLD_APPEND] THEN
  REWRITE_TAC[list_of_seq; NATIVE_FOLD_APPEND] THEN
  MP_TAC(ISPECL [`body:I->S->((S,R)statement_outcome)native_result`;
                 `f:num->I`; `m:num`; `st:num->S`] NATIVE_FOLD_LIST_OF_SEQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NATIVE_CONTINUE_BIND; native_fold_DEF; NATIVE_SEQ;
              NATIVE_CONTINUE_BIND_ASSOC] THEN
  MATCH_MP_TAC NATIVE_CONTINUE_BIND_NO_CONTINUE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* While loops: native_iter is hol_light_iterate with enough fuel, or        *)
(* Nontermination if no fuel suffices.                                       *)
(* ------------------------------------------------------------------------- *)

let HOL_LIGHT_ITERATE = prove
 (`(!(step:S->((S,A)iteration_outcome)native_result) s.
      hol_light_iterate 0 step s = Nontermination) /\
   (!n (step:S->((S,A)iteration_outcome)native_result) s a.
      step s = Value (Finished a) ==> hol_light_iterate (SUC n) step s = Value a) /\
   (!n (step:S->((S,A)iteration_outcome)native_result) s s'.
      step s = Value (Again s')
      ==> hol_light_iterate (SUC n) step s = hol_light_iterate n step s') /\
   (!n (step:S->((S,A)iteration_outcome)native_result) s e.
      step s = Fault e ==> hol_light_iterate (SUC n) step s = Fault e) /\
   (!n (step:S->((S,A)iteration_outcome)native_result) s.
      step s = Nontermination
      ==> hol_light_iterate (SUC n) step s = Nontermination)`,
  SIMP_TAC[hol_light_iterate_DEF; case_native_result_DEF;
           case_iteration_outcome_DEF]);;

let HOL_LIGHT_ITERATE_MONO = prove
 (`!n m (step:S->((S,A)iteration_outcome)native_result) s.
     ~(hol_light_iterate n step s = Nontermination) /\ n <= m
     ==> hol_light_iterate m step s = hol_light_iterate n step s`,
  INDUCT_TAC THEN REWRITE_TAC[HOL_LIGHT_ITERATE] THEN
  INDUCT_TAC THEN REWRITE_TAC[ARITH_RULE `~(SUC n <= 0)`; LE_SUC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[hol_light_iterate_DEF] THEN
  NATIVE_CASES_TAC `(step:S->((S,A)iteration_outcome)native_result) s` THEN
  REWRITE_TAC[case_native_result_DEF] THEN
  TRY(ITERATION_CASES_TAC `a:(S,A)iteration_outcome`) THEN
  REWRITE_TAC[case_iteration_outcome_DEF] THEN ASM_MESON_TAC[]);;

(* The four shapes of the result of an iteration step.                       *)

let ITER_STEP_CASES = prove
 (`!r:((S,A)iteration_outcome)native_result.
     (?a. r = Value (Finished a)) \/ (?s. r = Value (Again s)) \/
     (?e. r = Fault e) \/ r = Nontermination`,
  GEN_TAC THEN
  NATIVE_CASES_TAC `r:((S,A)iteration_outcome)native_result` THEN
  REWRITE_TAC[NATIVE_RESULT_DISTINCT; NATIVE_RESULT_INJ] THEN
  TRY(ITERATION_CASES_TAC `a:(S,A)iteration_outcome`) THEN
  REWRITE_TAC[ITERATION_OUTCOME_DISTINCT; ITERATION_OUTCOME_INJ] THEN
  MESON_TAC[]);;

let NATIVE_ITER_EQ = prove
 (`!n (step:S->((S,A)iteration_outcome)native_result) s.
     ~(hol_light_iterate n step s = Nontermination)
     ==> native_iter step s = hol_light_iterate n step s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[native_iter_DEF] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN
  ABBREV_TAC `m = @n. ~(hol_light_iterate n (step:S->((S,A)iteration_outcome)native_result) s = Nontermination)` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`m:num`; `m + n:num`; `step:S->((S,A)iteration_outcome)native_result`; `s:S`]
         HOL_LIGHT_ITERATE_MONO) THEN
  MP_TAC(ISPECL [`n:num`; `m + n:num`; `step:S->((S,A)iteration_outcome)native_result`; `s:S`]
         HOL_LIGHT_ITERATE_MONO) THEN
  ASM_REWRITE_TAC[LE_ADD; LE_ADDR] THEN MESON_TAC[]);;

let NATIVE_ITER_NONTERM = prove
 (`!(step:S->((S,A)iteration_outcome)native_result) s.
     (!n. hol_light_iterate n step s = Nontermination)
     ==> native_iter step s = Nontermination`,
  SIMP_TAC[native_iter_DEF]);;

let NATIVE_ITER_FINISHED = prove
 (`!(step:S->((S,A)iteration_outcome)native_result) s a.
     step s = Value (Finished a) ==> native_iter step s = Value a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`SUC 0`; `step:S->((S,A)iteration_outcome)native_result`;
                 `s:S`] NATIVE_ITER_EQ) THEN
  ASM_SIMP_TAC[HOL_LIGHT_ITERATE; NATIVE_RESULT_DISTINCT]);;

let NATIVE_ITER_FAULT = prove
 (`!(step:S->((S,A)iteration_outcome)native_result) s e.
     step s = Fault e ==> native_iter step s = Fault e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`SUC 0`; `step:S->((S,A)iteration_outcome)native_result`;
                 `s:S`] NATIVE_ITER_EQ) THEN
  ASM_SIMP_TAC[HOL_LIGHT_ITERATE; NATIVE_RESULT_DISTINCT]);;

let NATIVE_ITER_NONTERMINATION = prove
 (`!(step:S->((S,A)iteration_outcome)native_result) s.
     step s = Nontermination ==> native_iter step s = Nontermination`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NATIVE_ITER_NONTERM THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[HOL_LIGHT_ITERATE]);;

let NATIVE_ITER_AGAIN = prove
 (`!(step:S->((S,A)iteration_outcome)native_result) s s'.
     step s = Value (Again s') ==> native_iter step s = native_iter step s'`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC
   `?n. ~(hol_light_iterate n (step:S->((S,A)iteration_outcome)native_result)
                            s' = Nontermination)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `n:num`) THEN
    MP_TAC(ISPECL [`n:num`; `step:S->((S,A)iteration_outcome)native_result`;
                   `s':S`] NATIVE_ITER_EQ) THEN
    MP_TAC(ISPECL [`SUC n`; `step:S->((S,A)iteration_outcome)native_result`;
                   `s:S`] NATIVE_ITER_EQ) THEN
    ASM_SIMP_TAC[HOL_LIGHT_ITERATE];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_SIMP_TAC[NATIVE_ITER_NONTERM] THEN MATCH_MP_TAC NATIVE_ITER_NONTERM THEN
    INDUCT_TAC THEN ASM_SIMP_TAC[HOL_LIGHT_ITERATE]]);;

(* One-step unfolding of native_iter.                                        *)

let NATIVE_ITER = prove
 (`!(step:S->((S,A)iteration_outcome)native_result) s.
     native_iter step s =
     native_bind (step s)
      (\r. case_iteration_outcome (\a. Value a) (\s'. native_iter step s') r)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `(step:S->((S,A)iteration_outcome)native_result) s`
               ITER_STEP_CASES) THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[NATIVE_ITER_FINISHED; NATIVE_ITER_FAULT;
               NATIVE_ITER_NONTERMINATION; NATIVE_BIND;
               case_iteration_outcome_DEF] THEN
  FIRST_ASSUM(ACCEPT_TAC o MATCH_MP NATIVE_ITER_AGAIN));;

(* A loop that goes from st 0 through st k (k < K) to st K.                  *)

let NATIVE_ITER_STEPS = prove
 (`!(step:S->((S,A)iteration_outcome)native_result) st K.
     (!k. k < K ==> step (st k) = Value (Again (st (SUC k))))
     ==> native_iter step (st 0) = native_iter step (st K)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `k < K ==> k < SUC K`]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC NATIVE_ITER_AGAIN THEN
  ASM_MESON_TAC[ARITH_RULE `K < SUC K`]);;

let NATIVE_ITER_DIVERGE = prove
 (`!(step:S->((S,A)iteration_outcome)native_result) (st:num->S).
     (!k. step (st k) = Value (Again (st (SUC k))))
     ==> native_iter step (st 0) = Nontermination`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NATIVE_ITER_NONTERM THEN
  SUBGOAL_THEN
   `!n k. hol_light_iterate n (step:S->((S,A)iteration_outcome)native_result)
                            ((st:num->S) k) = Nontermination`
   (fun th -> REWRITE_TAC[th]) THEN
  INDUCT_TAC THEN REWRITE_TAC[hol_light_iterate_DEF] THEN
  ASM_REWRITE_TAC[case_native_result_DEF; case_iteration_outcome_DEF]);;

(* Total correctness: an invariant P and a measure m that decreases.         *)

let NATIVE_ITER_VARIANT = prove
 (`!(step:S->((S,A)iteration_outcome)native_result) P Q (msr:S->num) s.
     P s /\
     (!s. P s
          ==> (?a. step s = Value (Finished a) /\ Q a) \/
              (?s'. step s = Value (Again s') /\ P s' /\ msr s' < msr s))
     ==> ?a. native_iter step s = Value a /\ Q a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n s. (msr:S->num) s = n /\ (P:S->bool) s
          ==> ?a. native_iter (step:S->((S,A)iteration_outcome)native_result)
                              s = Value a /\ (Q:A->bool) a`
   (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `t:S` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `t:S` th) THEN
                          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[NATIVE_ITER_FINISHED];
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP NATIVE_ITER_AGAIN) THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* native_while with the trivial pre-statement (the only form generated),    *)
(* native_loop and native_indexed_while: unfolding, and the forms for a loop *)
(* that exits after K steps, never exits, or has a variant.                  *)
(* ------------------------------------------------------------------------- *)

let NATIVE_WHILE = prove
 (`!(test:S->(bool)native_result)
    (body:S->((S,R)statement_outcome)native_result) s.
     native_while (\s. Value (Continue s)) test body s =
     native_bind (test s)
      (\b. if b then native_continue_bind (body s)
                      (native_while (\s. Value (Continue s)) test body)
           else Value (Continue s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[native_while_DEF] THEN
  GEN_REWRITE_TAC LAND_CONV [NATIVE_ITER] THEN
  REWRITE_TAC[native_while_step_DEF; case_native_result_DEF;
              case_statement_outcome_DEF] THEN
  NATIVE_CASES_TAC `(test:S->(bool)native_result) s` THEN
  REWRITE_TAC[case_native_result_DEF; NATIVE_BIND] THEN
  BOOL_CASES_TAC `a:bool` THEN
  REWRITE_TAC[NATIVE_BIND; case_iteration_outcome_DEF] THEN
  NATIVE_CASES_TAC `(body:S->((S,R)statement_outcome)native_result) s` THEN
  REWRITE_TAC[case_native_result_DEF; NATIVE_BIND; NATIVE_CONTINUE_BIND] THEN
  OUTCOME_CASES_TAC `a:(S,R)statement_outcome` THEN
  REWRITE_TAC[case_statement_outcome_DEF; NATIVE_BIND; NATIVE_CONTINUE_BIND;
              case_iteration_outcome_DEF]);;

let NATIVE_WHILE_EXIT = prove
 (`!(test:S->(bool)native_result)
    (body:S->((S,R)statement_outcome)native_result) s.
     test s = Value F
     ==> native_while (\s. Value (Continue s)) test body s = Value (Continue s)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [NATIVE_WHILE] THEN
  ASM_REWRITE_TAC[NATIVE_BIND]);;

let NATIVE_WHILE_STEPS = prove
 (`!(test:S->(bool)native_result)
    (body:S->((S,R)statement_outcome)native_result) st K.
     (!k. k < K ==> test (st k) = Value T /\
                    body (st k) = Value (Continue (st (SUC k))))
     ==> native_while (\s. Value (Continue s)) test body (st 0) =
         native_while (\s. Value (Continue s)) test body (st K)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `k < K ==> k < SUC K`]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN GEN_REWRITE_TAC LAND_CONV [NATIVE_WHILE] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `K:num`) THEN REWRITE_TAC[ARITH_RULE `K < SUC K`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NATIVE_BIND; NATIVE_CONTINUE_BIND]);;

let NATIVE_WHILE_DIVERGE = prove
 (`!(test:S->(bool)native_result)
    (body:S->((S,R)statement_outcome)native_result) st.
     (!k. test (st k) = Value T /\ body (st k) = Value (Continue (st (SUC k))))
     ==> native_while (\s. Value (Continue s)) test body (st 0) =
         Nontermination`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[native_while_DEF] THEN
  MATCH_MP_TAC NATIVE_ITER_DIVERGE THEN
  ASM_REWRITE_TAC[native_while_step_DEF; case_native_result_DEF;
                  case_statement_outcome_DEF]);;

let NATIVE_WHILE_VARIANT = prove
 (`!(test:S->(bool)native_result)
    (body:S->((S,R)statement_outcome)native_result) P Q (msr:S->num) s.
     P s /\
     (!s. P s
          ==> (test s = Value F /\ Q s) \/
              (test s = Value T /\
               ?s'. body s = Value (Continue s') /\ P s' /\ msr s' < msr s))
     ==> ?s'. native_while (\s. Value (Continue s)) test body s =
              Value (Continue s') /\ Q s'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n s. (msr:S->num) s = n /\ (P:S->bool) s
          ==> ?s'. native_while (\s. Value (Continue s)) test
                     (body:S->((S,R)statement_outcome)native_result) s =
                   Value (Continue s') /\ (Q:S->bool) s'`
   (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `t:S` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `t:S` th) THEN
                          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  STRIP_TAC THEN GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o LAND_CONV)
   [NATIVE_WHILE] THEN
  ASM_REWRITE_TAC[NATIVE_BIND; NATIVE_CONTINUE_BIND; NATIVE_RESULT_INJ;
                  STATEMENT_OUTCOME_INJ] THEN
  ASM_MESON_TAC[]);;

let NATIVE_LOOP = prove
 (`!(test:S->(bool)native_result) (body:S->(S)native_result) s.
     native_loop test body s =
     native_bind (test s)
      (\b. if b then native_bind (body s) (native_loop test body)
           else Value s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[native_loop_DEF] THEN
  GEN_REWRITE_TAC LAND_CONV [NATIVE_ITER] THEN
  REWRITE_TAC[native_loop_step_DEF; NATIVE_BIND_ASSOC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `b:bool` THEN
  BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[NATIVE_BIND; case_iteration_outcome_DEF;
              MAP_NATIVE_RESULT_AS_BIND; NATIVE_BIND_ASSOC] THEN
  REWRITE_TAC[case_iteration_outcome_DEF; native_loop_DEF; ETA_AX]);;

let NATIVE_LOOP_EXIT = prove
 (`!(test:S->(bool)native_result) (body:S->(S)native_result) s.
     test s = Value F ==> native_loop test body s = Value s`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [NATIVE_LOOP] THEN
  ASM_REWRITE_TAC[NATIVE_BIND]);;

let NATIVE_LOOP_STEPS = prove
 (`!(test:S->(bool)native_result) (body:S->(S)native_result) st K.
     (!k. k < K ==> test (st k) = Value T /\ body (st k) = Value (st (SUC k)))
     ==> native_loop test body (st 0) = native_loop test body (st K)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `k < K ==> k < SUC K`]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN GEN_REWRITE_TAC LAND_CONV [NATIVE_LOOP] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `K:num`) THEN REWRITE_TAC[ARITH_RULE `K < SUC K`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NATIVE_BIND]);;

let NATIVE_LOOP_DIVERGE = prove
 (`!(test:S->(bool)native_result) (body:S->(S)native_result) st.
     (!k. test (st k) = Value T /\ body (st k) = Value (st (SUC k)))
     ==> native_loop test body (st 0) = Nontermination`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[native_loop_DEF] THEN
  MATCH_MP_TAC NATIVE_ITER_DIVERGE THEN
  ASM_REWRITE_TAC[native_loop_step_DEF; NATIVE_BIND; MAP_NATIVE_RESULT]);;

let NATIVE_LOOP_VARIANT = prove
 (`!(test:S->(bool)native_result) (body:S->(S)native_result) P Q (msr:S->num) s.
     P s /\
     (!s. P s
          ==> (test s = Value F /\ Q s) \/
              (test s = Value T /\
               ?s'. body s = Value s' /\ P s' /\ msr s' < msr s))
     ==> ?s'. native_loop test body s = Value s' /\ Q s'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n s. (msr:S->num) s = n /\ (P:S->bool) s
          ==> ?s'. native_loop test (body:S->(S)native_result) s = Value s' /\
                   (Q:S->bool) s'`
   (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `t:S` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `t:S` th) THEN
                          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  STRIP_TAC THEN GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o LAND_CONV)
   [NATIVE_LOOP] THEN
  ASM_REWRITE_TAC[NATIVE_BIND; NATIVE_RESULT_INJ] THEN ASM_MESON_TAC[]);;

let NATIVE_INDEXED_WHILE = prove
 (`!(test:I->S->(bool)native_result) next
    (body:I->S->((S,R)statement_outcome)native_result) i s.
     native_indexed_while test next body i s =
     native_bind (test i s)
      (\b. if b then native_continue_bind (body i s)
                      (native_indexed_while test next body (next i))
           else Value (Continue s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[native_indexed_while_DEF] THEN
  GEN_REWRITE_TAC LAND_CONV [NATIVE_ITER] THEN
  REWRITE_TAC[native_indexed_step_DEF; case_native_result_DEF;
              case_statement_outcome_DEF; FST; SND] THEN
  NATIVE_CASES_TAC `(test:I->S->(bool)native_result) i s` THEN
  REWRITE_TAC[case_native_result_DEF; NATIVE_BIND] THEN
  BOOL_CASES_TAC `a:bool` THEN
  REWRITE_TAC[NATIVE_BIND; case_iteration_outcome_DEF] THEN
  NATIVE_CASES_TAC `(body:I->S->((S,R)statement_outcome)native_result) i s` THEN
  REWRITE_TAC[case_native_result_DEF; NATIVE_BIND; NATIVE_CONTINUE_BIND] THEN
  OUTCOME_CASES_TAC `a:(S,R)statement_outcome` THEN
  REWRITE_TAC[case_statement_outcome_DEF; NATIVE_BIND; NATIVE_CONTINUE_BIND;
              case_iteration_outcome_DEF; native_indexed_while_DEF]);;

let NATIVE_INDEXED_WHILE_EXIT = prove
 (`!(test:I->S->(bool)native_result) next
    (body:I->S->((S,R)statement_outcome)native_result) i s.
     test i s = Value F
     ==> native_indexed_while test next body i s = Value (Continue s)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [NATIVE_INDEXED_WHILE] THEN
  ASM_REWRITE_TAC[NATIVE_BIND]);;

let NATIVE_INDEXED_WHILE_STEPS = prove
 (`!(test:I->S->(bool)native_result) next
    (body:I->S->((S,R)statement_outcome)native_result) ix st K.
     (!k. k < K ==> ix (SUC k) = next (ix k) /\
                    test (ix k) (st k) = Value T /\
                    body (ix k) (st k) = Value (Continue (st (SUC k))))
     ==> native_indexed_while test next body (ix 0) (st 0) =
         native_indexed_while test next body (ix K) (st K)`,
  REPLICATE_TAC 5 GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `k < K ==> k < SUC K`]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN GEN_REWRITE_TAC LAND_CONV [NATIVE_INDEXED_WHILE] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `K:num`) THEN REWRITE_TAC[ARITH_RULE `K < SUC K`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NATIVE_BIND; NATIVE_CONTINUE_BIND]);;

let NATIVE_INDEXED_WHILE_VARIANT = prove
 (`!(test:I->S->(bool)native_result) next
    (body:I->S->((S,R)statement_outcome)native_result) P Q (msr:I->S->num) i s.
     P i s /\
     (!i s. P i s
            ==> (test i s = Value F /\ Q s) \/
                (test i s = Value T /\
                 ?s'. body i s = Value (Continue s') /\ P (next i) s' /\
                      msr (next i) s' < msr i s))
     ==> ?s'. native_indexed_while test next body i s = Value (Continue s') /\
              Q s'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n i s. (msr:I->S->num) i s = n /\ (P:I->S->bool) i s
            ==> ?s'. native_indexed_while test next
                       (body:I->S->((S,R)statement_outcome)native_result) i s =
                     Value (Continue s') /\ (Q:S->bool) s'`
   (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`j:I`; `t:S`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`j:I`; `t:S`] th) THEN
                          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  STRIP_TAC THEN GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o LAND_CONV)
   [NATIVE_INDEXED_WHILE] THEN
  ASM_REWRITE_TAC[NATIVE_BIND; NATIVE_CONTINUE_BIND; NATIVE_RESULT_INJ;
                  STATEMENT_OUTCOME_INJ] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Residues: the phantom type parameter is the modulus, via dimindex.        *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_Q = DIMINDEX_CONV `dimindex(:8380417)`;;

let DIMINDEX_2 = DIMINDEX_CONV `dimindex(:2)`;;

let RESIDUE_REP_OF_INT_MOD = prove
 (`!x. &(residue_rep (residue_of_int_mod x:(Q)residue)) =
       x rem &(dimindex(:Q))`,
  GEN_TAC THEN
  REWRITE_TAC[residue_of_int_mod_DEF; residue_SEL_CTR; ISA_INT_MOD_NUM;
              INT_OF_NUM_ISA_NAT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  SIMP_TAC[INT_REM_POS_EQ; INT_OF_NUM_EQ; DIMINDEX_NONZERO]);;

let RESIDUE_REP_OF_INT_MOD_NUM = prove
 (`!x. residue_rep (residue_of_int_mod x:(Q)residue) =
       num_of_int (x rem &(dimindex(:Q)))`,
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; RESIDUE_REP_OF_INT_MOD] THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_REM_POS; INT_OF_NUM_EQ; DIMINDEX_NONZERO]);;

let RESIDUE_OF_INT_MOD_EQ = prove
 (`!x y. (residue_of_int_mod x:(Q)residue) = residue_of_int_mod y <=>
         x rem &(dimindex(:Q)) = y rem &(dimindex(:Q))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o BINOP_CONV) [GSYM RESIDUE_REP_OF_INT_MOD] THEN
  REWRITE_TAC[INT_OF_NUM_EQ] THEN
  MESON_TAC[residue_INJECT; residue_CTR_SEL]);;

let RESIDUE_OF_INT_MOD_CONG = prove
 (`!x y. (x == y) (mod &(dimindex(:Q)))
         ==> (residue_of_int_mod x:(Q)residue) = residue_of_int_mod y`,
  REWRITE_TAC[RESIDUE_OF_INT_MOD_EQ; INT_REM_EQ]);;

let RESIDUE_OF_INT_MOD_REM = prove
 (`!x. (residue_of_int_mod (x rem &(dimindex(:Q))):(Q)residue) =
       residue_of_int_mod x`,
  REWRITE_TAC[RESIDUE_OF_INT_MOD_EQ; INT_REM_REM]);;

let RESIDUE_OF_INT_MOD_NUM = prove
 (`!n. n < dimindex(:Q)
       ==> (residue_of_int_mod (&n):(Q)residue) = Residue n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[residue_of_int_mod_DEF; ISA_INT_MOD_NUM] THEN
  AP_TERM_TAC THEN
  ASM_SIMP_TAC[INT_REM_LT; INT_POS; INT_OF_NUM_LT; ISA_NAT_NUM]);;

(* ------------------------------------------------------------------------- *)
(* lift_zq: Z_q = (8380417)residue, q = 8380417.                             *)
(* ------------------------------------------------------------------------- *)

let LIFT_ZQ_RESIDUE = prove
 (`!x. fips204_zq_residue (lift_zq x) = residue_of_int_mod x`,
  REWRITE_TAC[lift_zq; fips204_zq_residue_DEF]);;

let LIFT_ZQ_REP = prove
 (`!x. &(residue_rep (fips204_zq_residue (lift_zq x))) = x rem &8380417`,
  REWRITE_TAC[LIFT_ZQ_RESIDUE; RESIDUE_REP_OF_INT_MOD; DIMINDEX_Q]);;

let LIFT_ZQ_REP_NUM = prove
 (`!x. residue_rep (fips204_zq_residue (lift_zq x)) =
       num_of_int (x rem &8380417)`,
  REWRITE_TAC[LIFT_ZQ_RESIDUE; RESIDUE_REP_OF_INT_MOD_NUM; DIMINDEX_Q]);;

let LIFT_ZQ_EQ = prove
 (`!x y. lift_zq x = lift_zq y <=> x rem &8380417 = y rem &8380417`,
  REWRITE_TAC[lift_zq; FIPS204_ZQ_INJ; RESIDUE_OF_INT_MOD_EQ; DIMINDEX_Q]);;

let LIFT_ZQ_CONG = prove
 (`!x y. (x == y) (mod &8380417) ==> lift_zq x = lift_zq y`,
  REWRITE_TAC[LIFT_ZQ_EQ; INT_REM_EQ]);;

let LIFT_ZQ_REM = prove
 (`!x. lift_zq (x rem &8380417) = lift_zq x`,
  REWRITE_TAC[LIFT_ZQ_EQ; INT_REM_REM]);;

let COEFFICIENT_TO_INTEGER_LIFT = prove
 (`!x. CoefficientToInteger_hol (lift_zq x) = Value (x rem &8380417)`,
  REWRITE_TAC[CoefficientToInteger_hol_DEF; LIFT_ZQ_REP]);;

(* The lift of a coefficient of an element of R_q is already reduced.        *)

let LIFT_ZQ_RQ_COEFF = prove
 (`!f i. f IN ring_carrier mldsa_rq
         ==> lift_zq (coeff i f) = FIPS204_Zq (Residue (num_of_int(coeff i f)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lift_zq] THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`f:(1->num)->int`; `i:num`] MLDSA_RQ_COEFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `residue_of_int_mod (&(num_of_int(coeff i (f:(1->num)->int))))
              :(8380417)residue` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT];
    MATCH_MP_TAC RESIDUE_OF_INT_MOD_NUM THEN REWRITE_TAC[DIMINDEX_Q] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT]]);;

(* ------------------------------------------------------------------------- *)
(* The coefficient lists of the lifted polynomials and vectors.              *)
(* ------------------------------------------------------------------------- *)

let FIPS204_POLY_COEFFICIENTS_LIFT = prove
 (`!a. fips204_poly_coefficients (lift_poly a:(A)fips204_poly) =
       list_of_seq (\i. lift_zq (a i)) 256`,
  REWRITE_TAC[lift_poly; fips204_poly_SEL_CTR]);;

let LENGTH_LIFT_POLY = prove
 (`!a. LENGTH (fips204_poly_coefficients (lift_poly a:(A)fips204_poly)) = 256`,
  REWRITE_TAC[FIPS204_POLY_COEFFICIENTS_LIFT; LENGTH_LIST_OF_SEQ]);;

let EL_LIFT_POLY = prove
 (`!a i. i < 256
         ==> EL i (fips204_poly_coefficients (lift_poly a:(A)fips204_poly)) =
             lift_zq (a i)`,
  SIMP_TAC[FIPS204_POLY_COEFFICIENTS_LIFT; EL_LIST_OF_SEQ]);;

let LIFT_POLY_EQ = prove
 (`!a b. (lift_poly a:(A)fips204_poly) = lift_poly b <=>
         !i. i < 256 ==> a i rem &8380417 = b i rem &8380417`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[lift_poly; fips204_poly_INJECT; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; LIFT_ZQ_EQ]);;

(* The handwritten spec builds elements of R_q with mldsa_poly, which        *)
(* reduces the coefficients mod q; the lift of its coefficients is the lift  *)
(* of the array itself.                                                      *)

let LIFT_POLY_MLDSA_POLY = prove
 (`!a. (lift_poly (\i. coeff i (mldsa_poly a)):(A)fips204_poly) = lift_poly a`,
  GEN_TAC THEN REWRITE_TAC[LIFT_POLY_EQ] THEN
  SIMP_TAC[COEFF_MLDSA_POLY; INT_REM_REM]);;

let LIFT_POLY_RQ = prove
 (`!a f. f IN ring_carrier mldsa_rq
         ==> ((lift_poly a:(A)fips204_poly) = lift_poly (\i. coeff i f) <=>
              !i. i < 256 ==> a i rem &8380417 = coeff i f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_POLY_EQ] THEN
  MATCH_MP_TAC(TAUT `(p <=> q) ==> (p <=> q)`) THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[INT_REM_LT; MLDSA_RQ_COEFF]);;

let FIPS204_INTPOLY_COEFFICIENTS_LIFT = prove
 (`!a. fips204_intpoly_coefficients (lift_intpoly a) = list_of_seq a 256`,
  REWRITE_TAC[lift_intpoly; fips204_intpoly_coefficients_DEF]);;

let LENGTH_LIFT_INTPOLY = prove
 (`!a. LENGTH (fips204_intpoly_coefficients (lift_intpoly a)) = 256`,
  REWRITE_TAC[FIPS204_INTPOLY_COEFFICIENTS_LIFT; LENGTH_LIST_OF_SEQ]);;

let EL_LIFT_INTPOLY = prove
 (`!a i. i < 256
         ==> EL i (fips204_intpoly_coefficients (lift_intpoly a)) = a i`,
  SIMP_TAC[FIPS204_INTPOLY_COEFFICIENTS_LIFT; EL_LIST_OF_SEQ]);;

let LIFT_INTPOLY_EQ = prove
 (`!a b. lift_intpoly a = lift_intpoly b <=> !i. i < 256 ==> a i = b i`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[lift_intpoly; FIPS204_INTPOLY_INJ; LIST_EQ;
              LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_LIST_OF_SEQ]);;

let FIPS204_BITPOLY_COEFFICIENTS_LIFT = prove
 (`!h. fips204_bitpoly_coefficients (lift_bitpoly h) =
       list_of_seq (\i. residue_of_int_mod (if h i then &1 else &0)) 256`,
  REWRITE_TAC[lift_bitpoly; fips204_bitpoly_coefficients_DEF]);;

let LENGTH_LIFT_BITPOLY = prove
 (`!h. LENGTH (fips204_bitpoly_coefficients (lift_bitpoly h)) = 256`,
  REWRITE_TAC[FIPS204_BITPOLY_COEFFICIENTS_LIFT; LENGTH_LIST_OF_SEQ]);;

let EL_LIFT_BITPOLY = prove
 (`!h i. i < 256
         ==> EL i (fips204_bitpoly_coefficients (lift_bitpoly h)) =
             residue_of_int_mod (if h i then &1 else &0)`,
  SIMP_TAC[FIPS204_BITPOLY_COEFFICIENTS_LIFT; EL_LIST_OF_SEQ]);;

(* The representative of a hint coefficient is 1 or 0 (q = 2 there).         *)

let RESIDUE_REP_LIFT_BITPOLY = prove
 (`!h i. i < 256
         ==> &(residue_rep (EL i (fips204_bitpoly_coefficients
                                   (lift_bitpoly h)))) =
             (if h i then &1 else &0):int`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_LIFT_BITPOLY; RESIDUE_REP_OF_INT_MOD; DIMINDEX_2] THEN
  COND_CASES_TAC THEN CONV_TAC INT_REDUCE_CONV);;

let LIFT_BITPOLY_EQ = prove
 (`!h1 h2. lift_bitpoly h1 = lift_bitpoly h2 <=>
           !i. i < 256 ==> (h1 i <=> h2 i)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!b c. (((if b then &1 else &0):int) rem &2 =
                       (if c then &1 else &0) rem &2) <=> (b <=> c)`
   (fun th ->
      REWRITE_TAC[lift_bitpoly; FIPS204_BITPOLY_INJ; LIST_EQ;
                  LENGTH_LIST_OF_SEQ] THEN
      SIMP_TAC[EL_LIST_OF_SEQ; RESIDUE_OF_INT_MOD_EQ; DIMINDEX_2; th]) THEN
  REPEAT GEN_TAC THEN MAP_EVERY BOOL_CASES_TAC [`b:bool`; `c:bool`] THEN
  CONV_TAC INT_REDUCE_CONV);;

let COMMON_VEC_ENTRIES_LIFT = prove
 (`!v. common_vec_entries (lift_vec v:(N,B)common_vec) =
       list_of_seq v (dimindex(:N))`,
  REWRITE_TAC[lift_vec; common_vec_SEL_CTR]);;

let LENGTH_LIFT_VEC = prove
 (`!v. LENGTH (common_vec_entries (lift_vec v:(N,B)common_vec)) =
       dimindex(:N)`,
  REWRITE_TAC[COMMON_VEC_ENTRIES_LIFT; LENGTH_LIST_OF_SEQ]);;

let EL_LIFT_VEC = prove
 (`!v i. i < dimindex(:N)
         ==> EL i (common_vec_entries (lift_vec v:(N,B)common_vec)) = v i`,
  SIMP_TAC[COMMON_VEC_ENTRIES_LIFT; EL_LIST_OF_SEQ]);;

let LIFT_VEC_EQ = prove
 (`!v w. (lift_vec v:(N,B)common_vec) = lift_vec w <=>
         !i. i < dimindex(:N) ==> v i = w i`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[lift_vec; common_vec_INJECT; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_LIST_OF_SEQ]);;

let FIPS_MATRIX_ENTRIES_LIFT = prove
 (`!m. fips_matrix_entries (lift_mat m:(R,C,E)fips_matrix) =
       list_of_seq (\n. m (n DIV dimindex(:C)) (n MOD dimindex(:C)))
                   (dimindex(:R) * dimindex(:C))`,
  REWRITE_TAC[lift_mat; fips_matrix_SEL_CTR]);;

let LENGTH_LIFT_MAT = prove
 (`!m. LENGTH (fips_matrix_entries (lift_mat m:(R,C,E)fips_matrix)) =
       dimindex(:R) * dimindex(:C)`,
  REWRITE_TAC[FIPS_MATRIX_ENTRIES_LIFT; LENGTH_LIST_OF_SEQ]);;

let EL_LIFT_MAT = prove
 (`!m i j. i < dimindex(:R) /\ j < dimindex(:C)
           ==> EL (i * dimindex(:C) + j)
                  (fips_matrix_entries (lift_mat m:(R,C,E)fips_matrix)) =
               m i j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FIPS_MATRIX_ENTRIES_LIFT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_LIST_OF_SEQ o lhand o snd) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `i * dimindex(:C) + dimindex(:C)` THEN
    ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
    REWRITE_TAC[ARITH_RULE `i * c + c = (i + 1) * c`] THEN
    ASM_SIMP_TAC[LE_MULT_RCANCEL; ARITH_RULE `i < r ==> i + 1 <= r`];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT;
                 ADD_CLAUSES; DIMINDEX_NONZERO]]);;

(* The generated matrices appear wrapped in Common_Mat; the lift of a matrix *)
(* as a (R,C,E)common_mat is Common_Mat (lift_mat m) (common.ml has no lift  *)
(* for common_mat).                                                          *)

let COMMON_MAT_ENTRIES_LIFT = prove
 (`!m. common_mat_entries (Common_Mat (lift_mat m:(R,C,E)fips_matrix)) =
       lift_mat m`,
  REWRITE_TAC[common_mat_entries_DEF]);;

(* A residue built by residue_of_int_mod is reduced; a fips204_zq in general *)
(* is not (Residue wraps any natural number), so there is no inverse lemma   *)
(* &(residue_rep (fips204_zq_residue x)) = ... for an arbitrary x.           *)

let RESIDUE_REP_OF_INT_MOD_LT = prove
 (`!x. residue_rep (residue_of_int_mod x:(Q)residue) < dimindex(:Q)`,
  GEN_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_LT; RESIDUE_REP_OF_INT_MOD] THEN
  MATCH_MP_TAC INT_LT_REM THEN
  REWRITE_TAC[INT_OF_NUM_LT; LT_NZ; DIMINDEX_NONZERO]);;

let RESIDUE_REP_LIFT_ZQ_LT = prove
 (`!x. residue_rep (fips204_zq_residue (lift_zq x)) < 8380417`,
  REWRITE_TAC[LIFT_ZQ_RESIDUE; GSYM DIMINDEX_Q; RESIDUE_REP_OF_INT_MOD_LT]);;

(* ------------------------------------------------------------------------- *)
(* Nominal (single-field record) updates, and the centered remainder.        *)
(* ------------------------------------------------------------------------- *)

let TYPED_HOL_NOMINAL_UPDATE = prove
 (`!(con:A->B) sel inner y.
     typed_hol_read (typed_hol_nominal_update con sel inner y) =
     map_native_result con (typed_hol_read (inner (sel y)))`,
  REWRITE_TAC[typed_hol_nominal_update_DEF; TYPED_HOL_READ_MAP_OPTION]);;

let TYPED_HOL_NOMINAL_LIST_UPDATE = prove
 (`!(con:(A)list->B) sel i a y.
     typed_hol_read
      (typed_hol_nominal_update con sel
        (\f. native_list_update f (&i) a) y) =
     if i < LENGTH (sel y)
     then Value (con (isa_list_update (sel y) i a))
     else Fault Bounds_Error`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TYPED_HOL_NOMINAL_UPDATE; NATIVE_LIST_UPDATE_NUM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[TYPED_HOL_READ; MAP_NATIVE_RESULT]);;

(* mod_pm_int on a positive modulus is the centered remainder mldsa_modpm.   *)

let TYPED_HOL_MOD_PM = prove
 (`!a m. &0 < m ==> typed_hol_mod_pm a m = Value (mod_pm_int a m)`,
  SIMP_TAC[typed_hol_mod_pm_DEF; INT_ARITH `&0:int < m ==> ~(m <= &0)`]);;

let MOD_PM_INT_MLDSA_MODPM = prove
 (`!a m. 0 < m ==> mod_pm_int a (&m) = mldsa_modpm a m`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mod_pm_int_DEF; mldsa_modpm; ISA_INT_MOD_NUM] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_NOT_LE] THEN
  ASM_CASES_TAC `&2 * (a rem &m):int <= &m` THEN
  ASM_SIMP_TAC[INT_ARITH `&2 * r:int <= m ==> ~(m < &2 * r)`] THEN
  ASM_SIMP_TAC[INT_ARITH `~(&2 * r:int <= m) ==> m < &2 * r`]);;

let TYPED_HOL_MOD_PM_MLDSA = prove
 (`!a m. 0 < m ==> typed_hol_mod_pm a (&m) = Value (mldsa_modpm a m)`,
  SIMP_TAC[TYPED_HOL_MOD_PM; MOD_PM_INT_MLDSA_MODPM;
           INT_OF_NUM_LT; INT_LT; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* The rewrite set and the tactic for evaluating generated code.             *)
(* ------------------------------------------------------------------------- *)

let GEN_MONAD_RULES =
 [(* the monad *)
  NATIVE_BIND; MAP_NATIVE_RESULT; NATIVE_FINISH; NATIVE_CONTINUE_BIND;
  NATIVE_SEQ; NATIVE_IF; TYPED_HOL_LET; TYPED_HOL_ALGORITHM;
  case_native_result_DEF; case_statement_outcome_DEF;
  case_iteration_outcome_DEF; case_native_slot_DEF; case_native_bottom_DEF;
  map_statement_outcome_DEF;
  (* reads and options *)
  TYPED_HOL_READ; TYPED_HOL_SLOT_READ; TYPED_HOL_READ_MAP_OPTION;
  isa_case_option; isa_map_option;
  (* lists *)
  NATIVE_LIST_INDEX_NUM; NATIVE_LIST_UPDATE_NUM; TYPED_HOL_LIST_SLICE_NUM;
  TYPED_HOL_NESTED_UPDATE_NUM; TYPED_HOL_NOMINAL_UPDATE;
  typed_hol_sequence_extent_DEF; typed_hol_bottom_index_DEF;
  typed_hol_bottom_sequence_extent_DEF; native_bottom_payload_DEF;
  (* integers, bits and bytes *)
  ISA_NAT_NUM; ISA_INT_DIV_NUM; ISA_INT_MOD_NUM; TYPED_HOL_NONNEGATIVE;
  TYPED_HOL_BIT_VALUE; TYPED_HOL_BYTE_VALUE; TYPED_HOL_INT_TO_BIT;
  TYPED_HOL_INT_TO_BYTE_NUM; TYPED_HOL_INT_ARITHMETIC;
  (* the selectors of the generated types *)
  residue_SEL_CTR; fips204_poly_SEL_CTR; common_vec_SEL_CTR;
  fips_matrix_SEL_CTR; fips204_zq_residue_DEF; common_mat_entries_DEF;
  fips204_intpoly_coefficients_DEF; fips204_bitpoly_coefficients_DEF;
  (* the lifts *)
  LIFT_ZQ_REP; LIFT_ZQ_RESIDUE; FIPS204_POLY_COEFFICIENTS_LIFT;
  FIPS204_INTPOLY_COEFFICIENTS_LIFT; FIPS204_BITPOLY_COEFFICIENTS_LIFT;
  COMMON_VEC_ENTRIES_LIFT; FIPS_MATRIX_ENTRIES_LIFT; COMMON_MAT_ENTRIES_LIFT;
  (* the constructors *)
  NATIVE_RESULT_INJ; NATIVE_RESULT_DISTINCT; STATEMENT_OUTCOME_INJ;
  STATEMENT_OUTCOME_DISTINCT; NATIVE_SLOT_INJ; NATIVE_SLOT_DISTINCT;
  NATIVE_BOTTOM_INJ; NATIVE_BOTTOM_DISTINCT; FIPS204_ZQ_INJ;
  (* list_of_seq *)
  LENGTH_LIST_OF_SEQ; LENGTH_ISA_LIST_UPDATE];;

let GEN_REDUCE_CONV =
  DEPTH_CONV(DIMINDEX_CONV ORELSEC NUM_RED_CONV ORELSEC INT_RED_CONV);;

let GEN_SIMP_TAC ths =
  REPEAT(CHANGED_TAC
   (ASM_SIMP_TAC (GEN_MONAD_RULES @ ths) THEN TRY(CONV_TAC GEN_REDUCE_CONV)));;

(* ------------------------------------------------------------------------- *)
(* bits_of_bytes: the bits of a byte string, bit j of byte i at 8 * i + j    *)
(* (the bit order of FIPS 204 BytesToBits).                                  *)
(* ------------------------------------------------------------------------- *)

let BITS_OF_BYTES_ALL = prove
 (`!s:byte list.
     ALL (\x. LENGTH x = 8)
         (MAP (\b. MAP (\j. bit j b) (isa_upt 0 8)) s)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; MAP; LENGTH_MAP; LENGTH_ISA_UPT] THEN ARITH_TAC);;

let LENGTH_BITS_OF_BYTES = prove
 (`!s:byte list. LENGTH (bits_of_bytes s) = 8 * LENGTH s`,
  GEN_TAC THEN REWRITE_TAC[bits_of_bytes_DEF] THEN
  MP_TAC(SPEC `s:byte list` BITS_OF_BYTES_ALL) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `8` LENGTH_ISA_CONCAT_CONST)) THEN
  REWRITE_TAC[LENGTH_MAP]);;

let EL_BITS_OF_BYTES = prove
 (`!(s:byte list) i j.
     i < LENGTH s /\ j < 8
     ==> EL (8 * i + j) (bits_of_bytes s) = bit j (EL i s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bits_of_bytes_DEF] THEN
  MP_TAC(ISPECL [`8`; `MAP (\(b:byte). MAP (\j. bit j b) (isa_upt 0 8)) s`;
                 `i:num`; `j:num`] EL_ISA_CONCAT_CONST) THEN
  ASM_REWRITE_TAC[BITS_OF_BYTES_ALL; LENGTH_MAP] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_ISA_UPT; ARITH_RULE `8 - 0 = 8`] THEN
  ASM_SIMP_TAC[ISA_UPT; EL_LIST_OF_SEQ; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `8 - 0 = 8`; EL_LIST_OF_SEQ]);;

let BITS_OF_BYTES_APPEND = prove
 (`!s t:byte list.
     bits_of_bytes (APPEND s t) =
     APPEND (bits_of_bytes s) (bits_of_bytes t)`,
  REWRITE_TAC[bits_of_bytes_DEF; MAP_APPEND; ISA_CONCAT_APPEND]);;

let BITS_OF_BYTES_NIL = prove
 (`bits_of_bytes [] = []`,
  REWRITE_TAC[bits_of_bytes_DEF; MAP; isa_concat]);;

(* ------------------------------------------------------------------------- *)
(* The hash H(str,8 * ell) and the XOF states.                               *)
(* ------------------------------------------------------------------------- *)

let SHAKE256_SEMANTIC = prove
 (`!str n. SHAKE256_semantic (str,&(8 * n)) =
           Value (MAP (shake256_bits str) (isa_upt 0 n))`,
  REWRITE_TAC[SHAKE256_semantic_DEF; UNCURRY_DEF; SHAKE256_DEF;
              INT_ARITH `~(&n:int < &0)`; ISA_NAT_NUM] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let H_HOL_NUM = prove
 (`!str n. H_hol str (&n) = Value (MAP (shake256_bits str) (isa_upt 0 n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[H_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ISA_NAT_NUM; REPLICATE; TYPED_HOL_LIST_SLICE_NUM; LENGTH;
              LE_REFL; TYPED_HOL_READ; NATIVE_BIND] THEN
  REWRITE_TAC[INT_OF_NUM_MUL; SHAKE256_SEMANTIC]);;

(* Under xof_ok, H on the bits of a byte string is mldsa_h.                  *)

let EQ_H_HOL = prove
 (`xof_ok ==> !m n. H_hol (bits_of_bytes m) (&n) = Value (mldsa_h m n)`,
  REWRITE_TAC[xof_ok] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[H_HOL_NUM; mldsa_h; MAP_ISA_UPT; SUB_0; ADD_CLAUSES;
                  ETA_AX]);;

let H_INIT = prove
 (`H_Init_hol = Value ([],(Absorbing,0))`,
  REWRITE_TAC[H_Init_hol_DEF; SHAKE_Init_semantic_DEF]);;

let G_INIT = prove
 (`G_Init_hol = Value ([],(Absorbing,0))`,
  REWRITE_TAC[G_Init_hol_DEF; SHAKE_Init_semantic_DEF]);;

let H_ABSORB = prove
 (`(!s off t. H_Absorb_hol (s,(Absorbing,off)) t =
              Value (APPEND s t,(Absorbing,off))) /\
   (!s off t. H_Absorb_hol (s,(Squeezing,off)) t = Fault Bounds_Error)`,
  REWRITE_TAC[H_Absorb_hol_DEF; SHAKE_Absorb_semantic_DEF; UNCURRY_DEF;
              XOF_PHASE_DISTINCT; source_fault_DEF]);;

let G_ABSORB = prove
 (`(!s off t. G_Absorb_hol (s,(Absorbing,off)) t =
              Value (APPEND s t,(Absorbing,off))) /\
   (!s off t. G_Absorb_hol (s,(Squeezing,off)) t = Fault Bounds_Error)`,
  REWRITE_TAC[G_Absorb_hol_DEF; SHAKE_Absorb_semantic_DEF; UNCURRY_DEF;
              XOF_PHASE_DISTINCT; source_fault_DEF]);;

(* Squeezing n bytes: bytes [off,off + n) of the stream of the absorbed      *)
(* string, and the offset advances by n. The phase becomes Squeezing, so     *)
(* absorbing afterwards faults; squeezing again continues at the offset.     *)

let H_SQUEEZE = prove
 (`!s ph off n.
     H_Squeeze_hol (s,(ph,off)) (&n) =
     Value ((s,(Squeezing,off + n)),
            MAP (shake256_bits (bits_of_bytes s)) (isa_upt off (off + n)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[H_Squeeze_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ISA_NAT_NUM; REPLICATE; TYPED_HOL_LIST_SLICE_NUM; LENGTH;
              LE_REFL; TYPED_HOL_READ; NATIVE_BIND] THEN
  REWRITE_TAC[INT_OF_NUM_MUL; SHAKE256_Squeeze_semantic_DEF;
              UNCURRY_DEF; INT_ARITH `~(&n:int < &0)`; ISA_NAT_NUM] THEN
  SIMP_TAC[MOD_MULT; DIV_MULT; ARITH_EQ]);;

let G_SQUEEZE = prove
 (`!s ph off n.
     G_Squeeze_hol (s,(ph,off)) (&n) =
     Value ((s,(Squeezing,off + n)),
            MAP (shake128_bits (bits_of_bytes s)) (isa_upt off (off + n)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[G_Squeeze_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ISA_NAT_NUM; REPLICATE; TYPED_HOL_LIST_SLICE_NUM; LENGTH;
              LE_REFL; TYPED_HOL_READ; NATIVE_BIND] THEN
  REWRITE_TAC[INT_OF_NUM_MUL; SHAKE128_Squeeze_semantic_DEF;
              UNCURRY_DEF; INT_ARITH `~(&n:int < &0)`; ISA_NAT_NUM] THEN
  SIMP_TAC[MOD_MULT; DIV_MULT; ARITH_EQ]);;

(* The same under xof_ok: consecutive slices of shake256 / shake128.         *)

let EQ_H_SQUEEZE = prove
 (`xof_ok
   ==> !s ph off n.
         H_Squeeze_hol (s,(ph,off)) (&n) =
         Value ((s,(Squeezing,off + n)),
                list_of_seq (\k. shake256 s (off + k)) n)`,
  REWRITE_TAC[xof_ok] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[H_SQUEEZE; MAP_ISA_UPT; ADD_SUB2;
                  ARITH_RULE `(off + n) - off = n`]);;

let EQ_G_SQUEEZE = prove
 (`xof_ok
   ==> !s ph off n.
         G_Squeeze_hol (s,(ph,off)) (&n) =
         Value ((s,(Squeezing,off + n)),
                list_of_seq (\k. shake128 s (off + k)) n)`,
  REWRITE_TAC[xof_ok] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[G_SQUEEZE; MAP_ISA_UPT;
                  ARITH_RULE `(off + n) - off = n`]);;

(* Init, absorb s1, ..., sm, then squeeze n bytes: the first n bytes of the  *)
(* stream of the concatenation; mldsa_h for SHAKE256.                        *)

let EQ_H_INIT_ABSORB_SQUEEZE = prove
 (`xof_ok
   ==> !t n. native_bind H_Init_hol
              (\ctx. native_bind (H_Absorb_hol ctx t) (\c. H_Squeeze_hol c (&n)))
             = Value ((t,(Squeezing,n)),mldsa_h t n)`,
  DISCH_THEN(MP_TAC o MATCH_MP EQ_H_SQUEEZE) THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[H_INIT; NATIVE_BIND; H_ABSORB; APPEND; ADD_CLAUSES;
                  mldsa_h; ETA_AX]);;

let EQ_G_INIT_ABSORB_SQUEEZE = prove
 (`xof_ok
   ==> !t n. native_bind G_Init_hol
              (\ctx. native_bind (G_Absorb_hol ctx t) (\c. G_Squeeze_hol c (&n)))
             = Value ((t,(Squeezing,n)),list_of_seq (shake128 t) n)`,
  DISCH_THEN(MP_TAC o MATCH_MP EQ_G_SQUEEZE) THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[G_INIT; NATIVE_BIND; G_ABSORB; APPEND; ADD_CLAUSES;
                  ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* The zero padding of the generated spec: BitZeros n and ByteZeros n are    *)
(* n zero bits and bytes, and Native_Bottom for a negative n.                *)
(* ------------------------------------------------------------------------- *)

let REPLICATE_APPEND_1 = prove
 (`!n (x:A). APPEND (REPLICATE n x) [x] = REPLICATE (SUC n) x`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; APPEND]);;

let BYTE_ZEROS = prove
 (`!n. ByteZeros_hol (&n) = Value (Native_Value (REPLICATE n (word 0)))`,
  GEN_TAC THEN REWRITE_TAC[ByteZeros_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ISA_NAT_NUM; REPLICATE; TYPED_HOL_LIST_SLICE_NUM; LENGTH;
              LE_REFL; TYPED_HOL_READ; NATIVE_BIND;
              INT_ARITH `~(&n:int < &0)`] THEN
  REWRITE_TAC[num_CONV `1`; REPLICATE; list_of_seq; SUB_REFL;
              TYPED_HOL_INT_TO_BYTE_NUM; NATIVE_BIND; NATIVE_LIST_UPDATE_NUM;
              LENGTH; isa_list_update; TYPED_HOL_READ] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[NATIVE_BIND; TYPED_HOL_READ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NATIVE_SCHEDULE_CONV) THEN
  REWRITE_TAC[INT_ARITH `&n - &1 + &1:int = &n`; ISA_NAT_NUM] THEN
  MP_TAC(ISPECL
   [`\(i:int) (z:byte list). Value (APPEND z [word 0:byte])`;
    `\k. &k:int`; `n:num`; `\k. REPLICATE k (word 0:byte)`]
   NATIVE_FOLDL_LIST_OF_SEQ) THEN
  REWRITE_TAC[REPLICATE_APPEND_1; REPLICATE] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NATIVE_BIND]);;

let BIT_ZEROS = prove
 (`!n. BitZeros_hol (&n) = Value (Native_Value (REPLICATE n F))`,
  GEN_TAC THEN REWRITE_TAC[BitZeros_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ISA_NAT_NUM; REPLICATE; TYPED_HOL_LIST_SLICE_NUM; LENGTH;
              LE_REFL; TYPED_HOL_READ; NATIVE_BIND;
              INT_ARITH `~(&n:int < &0)`] THEN
  REWRITE_TAC[num_CONV `1`; REPLICATE; list_of_seq; SUB_REFL;
              TYPED_HOL_INT_TO_BIT; NATIVE_BIND; NATIVE_LIST_UPDATE_NUM;
              LENGTH; isa_list_update; TYPED_HOL_READ] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[NATIVE_BIND; TYPED_HOL_READ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NATIVE_SCHEDULE_CONV) THEN
  REWRITE_TAC[INT_ARITH `&n - &1 + &1:int = &n`; ISA_NAT_NUM] THEN
  MP_TAC(ISPECL
   [`\(i:int) (z:bool list). Value (APPEND z [F])`;
    `\k. &k:int`; `n:num`; `\k. REPLICATE k F`]
   NATIVE_FOLDL_LIST_OF_SEQ) THEN
  REWRITE_TAC[REPLICATE_APPEND_1; REPLICATE] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NATIVE_BIND]);;

let BYTE_ZEROS_NEG = prove
 (`!n. n < &0 ==> ByteZeros_hol n = Value Native_Bottom`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ByteZeros_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[ISA_NAT_NUM; REPLICATE; TYPED_HOL_LIST_SLICE_NUM; LENGTH;
                  LE_REFL; TYPED_HOL_READ; NATIVE_BIND]);;

let BIT_ZEROS_NEG = prove
 (`!n. n < &0 ==> BitZeros_hol n = Value Native_Bottom`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BitZeros_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[ISA_NAT_NUM; REPLICATE; TYPED_HOL_LIST_SLICE_NUM; LENGTH;
                  LE_REFL; TYPED_HOL_READ; NATIVE_BIND]);;

(* ------------------------------------------------------------------------- *)
(* The byte-string interfaces of H: HBytes_34, HBytes_66 and HBytesString    *)
(* turn the string into bits, slice off the fixed length and call H. Each    *)
(* takes the BytesToBits lemma of the encoding component as a hypothesis.    *)
(* ------------------------------------------------------------------------- *)

let TYPED_HOL_LIST_SLICE_ALL = prove
 (`!(xs:A list) n. LENGTH xs = n ==> typed_hol_list_slice xs (&0) (&n) = SOME xs`,
  SIMP_TAC[TYPED_HOL_LIST_SLICE_NUM; LE_0; LE_REFL; ADD_CLAUSES; SUB_0] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[LIST_OF_SEQ_EQ_SELF]);;

let LIST_OF_SEQ_EL = prove
 (`!(xs:A list) n. LENGTH xs = n ==> list_of_seq (\i. EL i xs) n = xs`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[LIST_OF_SEQ_EQ_SELF]);;

let EQ_HBYTESSTRING = prove
 (`xof_ok /\ BytesToBitsString_hol str = Value (bits_of_bytes str)
   ==> !n. HBytesString_hol str (&n) = Value (mldsa_h str n)`,
  STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP EQ_H_HOL) THEN
  GEN_TAC THEN REWRITE_TAC[HBytesString_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[ISA_NAT_NUM; REPLICATE; TYPED_HOL_LIST_SLICE_NUM; LENGTH;
                  LE_REFL; TYPED_HOL_READ; NATIVE_BIND]);;

let EQ_HBYTES_34 = prove
 (`xof_ok /\ LENGTH str = 34 /\
   BytesToBits_34_hol str = Value (bits_of_bytes str)
   ==> !n. HBytes_34_hol str (&n) = Value (mldsa_h str n)`,
  STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP EQ_H_HOL) THEN
  SUBGOAL_THEN `LENGTH (bits_of_bytes str) = 272` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_BITS_OF_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[HBytes_34_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[ISA_NAT_NUM; REPLICATE; TYPED_HOL_LIST_SLICE_NUM; LENGTH;
                  LE_REFL; LE_0; TYPED_HOL_READ; NATIVE_BIND; ADD_CLAUSES;
                  SUB_0] THEN
  ASM_SIMP_TAC[LIST_OF_SEQ_EL; TYPED_HOL_READ; NATIVE_BIND]);;

let EQ_HBYTES_66 = prove
 (`xof_ok /\ LENGTH str = 66 /\
   BytesToBits_66_hol str = Value (bits_of_bytes str)
   ==> !n. HBytes_66_hol str (&n) = Value (mldsa_h str n)`,
  STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP EQ_H_HOL) THEN
  SUBGOAL_THEN `LENGTH (bits_of_bytes str) = 528` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_BITS_OF_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[HBytes_66_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[ISA_NAT_NUM; REPLICATE; TYPED_HOL_LIST_SLICE_NUM; LENGTH;
                  LE_REFL; LE_0; TYPED_HOL_READ; NATIVE_BIND; ADD_CLAUSES;
                  SUB_0] THEN
  ASM_SIMP_TAC[LIST_OF_SEQ_EL; TYPED_HOL_READ; NATIVE_BIND]);;

(* ------------------------------------------------------------------------- *)
(* Two more integer helpers: the generated bitlen (bitlen a = 0 for a = 0    *)
(* and SUC(bitlen(a DIV 2)) otherwise) and modular exponentiation. The       *)
(* relation of bitlen to mldsa_bitlen of common/fips204/fips204.ml is not    *)
(* proved here; the encoding component needs it and owns it.                 *)
(* ------------------------------------------------------------------------- *)

let BITLEN_SEMANTIC = prove
 (`(!n. bitlen_semantic (&n) = Value (&(bitlen n))) /\
   (!a. a < &0 ==> bitlen_semantic a = Fault Bounds_Error)`,
  REWRITE_TAC[bitlen_semantic_DEF; source_fault_DEF; ISA_NAT_NUM;
              INT_ARITH `~(&n:int < &0)`] THEN
  SIMP_TAC[]);;

let TYPED_HOL_POW_MOD = prove
 (`!a n m. &0 < m
           ==> typed_hol_pow_mod a (&n) m = Value ((a pow n) rem m)`,
  SIMP_TAC[typed_hol_pow_mod_DEF; ISA_NAT_NUM; ISA_INT_MOD_POS;
           INT_LT_IMP_LE; INT_ARITH `~(&n:int < &0)`;
           INT_ARITH `&0:int < m ==> ~(m <= &0)`]);;

(* ------------------------------------------------------------------------- *)
(* Facts hoisted from the component files. Each of these was proved          *)
(* separately, with the same statement, in two or more component files; the  *)
(* components use these copies.                                              *)
(* ------------------------------------------------------------------------- *)

(* Single clauses of the monad and reads, as rewrites on their own.          *)

let NATIVE_BIND_VALUE = CONJUNCT1 NATIVE_BIND;;

let TYPED_HOL_READ_SOME = CONJUNCT1 TYPED_HOL_READ;;

let TYPED_HOL_SLOT_READ_ASSIGNED = CONJUNCT1 TYPED_HOL_SLOT_READ;;

let TYPED_HOL_NONNEGATIVE_NUM = CONJUNCT1 TYPED_HOL_NONNEGATIVE;;

let H_ABSORB_ABSORBING = CONJUNCT1 H_ABSORB;;

let TYPED_HOL_INT_POW_NUM = el 2 (CONJUNCTS TYPED_HOL_INT_ARITHMETIC_POS);;

let TYPED_HOL_INT_POW_ONE = prove
 (`!n. typed_hol_int_arithmetic APow (&1) (&n) = Value (&1)`,
  REWRITE_TAC[TYPED_HOL_INT_POW_NUM; INT_POW_ONE]);;

let TYPED_HOL_INT_TO_BIT_NUM = prove
 (`!n. typed_hol_int_to_bit (&n) =
       if n < 2 then Value (n = 1) else Fault Bounds_Error`,
  REWRITE_TAC[typed_hol_int_to_bit_DEF; INT_POS; INT_OF_NUM_LT;
              INT_OF_NUM_EQ]);;

let ISA_INT_DIV_NUM_NUM = prove
 (`!m n. isa_int_div (&m) (&n) = &(m DIV n)`,
  REWRITE_TAC[ISA_INT_DIV_NUM; INT_OF_NUM_DIV]);;

(* The same facts as LENGTH_ISA_DROP, EL_ISA_DROP, LENGTH_ISA_TAKE and       *)
(* EL_ISA_TAKE with the list before the count in the quantifier prefix.      *)

let LENGTH_ISA_DROP_LIST_FIRST =
  ONCE_REWRITE_RULE[SWAP_FORALL_THM] LENGTH_ISA_DROP;;

let EL_ISA_DROP_LIST_FIRST =
  ONCE_REWRITE_RULE[SWAP_FORALL_THM] EL_ISA_DROP;;

let LENGTH_ISA_TAKE_LIST_FIRST =
  ONCE_REWRITE_RULE[SWAP_FORALL_THM] LENGTH_ISA_TAKE;;

let EL_ISA_TAKE_LIST_FIRST =
  ONCE_REWRITE_RULE[SWAP_FORALL_THM] EL_ISA_TAKE;;

let ISA_DROP_0 = prove
 (`!l:A list. isa_drop 0 l = l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[isa_drop]);;

let ISA_UPT_ADD = prove
 (`!a n. isa_upt a (a + n) = list_of_seq (\i. a + i) n`,
  REWRITE_TAC[ISA_UPT; ADD_SUB2]);;

let REPLICATE_LIST_OF_SEQ = prove
 (`!n (x:A). REPLICATE n x = list_of_seq (\i. x) n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; LIST_OF_SEQ] THEN
  REWRITE_TAC[o_DEF]);;

let REPLICATE_ONE = prove
 (`!x:A. REPLICATE 1 x = [x]`,
  REWRITE_TAC[ONE; REPLICATE]);;

let EL_REPLICATE_LT = prove
 (`!n (x:A) i. i < n ==> EL i (REPLICATE n x) = x`,
  INDUCT_TAC THEN REWRITE_TAC[REPLICATE; CONJUNCT1 LT] THEN
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; LT_SUC] THEN
  ASM_MESON_TAC[]);;

let TYPED_HOL_EMPTY_SLICE = prove
 (`typed_hol_list_slice (REPLICATE (isa_nat (&0)) (x:A)) (&0) (&0) = SOME [] /\
   typed_hol_list_slice (REPLICATE 0 (x:A)) (&0) (&0) = SOME [] /\
   typed_hol_list_slice ([]:A list) (&0) (&0) = SOME []`,
  REWRITE_TAC[ISA_NAT_NUM; REPLICATE; typed_hol_list_slice_DEF;
              LENGTH; INT_LE_REFL; INT_SUB_REFL; isa_take; isa_drop]);;

let NATIVE_LIST_INDEX_LT = prove
 (`!(l:A list) n. n < LENGTH l ==> native_list_index l (&n) = SOME (EL n l)`,
  SIMP_TAC[NATIVE_LIST_INDEX_NUM]);;

let NATIVE_LIST_UPDATE_LT = prove
 (`!(l:A list) n a.
        n < LENGTH l
        ==> native_list_update l (&n) a = SOME (isa_list_update l n a)`,
  SIMP_TAC[NATIVE_LIST_UPDATE_NUM]);;

let NATIVE_LIST_INDEX_LIST_OF_SEQ = prove
 (`!(f:num->A) n i. i < n ==> native_list_index (list_of_seq f n) (&i) =
                              SOME (f i)`,
  SIMP_TAC[NATIVE_LIST_INDEX_NUM; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let NATIVE_SCHEDULE_COUNT = prove
 (`!n. native_schedule (SUC n) (\i. i < &n) (\i. i + &1) (&0:int) =
       list_of_seq (\k. &k) n`,
  GEN_TAC THEN MP_TAC(SPECL [`SUC n`; `n:num`] NATIVE_SCHEDULE_NUM) THEN
  REWRITE_TAC[LE; LE_REFL]);;

let DIV_MOD_256_SMALL = prove
 (`!i j. j < 256 ==> (256 * i + j) DIV 256 = i /\ (256 * i + j) MOD 256 = j`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT; ARITH_EQ;
               ADD_CLAUSES]);;

(* Lifts of functions are equal if the functions agree on the index range.   *)

let LIFT_VEC_CONG = prove
 (`!(v:num->B) w.
        (!i. i < dimindex(:N) ==> v i = w i)
        ==> (lift_vec v:(N,B)common_vec) = lift_vec w`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LIFT_VEC_EQ] THEN
  ASM_SIMP_TAC[]);;

let LIFT_POLY_CONG = prove
 (`!a b. (!i. i < 256 ==> a i = b i)
         ==> (lift_poly a:(A)fips204_poly) = lift_poly b`,
  SIMP_TAC[LIFT_POLY_EQ]);;

let LIFT_INTPOLY_CONG = prove
 (`!a b. (!j. j < 256 ==> a j = b j) ==> lift_intpoly a = lift_intpoly b`,
  SIMP_TAC[LIFT_INTPOLY_EQ]);;

let LIFT_BITPOLY_VEC_CONG = prove
 (`!P Q. (!i j. i < dimindex(:N) /\ j < 256 ==> (P i j <=> Q i j))
         ==> (lift_vec (\i. lift_bitpoly (P i)):
                (N,fips204_bitpoly)common_vec) =
             lift_vec (\i. lift_bitpoly (Q i))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIFT_VEC_CONG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[LIFT_BITPOLY_EQ]);;

let COMMON_VEC_INTPOLY_ID = prove
 (`!v:(N,fips204_intpoly)common_vec.
     Common_Vec (MAP FIPS204_IntPoly
                  (MAP fips204_intpoly_coefficients
                       (common_vec_entries v))) = v`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!l. MAP FIPS204_IntPoly (MAP fips204_intpoly_coefficients l) = l`
   (fun th -> REWRITE_TAC[th; common_vec_CTR_SEL]) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; CONS_11] THEN
  MP_TAC(ISPEC `h:fips204_intpoly` (cases "fips204_intpoly")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[fips204_intpoly_coefficients_DEF]);;

(* Byte lists as numbers, and the encoding of coefficients.                  *)

let NUM_OF_BYTELIST_APPEND = prove
 (`!l m. num_of_bytelist (APPEND l m) =
         num_of_bytelist l + 256 EXP LENGTH l * num_of_bytelist m`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; num_of_bytelist; LENGTH; EXP; ADD_CLAUSES;
                  MULT_CLAUSES] THEN
  ARITH_TAC);;

let MLDSA_ENCODE_0 = prove
 (`!c f. mldsa_encode c 0 f = []`,
  REWRITE_TAC[mldsa_encode; MULT_CLAUSES; DIV_0; CONJUNCT1 bytelist_of_num]);;

let NSUM_LT_SUC = prove
 (`!g n. nsum {i | i < SUC n} g = nsum {i | i < n} g + g n`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{i | i < SUC n} = n INSERT {i | i < n}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ARITH_TAC;
    SIMP_TAC[NSUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
    ARITH_TAC]);;

let NSUM_LT_SPLIT = prove
 (`!g m n. nsum {i | i < m + n} g =
           nsum {i | i < m} g + nsum {j | j < n} (\j. g (m + j))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; NSUM_LT_SUC] THEN
  REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; NSUM_CLAUSES; ADD_CLAUSES] THEN
  ARITH_TAC);;

let BYTELIST_EQ_NUM = prove
 (`!l1 l2:byte list.
        l1 = l2 <=>
        LENGTH l1 = LENGTH l2 /\ num_of_bytelist l1 = num_of_bytelist l2`,
  MESON_TAC[BYTELIST_OF_NUM_OF_BYTELIST]);;

let MLDSA_ENCODE_APPEND = prove
 (`!c m n f.
        8 divides (c * m) /\ 8 divides (c * n)
        ==> mldsa_encode c (m + n) f =
            APPEND (mldsa_encode c m f) (mldsa_encode c n (\j. f (m + j)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `8 divides (c * (m + n))` ASSUME_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB] THEN ASM_MESON_TAC[DIVIDES_ADD];
    ALL_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_SIMP_TAC[BYTELIST_EQ_NUM; LENGTH_APPEND; MLDSA_ENCODE_LENGTH;
               NUM_OF_BYTELIST_APPEND; NUM_OF_BYTELIST_MLDSA_ENCODE] THEN
  UNDISCH_TAC `8 divides (c * m)` THEN UNDISCH_TAC `8 divides (c * n)` THEN
  REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `b:num` THEN DISCH_TAC THEN X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; ARITH_RULE `(8 * a) DIV 8 = a`;
                  ARITH_RULE `(8 * a + 8 * b) DIV 8 = a + b`] THEN
  REWRITE_TAC[NSUM_LT_SPLIT] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM NSUM_LMUL] THEN MATCH_MP_TAC NSUM_EQ THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP] THEN ARITH_TAC);;

(* The XOF squeeze under xof_ok with the quantifiers of the generated code.  *)

let H_SQUEEZE_XOF_OK = prove
 (`!input ph off n.
        xof_ok
        ==> H_Squeeze_hol (input,(ph,off)) (&n) =
            Value((input,(Squeezing,off + n)),
                  list_of_seq (\k. shake256 input (off + k)) n)`,
  MESON_TAC[EQ_H_SQUEEZE]);;

(* IntegerToBytes of a number below 2^(8 * alpha), alpha = 1 and 2.          *)

let INTEGER_TO_BYTES_1_NUM = prove
 (`!n. n < 256 ==> IntegerToBytes_1_hol (&n) (&1) = Value [word n]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IntegerToBytes_1_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[ISA_NAT_NUM; NATIVE_SCHEDULE_COUNT] THEN
  REWRITE_TAC[num_CONV `1`; LIST_OF_SEQ; o_DEF; native_foldl_DEF; REPLICATE;
              UNCURRY_DEF; ISA_INT_MOD_NUM; INT_OF_NUM_REM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN
  GEN_SIMP_TAC[TYPED_HOL_INT_TO_BYTE_NUM; TYPED_HOL_INT_ARITHMETIC_POS;
               ISA_INT_DIV_NUM] THEN
  REWRITE_TAC[LENGTH; ARITH; isa_list_update; native_foldl_DEF; NATIVE_BIND;
              TYPED_HOL_READ; UNCURRY_DEF]);;

let INTEGER_TO_BYTES_2_NUM = prove
 (`!n. IntegerToBytes_2_hol (&n) (&2) = Value (bytelist_of_num 2 n)`,
  GEN_TAC THEN REWRITE_TAC[IntegerToBytes_2_hol_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[ISA_NAT_NUM; NATIVE_SCHEDULE_COUNT] THEN
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; LIST_OF_SEQ; o_DEF;
              native_foldl_DEF; REPLICATE; UNCURRY_DEF; ISA_INT_MOD_NUM;
              INT_OF_NUM_REM] THEN
  REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; ARITH_RULE `SUC 1 = 2`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  GEN_SIMP_TAC[TYPED_HOL_INT_TO_BYTE_NUM; TYPED_HOL_INT_ARITHMETIC_POS;
               ISA_INT_DIV_NUM; MOD_LT_EQ; ARITH_EQ; INT_OF_NUM_DIV;
               INT_OF_NUM_REM] THEN
  REWRITE_TAC[LENGTH; ARITH; isa_list_update; native_foldl_DEF; NATIVE_BIND;
              TYPED_HOL_READ; UNCURRY_DEF; LENGTH_REPLICATE; REPLICATE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[INT_OF_NUM_REM; INT_OF_NUM_DIV] THEN
  GEN_SIMP_TAC[TYPED_HOL_INT_TO_BYTE_NUM; MOD_LT_EQ; ARITH_EQ; DIV_DIV] THEN
  REWRITE_TAC[LENGTH; ARITH; isa_list_update; native_foldl_DEF; NATIVE_BIND;
              TYPED_HOL_READ; UNCURRY_DEF; bytelist_of_num;
              ARITH_RULE `SUC(SUC 0) = 2`] THEN
  REWRITE_TAC[TWO; ONE; bytelist_of_num]);;
