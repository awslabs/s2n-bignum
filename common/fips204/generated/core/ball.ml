(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SampleInBall (FIPS 204 Algorithm 29) and ExpandMask (Algorithm 34): the   *)
(* generated SampleInBall_P_hol and ExpandMask_P_hol of                      *)
(* common/fips204/generated/fips204_generated.ml, for P =                    *)
(* MLDSA44/65/87_Configuration, against mldsa_ball_coeffs and                *)
(* mldsa_expand_mask of common/fips204/fips204.ml, under xof_ok.             *)
(*                                                                           *)
(* Both generated functions return integer polynomials (fips204_intpoly)     *)
(* with the signed coefficients of FIPS 204: SampleInBall coefficients in    *)
(* {-1, 0, 1} and ExpandMask coefficients gamma1 - field in                  *)
(* (-gamma1, gamma1]. The handwritten mldsa_sample_in_ball and               *)
(* mldsa_expand_mask reduce these mod q (mldsa_poly), so the lemmas lift the *)
(* unreduced coefficient arrays with lift_intpoly:                           *)
(*                                                                           *)
(*   EQ_SAMPLEINBALL_P: for LENGTH rho < 135,                                *)
(*     SampleInBall_P_hol rho =                                              *)
(*     Value (lift_intpoly (mldsa_ball_coeffs tau (shake256 rho) tau))       *)
(*   and mldsa_sample_in_ball tau rho is (by definition)                     *)
(*     mldsa_poly (mldsa_ball_coeffs tau (shake256 rho) tau);                *)
(*                                                                           *)
(*   EQ_EXPANDMASK_P: for LENGTH rho = 64,                                   *)
(*     ExpandMask_P_hol rho (&kappa) =                                       *)
(*     Value (lift_vec (\r. lift_intpoly (\i. &gamma1 - mldsa_field c        *)
(*       (mldsa_h (APPEND rho (bytelist_of_num 2 (kappa + r))) (32 * c)) i)))*)
(*   with c = 1 + bitlen(gamma1 - 1), and BALL_EXPAND_MASK says that         *)
(*   mldsa_expand_mask gamma1 rho kappa r is mldsa_poly of the same array.   *)
(*                                                                           *)
(* The generic monad, loop, list and XOF lemmas BALL_... and the bit         *)
(* conversions BytesToBits, BitsToInteger, IntegerToBytes and BitUnpack are  *)
(* the single copies that encode.ml and toplevel.ml use: encode.ml loads     *)
(* this file for ball_bytes_to_bits_gen, ball_bitunpack_gen, BALL_SIMP_TAC,  *)
(* BALL_FOLDL_TAC and BALL_HBYTESSTRING.                                     *)
(*                                                                           *)
(* Load after base.ml and common.ml.                                   *)
(* ========================================================================= *)

needs "common/fips204/generated/core/common.ml";;
needs "common/fips204/generated/core/core.ml";;

(* ------------------------------------------------------------------------- *)
(* The generated monad: binds, reads and list accesses at numeral indices.   *)
(* ------------------------------------------------------------------------- *)


(* The dummy initialisations of the generated code: empty slices.            *)


(* ------------------------------------------------------------------------- *)
(* Counted loops: native_foldl over native_schedule (SUC n) (\i. i < &b)     *)
(* (\i. i + &1) (&a) with a + n = b runs the body at a, ..., b - 1.          *)
(* ------------------------------------------------------------------------- *)

let BALL_FOLDL_SCHEDULE_ABS = prove
 (`!b (body:int->S->(S)native_result) n a (P:num->S->bool) s.
        a + n = b /\ P a s /\
        (!k s. a <= k /\ k < b /\ P k s
               ==> ?s'. body (&k) s = Value s' /\ P (SUC k) s')
        ==> ?s'. native_foldl body
                   (native_schedule (SUC n) (\i. i < &b) (\i. i + &1) (&a))
                   s = Value s' /\ P b s'`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ONCE_REWRITE_TAC[native_schedule_DEF] THEN
    ONCE_REWRITE_TAC[native_schedule_DEF] THEN
    ASM_REWRITE_TAC[INT_LT_REFL; native_foldl_DEF] THEN
    EXISTS_TAC `s:S` THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ONCE_REWRITE_TAC[native_schedule_DEF] THEN
    SUBGOAL_THEN `&a:int < &b` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[native_foldl_DEF] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`a:num`; `s:S`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:S` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[NATIVE_BIND; INT_OF_NUM_ADD; GSYM ADD1] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let BALL_FOLDL_SCHEDULE = prove
 (`!(body:int->S->(S)native_result) a n b (P:num->S->bool) s.
        a + n = b ==> P 0 s ==>
        (!k s. k < n /\ P k s
               ==> ?s'. body (&(a + k)) s = Value s' /\ P (SUC k) s')
        ==> ?s'. native_foldl body
                   (native_schedule (SUC n) (\i. i < &b) (\i. i + &1) (&a))
                   s = Value s' /\ P n s'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:num`; `body:int->S->(S)native_result`; `n:num`;
                 `a:num`; `\k (s:S). (P:num->S->bool) (k - a) s`; `s:S`]
        BALL_FOLDL_SCHEDULE_ABS) THEN
  ASM_REWRITE_TAC[SUB_REFL] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k - a:num`; `s':S`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `a <= k ==> a + k - a = k`;
                 ARITH_RULE `a <= k ==> SUC k - a = SUC(k - a)`];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ARITH_RULE `(a + n) - a = n`]]);;

(* ------------------------------------------------------------------------- *)
(* While loops: native_loop test body = native_iter (native_loop_step ...)   *)
(* gives the result of hol_light_iterate for any number of steps that is     *)
(* not Nontermination, so a loop that stops after d iterations by an         *)
(* invariant returns the state after them.                                   *)
(* ------------------------------------------------------------------------- *)

let BALL_ITERATE_MONO = prove
 (`!(step:S->((S,A)iteration_outcome)native_result) n m s.
        ~(hol_light_iterate n step s = Nontermination)
        ==> hol_light_iterate (n + m) step s = hol_light_iterate n step s`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[hol_light_iterate_DEF; ADD_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `s:S`] THEN
  STRUCT_CASES_TAC
   (ISPEC `(step:S->((S,A)iteration_outcome)native_result) s`
          (cases "native_result")) THEN
  REWRITE_TAC[case_native_result_DEF] THEN
  TRY(STRUCT_CASES_TAC (ISPEC `a:(S,A)iteration_outcome`
                               (cases "iteration_outcome"))) THEN
  REWRITE_TAC[case_iteration_outcome_DEF] THEN ASM_SIMP_TAC[]);;

let BALL_NATIVE_ITER = prove
 (`!(step:S->((S,A)iteration_outcome)native_result) n s.
        ~(hol_light_iterate n step s = Nontermination)
        ==> native_iter step s = hol_light_iterate n step s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[native_iter_DEF] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN
  ABBREV_TAC
   `m = @n. ~(hol_light_iterate n
                (step:S->((S,A)iteration_outcome)native_result) s =
              Nontermination)` THEN
  DISCH_TAC THEN
  DISJ_CASES_TAC(SPECL [`m:num`; `n:num`] LE_CASES) THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  ASM_SIMP_TAC[BALL_ITERATE_MONO]);;

let BALL_NATIVE_LOOP = prove
 (`!(test:S->(bool)native_result) body (P:num->S->bool) d s.
        P 0 s /\
        (!k s. k < d /\ P k s
               ==> test s = Value T /\
                   ?s'. body s = Value s' /\ P (SUC k) s') /\
        (!s. P d s ==> test s = Value F)
        ==> ?s'. native_loop test body s = Value s' /\ P d s'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!m k t. k + m = d /\ (P:num->S->bool) k t
            ==> ?t'. hol_light_iterate (SUC m) (native_loop_step test body) t =
                     Value t' /\ P d t'`
  MP_TAC THENL
   [INDUCT_TAC THEN MAP_EVERY X_GEN_TAC [`k:num`; `t:S`] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `t:S` THEN
      ASM_SIMP_TAC[hol_light_iterate_DEF; native_loop_step_DEF; NATIVE_BIND;
                   case_native_result_DEF; case_iteration_outcome_DEF];
      FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `t:S`] o
        check (fun th -> can (term_match []
                 `!k (s:S). k < d /\ (P:num->S->bool) k s ==> (q:bool)`)
               (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t1:S` STRIP_ASSUME_TAC)) THEN
      ONCE_REWRITE_TAC[hol_light_iterate_DEF] THEN
      ASM_REWRITE_TAC[native_loop_step_DEF; NATIVE_BIND; map_native_result_DEF;
                      case_native_result_DEF; case_iteration_outcome_DEF] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `SUC k` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPECL [`d:num`; `0`; `s:S`]) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(X_CHOOSE_THEN `s':S` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s':S` THEN ASM_REWRITE_TAC[native_loop_DEF] THEN
    MP_TAC(ISPECL [`native_loop_step (test:S->(bool)native_result) body`;
                   `SUC d`; `s:S`] BALL_NATIVE_ITER) THEN
    ASM_REWRITE_TAC[distinctness "native_result"]]);;

(* ------------------------------------------------------------------------- *)
(* The XOF H of the generated code (SHAKE256 with an explicit context) under *)
(* xof_ok: squeezing n bytes at offset off gives the stream bytes off, ...,  *)
(* off + n - 1 of shake256 of the absorbed bytes.                            *)
(* ------------------------------------------------------------------------- *)


let BALL_MAP_ISA_UPT = prove
 (`!(f:num->A) a n. MAP f (isa_upt a (a + n)) = list_of_seq (\i. f (a + i)) n`,
  REWRITE_TAC[ISA_UPT_ADD; MAP_LIST_OF_SEQ; o_DEF]);;

let BALL_MAP_ISA_UPT_0 = prove
 (`!(f:num->A) n. MAP f (isa_upt 0 n) = list_of_seq f n`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:num->A`; `0`; `n:num`] BALL_MAP_ISA_UPT) THEN
  REWRITE_TAC[ADD_CLAUSES; ETA_AX]);;

let BALL_LIST_OF_SEQ_1 = prove
 (`!f:num->A. list_of_seq f 1 = [f 0]`,
  REWRITE_TAC[num_CONV `1`; list_of_seq; APPEND]);;

(* ------------------------------------------------------------------------- *)
(* Bit strings of byte strings: bits_of_bytes of the generated prelude is    *)
(* the little-endian bit string, and BytesToBitsString_hol computes it.      *)
(* ------------------------------------------------------------------------- *)

let BALL_BITS_OF_BYTES = prove
 (`bits_of_bytes [] = [] /\
   (!b l. bits_of_bytes (CONS b l) =
          APPEND (list_of_seq (\j. bit j b) 8) (bits_of_bytes l))`,
  REWRITE_TAC[bits_of_bytes_DEF; MAP; isa_concat; BALL_MAP_ISA_UPT_0]);;

let BALL_EL_BITS_OF_BYTES = prove
 (`!l k. k < 8 * LENGTH l
         ==> (EL k (bits_of_bytes l) <=> ODD(num_of_bytelist l DIV 2 EXP k))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; MULT_CLAUSES; CONJUNCT1 LT] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BALL_BITS_OF_BYTES; EL_APPEND; LENGTH_LIST_OF_SEQ;
              num_of_bytelist] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[EL_LIST_OF_SEQ; BIT_VAL] THEN
    SUBGOAL_THEN `256 = 2 EXP k * 2 EXP (8 - k)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN
      ASM_SIMP_TAC[ARITH_RULE `k < 8 ==> k + 8 - k = 8`] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MULT_ASSOC] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `a + b * c:num = c * b + a`] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ODD_ADD; ODD_MULT; ODD_EXP; ARITH_ODD] THEN
    ASM_SIMP_TAC[ARITH_RULE `k < 8 ==> ~(8 - k = 0)`];
    FIRST_X_ASSUM(MP_TAC o SPEC `k - 8`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `2 EXP k = 256 * 2 EXP (k - 8)` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_ADD] THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `a + 256 * c:num = c * 256 + a`] THEN
    SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
    MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[DIV_LT; ADD_CLAUSES]]);;

(* ------------------------------------------------------------------------- *)
(* Integer operations of the generated code on naturals.                     *)
(* ------------------------------------------------------------------------- *)

let BALL_ISA_INT_NUM = prove
 (`(!m n. isa_int_mod (&m) (&n) = &(m MOD n)) /\
   (!m n. isa_int_div (&m) (&n) = &(m DIV n))`,
  REWRITE_TAC[isa_int_mod; isa_int_div; INT_OF_NUM_LT; INT_OF_NUM_REM;
              INT_OF_NUM_DIV] THEN
  REWRITE_TAC[ARITH_RULE `~(n < 0)`]);;

let BALL_INT_ARITH = prove
 (`(!m n. typed_hol_int_arithmetic ADiv (&m) (&n) =
          if n = 0 then Fault Bounds_Error else Value (&(m DIV n))) /\
   (!a n. typed_hol_int_arithmetic APow a (&n) = Value (a pow n))`,
  REWRITE_TAC[typed_hol_int_arithmetic_DEF; arith_faults_DEF; int_op_DEF;
              case_aop_DEF; distinctness "aop"; INT_ARITH `~(&n:int < &0)`;
              ISA_NAT_NUM; ISA_INT_DIV_NUM_NUM; INT_OF_NUM_EQ]);;

let BALL_SLICE_0 = prove
 (`!(xs:A list) n.
        typed_hol_list_slice xs (&0) (&n) =
        if n <= LENGTH xs then SOME (isa_take n xs) else NONE`,
  REWRITE_TAC[typed_hol_list_slice_DEF; INT_LE_REFL; INT_POS; INT_OF_NUM_LE;
              INT_SUB_RZERO; ISA_NAT_NUM; ISA_DROP_0]);;

(* ------------------------------------------------------------------------- *)
(* A tactic for the counted loops of the generated code: find the first      *)
(* native_foldl body sched s0 in the goal, with sched of the form            *)
(* native_schedule N (\i. i < &b) (\i. i + &1) (&a), and reduce the goal to  *)
(* P 0 s0 and the step for the invariant ptm (a term \k s. ...), with the    *)
(* final state introduced as a variable named by fname satisfying P n.       *)
(* ------------------------------------------------------------------------- *)

let BALL_SIMP_TAC ths =
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC([TYPED_HOL_EMPTY_SLICE; ISA_NAT_NUM; CONJUNCT1 REPLICATE;
               NATIVE_BIND; TYPED_HOL_READ; TYPED_HOL_SLOT_READ_ASSIGNED; NATIVE_LIST_INDEX_NUM;
               NATIVE_LIST_UPDATE_NUM; LENGTH; EL; HD; TL; UNCURRY_DEF; LT_0] @
              ths);;

let BALL_FOLDL_TAC ptm fname : tactic =
  fun (asl,w) ->
    let is_foldl t =
      match strip_comb t with
        (c,[_;_;_]) -> is_const c && fst(dest_const c) = "native_foldl"
      | _ -> false in
    let tm = find_term is_foldl w in
    let body,sched,s0 = match snd(strip_comb tm) with
        [x;y;z] -> x,y,z | _ -> failwith "BALL_FOLDL_TAC" in
    let nn,guard,_,start = match snd(strip_comb sched) with
        [n;g;x;s] -> n,g,x,s | _ -> failwith "BALL_FOLDL_TAC: schedule" in
    let n1 =
      if is_numeral nn then mk_numeral(dest_numeral nn -/ num 1)
      else if is_comb nn && rator nn = `SUC` then rand nn
      else failwith "BALL_FOLDL_TAC: count" in
    let b = rand(rand(snd(dest_abs guard)))
    and a = rand start in
    let th = ISPECL [body; a; n1; b; ptm; s0] BALL_FOLDL_SCHEDULE in
    let ar,_ = dest_imp(concl th) in
    let th' = MP th (ARITH_RULE ar) in
    let sty = type_of s0 in
    let svar = mk_var(fname, sty) in
    let count_conv t =
      if t = sched then
        RATOR_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV
          (fun n -> if is_numeral n then num_CONV n else REFL n)))) t
      else failwith "count_conv" in
    (CONV_TAC(ONCE_DEPTH_CONV count_conv) THEN
     MP_TAC th' THEN
     ANTS_TAC THENL
      [CONV_TAC(DEPTH_CONV BETA_CONV);
       ANTS_TAC THENL
        [CONV_TAC(DEPTH_CONV BETA_CONV);
         DISCH_THEN(X_CHOOSE_THEN svar
           (CONJUNCTS_THEN2 SUBST1_TAC (ASSUME_TAC o BETA_RULE))) THEN
         REWRITE_TAC[NATIVE_BIND]]]) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* BytesToBits of the generated code.                                        *)
(* ------------------------------------------------------------------------- *)

let BALL_BYTES_TO_BITS_1 = prove
 (`!b:byte. BytesToBits_1_hol [b] = Value (list_of_seq (\j. bit j b) 8)`,
  GEN_TAC THEN REWRITE_TAC[BytesToBits_1_hol_DEF] THEN BALL_SIMP_TAC[] THEN
  REWRITE_TAC[BALL_SLICE_0; LENGTH; ARITH; NATIVE_BIND; TYPED_HOL_READ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[isa_take; NATIVE_BIND; TYPED_HOL_READ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[isa_take] THEN
  BALL_FOLDL_TAC `\k (s:bool list # byte list).
     if k = 0 then s = (REPLICATE 8 F,[b:byte])
     else ?w. s = (list_of_seq (\j. bit j (b:byte)) 8,[w])` "st" THENL
   [REWRITE_TAC[];
    REWRITE_TAC[ARITH_RULE `k < 1 <=> k = 0`] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `s:bool list # byte list`] THEN
    DISCH_THEN(fun th -> let th1,th2 = CONJ_PAIR th in
       SUBST_ALL_TAC th1 THEN SUBST1_TAC (REWRITE_RULE[th1] th2)) THEN
    REWRITE_TAC[ADD_CLAUSES; INT_MUL_RZERO; INT_ADD_LID; ARITH] THEN
    BALL_FOLDL_TAC `\j (s:bool list # byte list).
       ?w. s = (list_of_seq (\t. if t < j then bit t (b:byte) else F) 8,[w]) /\
           val w = val (b:byte) DIV 2 EXP j` "st1" THENL
     [EXISTS_TAC `b:byte` THEN
      REWRITE_TAC[EXP; DIV_1; REPLICATE_LIST_OF_SEQ; CONJUNCT1 LT; PAIR_EQ];
      MAP_EVERY X_GEN_TAC [`j:num`; `s:bool list # byte list`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `w:byte` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
      REWRITE_TAC[ADD_CLAUSES] THEN
      BALL_SIMP_TAC[typed_hol_byte_value_DEF] THEN
      SUBGOAL_THEN `val(b:byte) DIV 2 EXP j DIV 2 < 256` ASSUME_TAC THENL
       [MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
        MP_TAC(SPECL [`val(b:byte)`; `2 EXP j`] DIV_LE) THEN
        REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[BALL_ISA_INT_NUM; TYPED_HOL_INT_TO_BIT_NUM; MOD_LT_EQ;
        ARITH_EQ; NATIVE_BIND; LENGTH_LIST_OF_SEQ; TYPED_HOL_READ;
        ISA_LIST_UPDATE_LIST_OF_SEQ; BALL_INT_ARITH; TYPED_HOL_INT_TO_BYTE_NUM;
        isa_list_update] THEN
      REWRITE_TAC[injectivity "native_result"; UNWIND_THM1] THEN
      EXISTS_TAC `word(val(b:byte) DIV 2 EXP j DIV 2):byte` THEN
      REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN
        DISCH_TAC THEN REWRITE_TAC[LT] THEN ASM_CASES_TAC `i:num = j` THEN
        ASM_REWRITE_TAC[BIT_VAL; ODD_MOD];
        REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_SIMP_TAC[MOD_LT] THEN REWRITE_TAC[EXP; DIV_DIV; MULT_SYM]];
      FIRST_X_ASSUM(X_CHOOSE_THEN `w:byte`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      REWRITE_TAC[injectivity "native_result"; UNWIND_THM1] THEN
      EXISTS_TAC `w:byte` THEN REWRITE_TAC[PAIR_EQ] THEN
      MATCH_MP_TAC LIST_OF_SEQ_EQ THEN SIMP_TAC[]];
    FIRST_X_ASSUM(X_CHOOSE_THEN `w:byte` SUBST1_TAC o
                  REWRITE_RULE[ARITH_EQ]) THEN
    REWRITE_TAC[NATIVE_BIND; UNCURRY_DEF]]);;

let BALL_BYTES_TO_BITS_STRING = prove
 (`!z. BytesToBitsString_hol z = Value (bits_of_bytes z)`,
  GEN_TAC THEN REWRITE_TAC[BytesToBitsString_hol_DEF] THEN BALL_SIMP_TAC[] THEN
  BALL_FOLDL_TAC `\k (s:byte list # bool list).
     ?x. s = ([x], bits_of_bytes (list_of_seq (\i. EL i z) k))` "st" THENL
   [EXISTS_TAC `word 0:byte` THEN
    REWRITE_TAC[REPLICATE_LIST_OF_SEQ; BALL_LIST_OF_SEQ_1; list_of_seq;
                BALL_BITS_OF_BYTES];
    MAP_EVERY X_GEN_TAC [`k:num`; `s:byte list # bool list`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:byte` SUBST1_TAC)) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN BALL_SIMP_TAC[isa_list_update] THEN
    REWRITE_TAC[BALL_BYTES_TO_BITS_1; NATIVE_BIND] THEN
    ASM_SIMP_TAC[TYPED_HOL_LIST_SLICE_ALL; LENGTH_LIST_OF_SEQ; TYPED_HOL_READ; NATIVE_BIND] THEN
    REWRITE_TAC[injectivity "native_result"; UNWIND_THM1] THEN
    EXISTS_TAC `EL k (z:byte list)` THEN
    REWRITE_TAC[list_of_seq; BITS_OF_BYTES_APPEND; BALL_BITS_OF_BYTES;
                APPEND_NIL];
    FIRST_X_ASSUM(X_CHOOSE_THEN `x:byte` SUBST1_TAC) THEN
    REWRITE_TAC[UNCURRY_DEF; LIST_OF_SEQ_EQ_SELF]]);;

(* H on a byte string through HBytesString_hol (which first converts the     *)
(* string with BytesToBitsString_hol) is mldsa_h. This is the one copy of    *)
(* the lemma: BALL_HBYTESSTRING (toplevel.ml) is an alias, and sign.ml and   *)
(* verify.ml prove it again as BALL_HBYTESSTRING and BALL_HBYTESSTRING.      *)

let BALL_HBYTESSTRING = prove
 (`!s n. xof_ok ==> HBytesString_hol s (&n) = Value (mldsa_h s n)`,
  MESON_TAC[EQ_HBYTESSTRING; BALL_BYTES_TO_BITS_STRING]);;

(* ------------------------------------------------------------------------- *)
(* SampleInBall. The handwritten mldsa_ball_pos tau s k is the position of   *)
(* the byte that step k uses: the first one at or after the offset           *)
(*                                                                           *)
(*   off k = if k = 0 then 8 else mldsa_ball_pos tau s (k - 1) + 1           *)
(*                                                                           *)
(* that is <= 256 - tau + k. It exists if there are bytes <= 256 - tau at    *)
(* arbitrarily late positions.                                               *)
(* ------------------------------------------------------------------------- *)


let BALL_POS = prove
 (`!tau (s:num->byte).
        (!N. ?p. N < p /\ val(s p) <= 256 - tau)
        ==> !k. (if k = 0 then 8 else mldsa_ball_pos tau s (k - 1) + 1)
                <= mldsa_ball_pos tau s k /\
                val(s(mldsa_ball_pos tau s k)) <= 256 - tau + k /\
                !q. (if k = 0 then 8 else mldsa_ball_pos tau s (k - 1) + 1)
                    <= q /\ q < mldsa_ball_pos tau s k
                    ==> 256 - tau + k < val(s q)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; mldsa_ball_pos; ADD_CLAUSES] THENL
   [MP_TAC(ISPEC `\p. 8 <= p /\ val((s:num->byte) p) <= 256 - tau`
           MINIMAL) THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `7`) THEN MATCH_MP_TAC MONO_EXISTS THEN
      ARITH_TAC;
      ALL_TAC];
    MP_TAC(ISPEC `\p. mldsa_ball_pos tau s k < p /\
                      val((s:num->byte) p) <= SUC(256 - tau + k)` MINIMAL) THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `mldsa_ball_pos tau s k`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN ARITH_TAC;
      ALL_TAC]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN ASM_REWRITE_TAC[NOT_LE]);;

(* The inner loop of SampleInBall squeezes one byte at a time while the last *)
(* byte is above the bound; it ends at the first position p >= off with a    *)
(* byte <= bound. The loop state is (s, h, h_squeeze, ctx, j, c), of which   *)
(* only ctx, j and the slot h_squeeze change.                                *)

let BALL_SQUEEZE_LOOP = prove
 (`!(test:A#B#(ty_prod_2)native_slot#ty_prod_1#byte list#C->
          (bool)native_result)
    body bound rho off p.
     xof_ok /\
     (!x1 x2 x3 ctx b x6.
         test (x1,x2,x3,ctx,[b],x6) = Value (bound < val b)) /\
     (!x1 x2 x3 ctx j x6.
         body (x1,x2,x3,ctx,j,x6) =
         native_bind (H_Squeeze_hol ctx (&1))
           (\vp. Value (x1,x2,Native_Assigned vp,FST vp,SND vp,x6))) /\
     off <= p /\ val(shake256 rho p) <= bound /\
     (!q. off <= q /\ q < p ==> bound < val(shake256 rho q))
     ==> !x1 x2 x3 x6.
           native_loop test body
             (x1,x2,x3,(rho,Squeezing,off + 1),[shake256 rho off],x6) =
           Value (x1,x2,
                  (if p = off then x3
                   else Native_Assigned ((rho,Squeezing,p + 1),
                                         [shake256 rho p])),
                  (rho,Squeezing,p + 1),[shake256 rho p],x6)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`test:A#B#(ty_prod_2)native_slot#ty_prod_1#byte list#C->
          (bool)native_result`;
    `body:A#B#(ty_prod_2)native_slot#ty_prod_1#byte list#C->
          (A#B#(ty_prod_2)native_slot#ty_prod_1#byte list#C)native_result`;
    `\m (t:A#B#(ty_prod_2)native_slot#ty_prod_1#byte list#C).
        t = (x1,x2,
             (if m = 0 then x3
              else Native_Assigned ((rho,Squeezing,off + m + 1),
                                    [shake256 rho (off + m)])),
             (rho,Squeezing,off + m + 1),[shake256 rho (off + m)],x6)`;
    `p - off:num`;
    `(x1,x2,x3,(rho,Squeezing,off + 1),[shake256 rho off],x6):
     A#B#(ty_prod_2)native_slot#ty_prod_1#byte list#C`]
   BALL_NATIVE_LOOP) THEN
  REWRITE_TAC[ADD_CLAUSES; NOT_SUC; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC
       [`k:num`; `t:A#B#(ty_prod_2)native_slot#ty_prod_1#byte list#C`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
      ASM_SIMP_TAC[H_SQUEEZE_XOF_OK; NATIVE_BIND; BALL_LIST_OF_SEQ_1; ADD_CLAUSES;
                   injectivity "native_result"] THEN
      REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; UNWIND_THM1] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `off <= p ==> off + p - off = p`; GSYM NOT_LE]];
    DISCH_THEN(X_CHOOSE_THEN
      `s':A#B#(ty_prod_2)native_slot#ty_prod_1#byte list#C`
      (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
    ASM_SIMP_TAC[ARITH_RULE `off <= p ==> off + p - off = p`;
                 ARITH_RULE `off <= p ==> (p - off = 0 <=> p = off)`;
                 ARITH_RULE `off <= p ==> off + p - off + 1 = p + 1`]]);;

let BALL_COEFFS_0 = prove
 (`!tau (s:num->byte). mldsa_ball_coeffs tau s 0 = \t. &0`,
  REWRITE_TAC[FUN_EQ_THM; mldsa_ball_coeffs]);;

let BALL_INT_IDX = prove
 (`!a tau. a + tau = 256 ==> !k. (&(a + k) + &tau) - &256:int = &k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&256:int = &a + &tau` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_ADD]; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC);;

(* The inner loop of SampleInBall, for the loop found in the goal.           *)

let BALL_SQUEEZE_TAC bound rho off p : tactic =
  fun (asl,w) ->
    let is_loop t =
      match strip_comb t with
        (c,[_;_;_]) -> is_const c && fst(dest_const c) = "native_loop"
      | _ -> false in
    let tm = find_term is_loop w in
    let test,body = match snd(strip_comb tm) with
        [x;y;_] -> x,y | _ -> failwith "BALL_SQUEEZE_TAC" in
    let th = ISPECL [test; body; bound; rho; off; p] BALL_SQUEEZE_LOOP in
    (MP_TAC th THEN ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
       REWRITE_TAC[UNCURRY_DEF; LENGTH; LT_0; HD; TYPED_HOL_READ; NATIVE_BIND;
                   typed_hol_byte_value_DEF; INT_SUB_LT; INT_OF_NUM_LT];
       DISCH_THEN(fun th -> REWRITE_TAC[th])]) (asl,w);;

(* The proof for one parameter set: cfg is MLDSA44, MLDSA65 or MLDSA87, tau  *)
(* its tau, def the definition of SampleInBall_cfg_Configuration_hol and     *)
(* exts the selector theorems _s_EXT, _h_EXT, _tmp2_EXT, _ctx_EXT, _c_EXT.   *)

let ball_sample_in_ball_gen cfg tau def exts =
  let a = 256 - tau in
  let st = string_of_int tau and sa = string_of_int a in
  let pre = "SampleInBall_" ^ cfg ^ "_Configuration_hol" in
  let goal = parse_term
   ("!rho. xof_ok /\\ (!N. ?p. N < p /\\ val(shake256 rho p) <= 256 - " ^ st ^
    ") ==> " ^ pre ^ " rho = Value (lift_intpoly (mldsa_ball_coeffs " ^ st ^
    " (shake256 rho) " ^ st ^ "))") in
  let inv = parse_term
   ("\\k st. " ^ pre ^ "_emitted_ctx st = Native_Assigned (rho,Squeezing," ^
    "if k = 0 then 8 else mldsa_ball_pos " ^ st ^
    " (shake256 rho) (k - 1) + 1) /\\ " ^
    pre ^ "_emitted_h st = Native_Assigned (bits_of_bytes " ^
    "(list_of_seq (shake256 rho) 8)) /\\ " ^
    pre ^ "_emitted_c st = Native_Assigned (lift_intpoly " ^
    "(mldsa_ball_coeffs " ^ st ^ " (shake256 rho) k))") in
  let hyp = parse_term
   ("!N. ?p. N < p /\\ val(shake256 rho p) <= 256 - " ^ st) in
  let idx = MP (SPECL [mk_small_numeral a; mk_small_numeral tau] BALL_INT_IDX)
               (ARITH_RULE (parse_term (sa ^ " + " ^ st ^ " = 256"))) in
  let facts = parse_term
   ("val (shake256 rho (mldsa_ball_pos " ^ st ^
    " (shake256 rho) k)) < 256 /\\ " ^
    sa ^ " + k < 256 /\\ k < 8 * 8") in
  let bound = parse_term (sa ^ " + k")
  and off = parse_term
   ("if k = 0 then 8 else mldsa_ball_pos " ^ st ^
    " (shake256 rho) (k - 1) + 1")
  and pos = parse_term ("mldsa_ball_pos " ^ st ^ " (shake256 rho) k") in
  prove(goal,
    REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
    BALL_SIMP_TAC[H_INIT; H_ABSORB_ABSORBING; APPEND] THEN
    ASM_SIMP_TAC[H_SQUEEZE_XOF_OK; NATIVE_BIND] THEN
    BALL_SIMP_TAC[BALL_BYTES_TO_BITS_STRING; ADD_CLAUSES; ETA_AX] THEN
    BALL_FOLDL_TAC inv "st" THENL
     [REWRITE_TAC(exts @ [lift_intpoly; BALL_COEFFS_0; REPLICATE_LIST_OF_SEQ]);
      X_GEN_TAC `k:num` THEN GEN_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
      ASM_REWRITE_TAC[TYPED_HOL_SLOT_READ_ASSIGNED; NATIVE_BIND] THEN
      ASM_SIMP_TAC[H_SQUEEZE_XOF_OK; NATIVE_BIND; BALL_LIST_OF_SEQ_1;
                   ADD_CLAUSES] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST; SND] THEN
      MP_TAC(SPEC `k:num` (MATCH_MP (ISPECL [mk_small_numeral tau;
                                             `shake256 rho`] BALL_POS)
                                    (ASSUME hyp))) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN STRIP_TAC THEN
      BALL_SQUEEZE_TAC bound `rho:byte list` off pos THEN
      SUBGOAL_THEN facts STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[NATIVE_BIND; UNCURRY_DEF; TYPED_HOL_SLOT_READ_ASSIGNED; LENGTH; LT_0; HD;
        TYPED_HOL_READ; typed_hol_byte_value_DEF; lift_intpoly;
        fips204_intpoly_coefficients_DEF; NATIVE_LIST_INDEX_NUM; LENGTH_LIST_OF_SEQ;
        typed_hol_nominal_update_DEF; NATIVE_LIST_UPDATE_NUM; idx;
        LENGTH_BITS_OF_BYTES; typed_hol_bit_value_DEF] THEN
      ASM_SIMP_TAC[EL_LIST_OF_SEQ; isa_map_option; TYPED_HOL_READ; NATIVE_BIND;
                   ISA_LIST_UPDATE_LIST_OF_SEQ; LENGTH_LIST_OF_SEQ] THEN
      ASM_SIMP_TAC[fips204_intpoly_coefficients_DEF; LENGTH_LIST_OF_SEQ;
                   ISA_LIST_UPDATE_LIST_OF_SEQ; isa_map_option; TYPED_HOL_READ;
                   NATIVE_BIND] THEN
      SUBGOAL_THEN
       `EL k (bits_of_bytes (list_of_seq (shake256 rho) 8)) <=>
        ODD(num_of_bytelist (list_of_seq (shake256 rho) 8) DIV 2 EXP k)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC BALL_EL_BITS_OF_BYTES THEN
        ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ];
        ALL_TAC] THEN
      ASM_CASES_TAC
       `ODD(num_of_bytelist (list_of_seq (shake256 rho) 8) DIV 2 EXP k)` THEN
      ASM_REWRITE_TAC[BALL_INT_ARITH; INT_POW_1; INT_POW; NATIVE_BIND;
                      injectivity "native_result"; UNWIND_THM1] THEN
      REWRITE_TAC(exts @ [NOT_SUC; SUC_SUB1; injectivity "native_slot";
                          injectivity "fips204_intpoly"]) THEN
      MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN
      DISCH_TAC THEN REWRITE_TAC[mldsa_ball_coeffs] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[TYPED_HOL_SLOT_READ_ASSIGNED]]);;

let BALL_SAMPLE_IN_BALL_MLDSA44 = ball_sample_in_ball_gen "MLDSA44" 39
  SampleInBall_MLDSA44_Configuration_hol_DEF
  [SampleInBall_MLDSA44_Configuration_hol_emitted_s_EXT;
   SampleInBall_MLDSA44_Configuration_hol_emitted_h_EXT;
   SampleInBall_MLDSA44_Configuration_hol_emitted_tmp2_EXT;
   SampleInBall_MLDSA44_Configuration_hol_emitted_ctx_EXT;
   SampleInBall_MLDSA44_Configuration_hol_emitted_c_EXT];;

let BALL_SAMPLE_IN_BALL_MLDSA65 = ball_sample_in_ball_gen "MLDSA65" 49
  SampleInBall_MLDSA65_Configuration_hol_DEF
  [SampleInBall_MLDSA65_Configuration_hol_emitted_s_EXT;
   SampleInBall_MLDSA65_Configuration_hol_emitted_h_EXT;
   SampleInBall_MLDSA65_Configuration_hol_emitted_tmp2_EXT;
   SampleInBall_MLDSA65_Configuration_hol_emitted_ctx_EXT;
   SampleInBall_MLDSA65_Configuration_hol_emitted_c_EXT];;

let BALL_SAMPLE_IN_BALL_MLDSA87 = ball_sample_in_ball_gen "MLDSA87" 60
  SampleInBall_MLDSA87_Configuration_hol_DEF
  [SampleInBall_MLDSA87_Configuration_hol_emitted_s_EXT;
   SampleInBall_MLDSA87_Configuration_hol_emitted_h_EXT;
   SampleInBall_MLDSA87_Configuration_hol_emitted_tmp2_EXT;
   SampleInBall_MLDSA87_Configuration_hol_emitted_ctx_EXT;
   SampleInBall_MLDSA87_Configuration_hol_emitted_c_EXT];;

(* ------------------------------------------------------------------------- *)
(* The equivalence: for seeds of fewer than 135 bytes (one SHAKE256 block,   *)
(* so all c-tilde of lam / 4 <= 64 bytes) the generated SampleInBall         *)
(* terminates and gives the coefficients of the handwritten recursion, by    *)
(* MLDSA_SAMPLE_IN_BALL_TERMINATES. The handwritten mldsa_sample_in_ball     *)
(* tau rho is mldsa_poly of the same coefficient array.                      *)
(* ------------------------------------------------------------------------- *)

let ball_eq_sample_in_ball th tau =
  GEN `rho:byte list` (DISCH_ALL
   (MP (SPEC `rho:byte list` th)
       (CONJ (ASSUME `xof_ok`)
             (GEN `N:num`
               (MP (SPECL [mk_small_numeral tau; `rho:byte list`; `N:num`]
                          MLDSA_SAMPLE_IN_BALL_TERMINATES)
                   (CONJ (ASSUME `LENGTH(rho:byte list) < 135`)
                         (ARITH_RULE (mk_binary "<=" (mk_small_numeral tau,
                                                      `128`)))))))));;

let EQ_SAMPLEINBALL_MLDSA44 = prove
 (`!rho. xof_ok /\ LENGTH rho < 135
         ==> SampleInBall_MLDSA44_Configuration_hol rho =
             Value (lift_intpoly (mldsa_ball_coeffs 39 (shake256 rho) 39))`,
  MESON_TAC[ball_eq_sample_in_ball BALL_SAMPLE_IN_BALL_MLDSA44 39]);;

let EQ_SAMPLEINBALL_MLDSA65 = prove
 (`!rho. xof_ok /\ LENGTH rho < 135
         ==> SampleInBall_MLDSA65_Configuration_hol rho =
             Value (lift_intpoly (mldsa_ball_coeffs 49 (shake256 rho) 49))`,
  MESON_TAC[ball_eq_sample_in_ball BALL_SAMPLE_IN_BALL_MLDSA65 49]);;

let EQ_SAMPLEINBALL_MLDSA87 = prove
 (`!rho. xof_ok /\ LENGTH rho < 135
         ==> SampleInBall_MLDSA87_Configuration_hol rho =
             Value (lift_intpoly (mldsa_ball_coeffs 60 (shake256 rho) 60))`,
  MESON_TAC[ball_eq_sample_in_ball BALL_SAMPLE_IN_BALL_MLDSA87 60]);;

(* ------------------------------------------------------------------------- *)
(* BytesToBits_n_hol for byte strings of n bytes (the generated code has one *)
(* constant per length): the bit string bits_of_bytes, bit j of byte i at    *)
(* position 8 * i + j.                                                       *)
(* ------------------------------------------------------------------------- *)

let BALL_EL_BITS_OF_BYTES_BIT = prove
 (`!l k. k < 8 * LENGTH l
         ==> EL k (bits_of_bytes l) = bit (k MOD 8) (EL (k DIV 8) l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; MULT_CLAUSES; CONJUNCT1 LT] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BALL_BITS_OF_BYTES; EL_APPEND; LENGTH_LIST_OF_SEQ] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[EL_LIST_OF_SEQ; MOD_LT; DIV_LT; EL; HD];
    FIRST_X_ASSUM(MP_TAC o SPEC `k - 8`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_LT]) THEN
    REWRITE_TAC[LE_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
    REWRITE_TAC[ADD_SUB2] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `8 + d = 1 * 8 + d`] THEN
    SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `1 + n = SUC n`; EL; TL]]);;

let BALL_DIV_MOD_8 = prove
 (`!i j. j < 8 ==> (8 * i + j) MOD 8 = j /\ (8 * i + j) DIV 8 = i`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT; DIV_MULT_ADD; DIV_LT; ARITH_EQ;
               ADD_CLAUSES]);;

let ball_bytes_to_bits_gen n def =
  let sn = string_of_int n and s8n = string_of_int (8 * n) in
  let goal = parse_term
   ("!z. LENGTH z = " ^ sn ^ " ==> BytesToBits_" ^ sn ^
    "_hol z = Value (bits_of_bytes z)") in
  let pinv = parse_term
   ("\\i (s:bool list # byte list). ?zz. s = " ^
    "(list_of_seq (\\t. if t < 8 * i " ^
    "then EL t (bits_of_bytes z) else F) " ^ s8n ^ ", zz) /\\ " ^
    "LENGTH zz = " ^ sn ^ " /\\ !t. i <= t /\\ t < " ^ sn ^
    " ==> EL t zz = EL t (z:byte list)") in
  let qinv = parse_term
   ("\\j (s:bool list # byte list). ?zz. s = " ^
    "(list_of_seq (\\t. if t < 8 * i + j " ^
    "then EL t (bits_of_bytes z) else F) " ^ s8n ^ ", zz) /\\ " ^
    "LENGTH zz = " ^ sn ^ " /\\ (!t. i < t /\\ t < " ^ sn ^
    " ==> EL t zz = EL t (z:byte list)) /\\ " ^
    "val(EL i zz) = val(EL i (z:byte list)) DIV 2 EXP j") in
  let len = parse_term ("LENGTH(z:byte list) = " ^ sn) in
  let facts = parse_term
   ("val(EL i (yy:byte list)) DIV 2 < 256 /\\ " ^
    "val(EL i (z:byte list)) DIV 2 EXP j DIV 2 < 256 /\\ 8 * i + j < " ^ s8n ^
    " /\\ i < LENGTH yy /\\ 8 * i + j < 8 * LENGTH(z:byte list)") in
  prove(goal,
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[def] THEN BALL_SIMP_TAC[] THEN
    ASM_SIMP_TAC[TYPED_HOL_LIST_SLICE_ALL; TYPED_HOL_READ; NATIVE_BIND] THEN
    BALL_FOLDL_TAC pinv "st" THENL
     [EXISTS_TAC `z:byte list` THEN
      ASM_REWRITE_TAC[REPLICATE_LIST_OF_SEQ; MULT_CLAUSES; CONJUNCT1 LT];
      X_GEN_TAC `i:num` THEN GEN_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `zz:byte list` (CONJUNCTS_THEN2 SUBST1_TAC
          STRIP_ASSUME_TAC))) THEN
      REWRITE_TAC[ADD_CLAUSES] THEN
      BALL_FOLDL_TAC qinv "st1" THENL
       [EXISTS_TAC `zz:byte list` THEN
        ASM_SIMP_TAC[ADD_CLAUSES; EXP; DIV_1; LE_REFL; LT_IMP_LE];
        X_GEN_TAC `j:num` THEN GEN_TAC THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
         (X_CHOOSE_THEN `yy:byte list` (CONJUNCTS_THEN2 SUBST1_TAC
            STRIP_ASSUME_TAC))) THEN
        REWRITE_TAC[ADD_CLAUSES; INT_OF_NUM_MUL; INT_OF_NUM_ADD] THEN
        BALL_SIMP_TAC[typed_hol_byte_value_DEF] THEN
        SUBGOAL_THEN facts STRIP_ASSUME_TAC THENL
         [MP_TAC(ISPEC `EL i (yy:byte list)` VAL_BOUND) THEN
          REWRITE_TAC[DIMINDEX_8] THEN UNDISCH_TAC len THEN
          FIRST_ASSUM(fun th -> if is_eq(concl th) &&
             can (find_term ((=) `2 EXP j`)) (concl th)
             then REWRITE_TAC[th] else NO_TAC) THEN ASM_ARITH_TAC;
          ALL_TAC] THEN
        ASM_REWRITE_TAC[BALL_ISA_INT_NUM; TYPED_HOL_INT_TO_BIT_NUM; MOD_LT_EQ;
          ARITH_EQ; NATIVE_BIND; LENGTH_LIST_OF_SEQ; TYPED_HOL_READ;
          ISA_LIST_UPDATE_LIST_OF_SEQ; BALL_INT_ARITH; TYPED_HOL_INT_TO_BYTE_NUM] THEN
        ASM_REWRITE_TAC[NATIVE_BIND; TYPED_HOL_READ; LENGTH_ISA_LIST_UPDATE;
                        injectivity "native_result"; UNWIND_THM1] THEN
        EXISTS_TAC
         `isa_list_update yy i (word(val(EL i (yy:byte list)) DIV 2))` THEN
        ASM_SIMP_TAC[PAIR_EQ; LENGTH_ISA_LIST_UPDATE;
                     EL_ISA_LIST_UPDATE] THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `t:num` THEN
          DISCH_TAC THEN REWRITE_TAC[ADD_CLAUSES; LT] THEN
          ASM_CASES_TAC `t = 8 * i + j` THEN ASM_REWRITE_TAC[] THEN
          ASM_SIMP_TAC[BALL_EL_BITS_OF_BYTES_BIT] THEN
          ASM_SIMP_TAC[BALL_DIV_MOD_8] THEN
          ASM_REWRITE_TAC[BIT_VAL; ODD_MOD];
          SIMP_TAC[ARITH_RULE `i < t ==> ~(t = i)`];
          REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
          ASM_SIMP_TAC[MOD_LT] THEN REWRITE_TAC[EXP; DIV_DIV; MULT_SYM]];
        FIRST_X_ASSUM(X_CHOOSE_THEN `yy:byte list`
          (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
        REWRITE_TAC[injectivity "native_result"; UNWIND_THM1] THEN
        EXISTS_TAC `yy:byte list` THEN
        ASM_SIMP_TAC[PAIR_EQ; ARITH_RULE `8 * SUC i = 8 * i + 8`] THEN
        X_GEN_TAC `t:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_ARITH_TAC];
      FIRST_X_ASSUM(X_CHOOSE_THEN `zz:byte list`
        (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
      REWRITE_TAC[UNCURRY_DEF] THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LIST_OF_SEQ_EQ_SELF] THEN
      ASM_REWRITE_TAC[LENGTH_BITS_OF_BYTES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC LIST_OF_SEQ_EQ THEN SIMP_TAC[]]);;

let BALL_BYTES_TO_BITS_66 = ball_bytes_to_bits_gen 66 BytesToBits_66_hol_DEF;;

(* ------------------------------------------------------------------------- *)
(* IntegerToBytes(x,2), the one-shot H over a bit string, and bitlen.        *)
(* ------------------------------------------------------------------------- *)


let BALL_H_HOL = prove
 (`!s n. xof_ok ==> H_hol (bits_of_bytes s) (&n) = Value (mldsa_h s n)`,
  REWRITE_TAC[xof_ok] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[H_hol_DEF] THEN BALL_SIMP_TAC[] THEN
  REWRITE_TAC[SHAKE256_semantic_DEF; UNCURRY_DEF; SHAKE256_DEF] THEN
  REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_LT; CONJUNCT1 LT;
              ISA_NAT_NUM] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
  ASM_REWRITE_TAC[BALL_MAP_ISA_UPT_0; mldsa_h]);;

let BALL_LENGTH_MLDSA_H = prove
 (`!s n. LENGTH (mldsa_h s n) = n`,
  REWRITE_TAC[mldsa_h; LENGTH_LIST_OF_SEQ]);;

(* HBytes over a string of 66 bytes, as used by ExpandMask.                  *)

let BALL_HBYTES_66 = prove
 (`!str n. xof_ok /\ LENGTH str = 66
           ==> HBytes_66_hol str (&n) = Value (mldsa_h str n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HBytes_66_hol_DEF] THEN
  BALL_SIMP_TAC[] THEN
  ASM_SIMP_TAC[BALL_BYTES_TO_BITS_66; NATIVE_BIND] THEN
  ASM_SIMP_TAC[TYPED_HOL_LIST_SLICE_ALL; LENGTH_BITS_OF_BYTES; ARITH; TYPED_HOL_READ;
               NATIVE_BIND; BALL_H_HOL]);;

let BALL_BITLEN = prove
 (`bitlen 131071 = 17 /\ bitlen 524287 = 19`,
  REPEAT(ONCE_REWRITE_TAC[bitlen_DEF] THEN
         CONV_TAC(NUM_REDUCE_CONV THENC REWRITE_CONV[])));;

let BALL_MLDSA_BITLEN = prove
 (`mldsa_bitlen 131071 = 17 /\ mldsa_bitlen 524287 = 19`,
  let tac e =
    MATCH_MP_TAC MINIMAL_UNIQUE THEN REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[NOT_LT] THEN
    TRANS_TAC LE_TRANS (mk_comb(`(EXP) 2`, mk_small_numeral e)) THEN
    REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC in
  REWRITE_TAC[mldsa_bitlen] THEN CONJ_TAC THENL [tac 16; tac 18]);;

(* ------------------------------------------------------------------------- *)
(* BitUnpack (FIPS 204 Algorithm 19) for the two instances of ExpandMask,    *)
(* proved here locally: BitsToInteger of the bits at positions o, ..., o +   *)
(* c - 1 of a byte string is field c at offset o of its numeric value.       *)
(* ------------------------------------------------------------------------- *)


let BALL_SLICE = prove
 (`!(xs:A list) l u.
        l <= u /\ u <= LENGTH xs
        ==> typed_hol_list_slice xs (&l) (&u) =
            SOME (list_of_seq (\i. EL (l + i) xs) (u - l))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[typed_hol_list_slice_DEF; INT_POS; INT_OF_NUM_LE] THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB; ISA_NAT_NUM; option_INJ] THEN
  REWRITE_TAC[LIST_EQ; LENGTH_ISA_TAKE_LIST_FIRST; LENGTH_ISA_DROP_LIST_FIRST;
              LENGTH_LIST_OF_SEQ] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_ISA_TAKE_LIST_FIRST o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_ISA_DROP_LIST_FIRST] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `i < LENGTH(xs:A list) - l` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[EL_ISA_DROP_LIST_FIRST; EL_LIST_OF_SEQ]]);;

let BALL_BITS_TO_INTEGER = prove
 (`!y c M off.
        LENGTH y = c /\
        (!t. t < c ==> (EL t y <=> ODD(M DIV 2 EXP (off + t))))
        ==> BitsToInteger_hol y (&c) =
            Value (&((M DIV 2 EXP off) MOD 2 EXP c))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BitsToInteger_hol_DEF] THEN
  REWRITE_TAC[INT_ARITH `(x + &1) - &1:int = x`; ISA_NAT_NUM;
              INT_OF_NUM_ADD] THEN
  BALL_FOLDL_TAC `\k (x:int). x = &((M DIV 2 EXP (off + c - k)) MOD 2 EXP k)`
    "st" THENL
   [REWRITE_TAC[EXP; MOD_1];
    MAP_EVERY X_GEN_TAC [`k:num`; `x:int`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_SIMP_TAC[INT_OF_NUM_SUB; ARITH_RULE `k < c ==> 1 + k <= c`] THEN
    ASM_SIMP_TAC[NATIVE_LIST_INDEX_NUM; ARITH_RULE `k < c ==> c - (1 + k) < c`;
                 TYPED_HOL_READ; NATIVE_BIND; typed_hol_bit_value_DEF] THEN
    ASM_SIMP_TAC[ARITH_RULE `k < c ==> c - (1 + k) < c`] THEN
    REWRITE_TAC[injectivity "native_result"; UNWIND_THM1] THEN
    SUBGOAL_THEN
     `M DIV 2 EXP (off + c - k) = (M DIV 2 EXP (off + c - SUC k)) DIV 2`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `off + c - k = SUC(off + c - SUC k)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[EXP; DIV_DIV; MULT_SYM]];
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `1 + k = SUC k`] THEN
    SPEC_TAC(`M DIV 2 EXP (off + c - SUC k)`,`K:num`) THEN GEN_TAC THEN
    REWRITE_TAC[EXP; MOD_MULT_MOD] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_ADD] THEN
    REWRITE_TAC[ODD_MOD] THEN
    MP_TAC(SPECL [`K:num`; `2`] MOD_LT_EQ) THEN REWRITE_TAC[ARITH_EQ] THEN
    SPEC_TAC(`K MOD 2`,`b:num`) THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `b < 2 <=> b = 0 \/ b = 1`] THEN
    ASM_CASES_TAC `b = 0` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ASM_REWRITE_TAC[ARITH_RULE `off + c - c = off`]]);;

let BALL_BYTES_TO_BITS_576 =
  ball_bytes_to_bits_gen 576 BytesToBits_576_hol_DEF;;

let BALL_BYTES_TO_BITS_640 =
  ball_bytes_to_bits_gen 640 BytesToBits_640_hol_DEF;;

let ball_bitlen_fact n c =
  prove(parse_term (Printf.sprintf "bitlen %d = %d" n c),
   REPEAT(ONCE_REWRITE_TAC[bitlen_DEF] THEN
          CONV_TAC(NUM_REDUCE_CONV THENC REWRITE_CONV[])));;

(* BitUnpack and SimpleBitUnpack (FIPS 204 Algorithms 18 and 19): for LENGTH *)
(* v = 32 * c, coefficient i is b - mldsa_field c v i (resp. mldsa_field c v *)
(* i), where c = bitlen(a + b) (resp. bitlen b). The arguments of the        *)
(* generator are simple a b c, the generated definition and the theorem for  *)
(* BytesToBits of 32 * c bytes.                                              *)

let ball_bitunpack_gen simple a b c def b2b =
  let sg = string_of_int b and sa = string_of_int a
  and sc = string_of_int c and sb = string_of_int (32 * c) in
  let xs = if simple then "" else "&" ^ sg ^ " - " in
  let goal = parse_term
   (if simple then
    ("!v. LENGTH v = " ^ sb ^ " ==> SimpleBitUnpack_" ^ sg ^
     "_hol v (&" ^ sg ^ ") = Value (lift_intpoly " ^
     "(\\i. mldsa_field " ^ sc ^ " v i))")
    else
    ("!v. LENGTH v = " ^ sb ^ " ==> BitUnpack_" ^ sa ^ "_" ^ sg ^
     "_hol v (&" ^ sa ^ ") (&" ^ sg ^ ") = Value (lift_intpoly " ^
     "(\\i. &" ^ sg ^ " - mldsa_field " ^ sc ^ " v i))")) in
  let inv = parse_term
   ("\\k (w:fips204_intpoly). w = FIPS204_IntPoly (list_of_seq " ^
    "(\\i. if i < k then " ^ xs ^ "mldsa_field " ^ sc ^
    " v i else &0) 256)") in
  let bounds = parse_term
   ("k * " ^ sc ^ " <= k * " ^ sc ^ " + " ^ sc ^ " /\\ k * " ^ sc ^ " + " ^
    sc ^ " <= LENGTH(bits_of_bytes v)") in
  let seg = parse_term
   ("list_of_seq (\\i. EL (k * " ^ sc ^ " + i) (bits_of_bytes v)) " ^ sc) in
  let blen = ball_bitlen_fact (if simple then b else a + b) c in
  let comm = ARITH_RULE (parse_term (sc ^ " * k = k * " ^ sc)) in
  prove(goal,
    REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
    BALL_SIMP_TAC[] THEN CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
    REWRITE_TAC[bitlen_semantic_DEF; ISA_NAT_NUM; blen;
                INT_ARITH `~(&n:int < &0)`; NATIVE_BIND] THEN
    ASM_SIMP_TAC[b2b; NATIVE_BIND] THEN
    ASM_SIMP_TAC[TYPED_HOL_LIST_SLICE_ALL; LENGTH_BITS_OF_BYTES; ARITH; TYPED_HOL_READ;
                 NATIVE_BIND] THEN
    BALL_FOLDL_TAC inv "st" THENL
     [REWRITE_TAC[CONJUNCT1 LT; REPLICATE_LIST_OF_SEQ];
      X_GEN_TAC `k:num` THEN GEN_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
      REWRITE_TAC[ADD_CLAUSES; typed_hol_nonnegative_DEF; INT_POS; NATIVE_BIND;
                  INT_OF_NUM_MUL; BALL_INT_ARITH; INT_POW_ONE; INT_MUL_RID;
                  INT_OF_NUM_ADD; MULT_CLAUSES] THEN
      SUBGOAL_THEN bounds STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[LENGTH_BITS_OF_BYTES] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[BALL_SLICE; TYPED_HOL_READ; NATIVE_BIND;
                   ARITH_RULE `(a + b) - a = b`] THEN
      MP_TAC(ISPECL [seg; mk_small_numeral c; `num_of_bytelist v`;
                     mk_binop `( * ):num->num->num` `k:num`
                       (mk_small_numeral c)] BALL_BITS_TO_INTEGER) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
        MATCH_MP_TAC BALL_EL_BITS_OF_BYTES THEN ASM_ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[NATIVE_BIND; typed_hol_nominal_update_DEF;
        fips204_intpoly_coefficients_DEF; NATIVE_LIST_UPDATE_NUM; LENGTH_LIST_OF_SEQ;
        isa_map_option; TYPED_HOL_READ; ISA_LIST_UPDATE_LIST_OF_SEQ;
        injectivity "native_result"; UNWIND_THM1;
        injectivity "fips204_intpoly"] THEN
      MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN
      DISCH_TAC THEN REWRITE_TAC[LT] THEN ASM_CASES_TAC `i:num = k` THEN
      ASM_REWRITE_TAC[mldsa_field; comm];
      ASM_REWRITE_TAC[lift_intpoly; injectivity "native_result";
                      injectivity "fips204_intpoly"] THEN
      MATCH_MP_TAC LIST_OF_SEQ_EQ THEN SIMP_TAC[]]);;

let BALL_BITUNPACK_131071 = ball_bitunpack_gen false 131071 131072 18
  BitUnpack_131071_131072_hol_DEF BALL_BYTES_TO_BITS_576;;

let BALL_BITUNPACK_524287 = ball_bitunpack_gen false 524287 524288 20
  BitUnpack_524287_524288_hol_DEF BALL_BYTES_TO_BITS_640;;

(* ------------------------------------------------------------------------- *)
(* ExpandMask. The generated ExpandMask_P_hol rho mu returns the vector of l *)
(* integer polynomials y[r] = BitUnpack(H(rho || IntegerToBytes(mu + r, 2),  *)
(* 32 * c), gamma1 - 1, gamma1) with c = 1 + bitlen(gamma1 - 1), for a seed  *)
(* rho of 64 bytes (the generated signing code checks this length). The      *)
(* coefficients are gamma1 - field, not reduced mod q; mldsa_expand_mask is  *)
(* mldsa_poly of the same array (BALL_EXPAND_MASK).                          *)
(* ------------------------------------------------------------------------- *)

let BALL_MAP_REPLICATE = prove
 (`!(f:A->B) n x. MAP f (REPLICATE n x) = list_of_seq (\i. f x) n`,
  REWRITE_TAC[REPLICATE_LIST_OF_SEQ; MAP_LIST_OF_SEQ; o_DEF]);;

let ball_expand_mask_gen cfg l g1 c bustmt def =
  let sl = string_of_int l and sg = string_of_int g1 and sc = string_of_int c
  and sb = string_of_int (32 * c) in
  let coeffs r =
    "(\\t. &" ^ sg ^ " - mldsa_field " ^ sc ^
    " (mldsa_h (APPEND rho (bytelist_of_num 2 (kappa + " ^ r ^ "))) " ^ sb ^
    ") t)" in
  let goal = mk_imp(bustmt, parse_term
   ("!rho kappa. xof_ok /\\ LENGTH rho = 64 ==> ExpandMask_" ^ cfg ^
    "_Configuration_hol rho (&kappa) = Value (lift_vec (\\r. lift_intpoly " ^
    coeffs "r" ^ "))")) in
  let inv = parse_term
   ("\\r (y:(" ^ sl ^ ",fips204_intpoly)common_vec). y = Common_Vec " ^
    "(list_of_seq (\\i. if i < r then lift_intpoly " ^ coeffs "i" ^
    " else FIPS204_IntPoly (REPLICATE 256 (&0))) " ^ sl ^ ")") in
  prove(goal,
    DISCH_TAC THEN REPEAT STRIP_TAC THEN REWRITE_TAC[def] THEN
    BALL_SIMP_TAC[] THEN
    REWRITE_TAC[bitlen_semantic_DEF; ISA_NAT_NUM; BALL_BITLEN;
                INT_ARITH `~(&n:int < &0)`; NATIVE_BIND] THEN
    CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
    BALL_FOLDL_TAC inv "st" THENL
     [REWRITE_TAC[CONJUNCT1 LT; BALL_MAP_REPLICATE];
      X_GEN_TAC `k:num` THEN GEN_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
      REWRITE_TAC[ADD_CLAUSES; INT_OF_NUM_ADD; INTEGER_TO_BYTES_2_NUM;
                  NATIVE_BIND] THEN
      ASM_SIMP_TAC[BALL_HBYTES_66; LENGTH_APPEND; LENGTH_BYTELIST_OF_NUM;
                   ARITH; NATIVE_BIND] THEN
      REWRITE_TAC[typed_hol_nonnegative_DEF; INT_POS; NATIVE_BIND] THEN
      SIMP_TAC[typed_hol_sequence_extent_DEF; BALL_LENGTH_MLDSA_H;
               NATIVE_BIND] THEN
      ASM_SIMP_TAC[BALL_LENGTH_MLDSA_H; NATIVE_BIND;
                   typed_hol_nominal_update_DEF;
                   common_vec_SEL_CTR; NATIVE_LIST_UPDATE_NUM; LENGTH_LIST_OF_SEQ;
                   isa_map_option; TYPED_HOL_READ; ISA_LIST_UPDATE_LIST_OF_SEQ;
                   injectivity "native_result"; UNWIND_THM1] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[LT] THEN
      ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM SUBST1_TAC THEN
      REWRITE_TAC[injectivity "native_result"; lift_vec] THEN
      CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN AP_TERM_TAC THEN
      MATCH_MP_TAC LIST_OF_SEQ_EQ THEN SIMP_TAC[]]);;

let EQ_EXPANDMASK_MLDSA44 =
  MP (ball_expand_mask_gen "MLDSA44" 4 131072 18
        (concl BALL_BITUNPACK_131071) ExpandMask_MLDSA44_Configuration_hol_DEF)
     BALL_BITUNPACK_131071;;

let EQ_EXPANDMASK_MLDSA65 =
  MP (ball_expand_mask_gen "MLDSA65" 5 524288 20
        (concl BALL_BITUNPACK_524287) ExpandMask_MLDSA65_Configuration_hol_DEF)
     BALL_BITUNPACK_524287;;

let EQ_EXPANDMASK_MLDSA87 =
  MP (ball_expand_mask_gen "MLDSA87" 7 524288 20
        (concl BALL_BITUNPACK_524287) ExpandMask_MLDSA87_Configuration_hol_DEF)
     BALL_BITUNPACK_524287;;

(* The handwritten ExpandMask polynomials: mldsa_poly of the same arrays.    *)

let BALL_EXPAND_MASK = prove
 (`(!rho kappa r.
      mldsa_expand_mask 131072 rho kappa r =
      mldsa_poly (\i. &131072 - mldsa_field 18
                   (mldsa_h (APPEND rho (bytelist_of_num 2 (kappa + r))) 576)
                   i)) /\
   (!rho kappa r.
      mldsa_expand_mask 524288 rho kappa r =
      mldsa_poly (\i. &524288 - mldsa_field 20
                   (mldsa_h (APPEND rho (bytelist_of_num 2 (kappa + r))) 640)
                   i))`,
  REWRITE_TAC[mldsa_expand_mask] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BALL_MLDSA_BITLEN] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;
