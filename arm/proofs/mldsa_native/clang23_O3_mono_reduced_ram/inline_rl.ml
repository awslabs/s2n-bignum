(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the loops that clang 23 -O3 has inlined into                   *)
(* mldsa{44,65,87}_polyvec_matrix_pointwise_montgomery_row_lazy of           *)
(* mldsa-native's monolithic reduced-RAM build, stated from the head of the  *)
(* loop or region to its exit with the registers as parameters (see          *)
(* inline_sign.ml for the form of the lemmas): the pointwise Montgomery      *)
(* product of two polynomials with one coefficient per iteration, and the   *)
(* sum of two polynomials as straight-line code of 128-bit loads, adds and   *)
(* stores, which the code takes when the two do not overlap. The reduction   *)
(* of the sum is the loop of INLINE_REDUCE_LOOP of inline_sign_arith.ml.     *)
(* ========================================================================= *)

needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_pwm.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;

(* ------------------------------------------------------------------------- *)
(* The pointwise Montgomery product, one coefficient per iteration, in       *)
(* place at A with B (registers A, B, I, QI, NQ, T1, T2):                    *)
(*   ldrsw T1, [A, I]; ldrsw T2, [B, I]; smull T1, w.T2, w.T1;               *)
(*   mul T2, T1, QI; asr T2, T2, #32; smaddl T1, w.T2, w.NQ, T1;             *)
(*   lsr T1, T1, #32; str w.T1, [A, I]; add I, I, #4; cmp I, #0x400; b.ne    *)
(* ------------------------------------------------------------------------- *)

let RL_PWM1_LOOP_TERM mc loop exit (rs:string list) =
  let r k = List.nth rs k in
  (* rs: A, B, I, QI, NQ, T1, T2 *)
  parse_term(Printf.sprintf
   "exists f_events.
      forall e a b (x:num->int32) (y:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size); (b,1024)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = a /\\ read %s s = b /\\
                  read %s s = word 0 /\\
                  read %s s = word 0x0380200100000000 /\\
                  read %s s = word 0xffffffffff801fff /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add b (word(4 * i))))
                             s = y i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read %s s = word 1024 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = mld_poly_pointwise_montgomery x y i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a b pc /\\
                     memaccess_inbounds e2 [a,1024; b,1024] [a,1024]))
             (MAYCHANGE [PC; %s; %s; %s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,1024)])"
   mc loop (r 0) (r 1) (r 2) (r 3) (r 4) exit (r 2) (r 2) (r 5) (r 6));;

let RL_PWM1_LOOP mc exec loop exit (rs:string list) =
  let r k = List.nth rs k in
  let tm = RL_PWM1_LOOP_TERM mc loop exit rs in
  let inv = parse_term(Printf.sprintf
   "\\i s. read %s s = a /\\ read %s s = b /\\ read %s s = word(4 * i) /\\
          read %s s = word 0x0380200100000000 /\\
          read %s s = word 0xffffffffff801fff /\\
          (!j. i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   (x:num->int32) j) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s =
                   (y:num->int32) j) /\\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_montgomery_reduce
                    (word_mul (word_sx (x j)) (word_sx (y j))))"
   (r 0) (r 1) (r 2) (r 3) (r 4)) in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (b:int64) (pc:num).
      APPEND (f_ev_epil a b pc)
       (APPEND (ENUMERATEL 256 (\i. f_ev_loop a b pc i)) (f_ev_prol a b pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `b:int64`;
                       `x:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS;
              mld_poly_pointwise_montgomery; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_forall c && free_in `y:num->int32` c &&
         not(free_in `x:num->int32` c)
      then ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `i < 256`))
      else NO_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_montgomery_reduce` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ARM_STEPS_TAC exec (1--11) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INLINE_SMULL; INLINE_MONTRED_LANE]) THEN
    FULL_FINAL_TAC [ONE_OUTPUT_SPLIT];

    INLINE_EXIT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The sum of two polynomials at the pointers A = X19 and B = X20 (the sum   *)
(* replaces A), as 163 instructions of straight-line code.                   *)
(* ------------------------------------------------------------------------- *)

(* The 64 128-bit values of the polynomial x at the pointer a *)
let RL_VINPUT_TAC (a:term) (x:term) =
  let addr n = if n = 0 then a else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,a),
            mk_comb(`word:num->int64`,mk_small_numeral n)) in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if not(is_forall c && free_in x c && free_in a c &&
           not(free_in `mld_poly_add` c)) then NO_TAC else
    let lanes = map (fun i ->
      let th1 = SPEC (mk_small_numeral i) th in
      let th2 = MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1)))) in
      REWRITE_RULE[WORD_ADD_0]
        (CONV_RULE(LAND_CONV(DEPTH_CONV NUM_RED_CONV)) th2)) (0--255) in
    let ths = map (fun k ->
      let tm = subst [addr(16 * k),`A:int64`]
                `read (memory :> bytes128 A) (s0:armstate)` in
      let eth = READ_MEMORY_MERGE_CONV 2 tm in
      let eth = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV
                  NORMALIZE_RELATIVE_ADDRESS_CONV)) eth in
      REWRITE_RULE lanes eth) (0--63) in
    MAP_EVERY ASSUME_TAC ths);;

(* The facts about the stores at the pointer a itself (address a, not     *)
(* word_add a e), which WIDE_STORE_SPLIT_TAC does not split               *)
let RL_SPLIT_A_TAC (a:term) =
  let split name k =
    TRY(FIRST_X_ASSUM(fun th ->
      let c = concl th in
      try let l,_ = dest_eq c in
          let comp = rand(rator l) in
          let bytesf,addr = dest_comb(rand comp) in
          if fst(dest_const bytesf) = name && addr = a then
            STRIP_ASSUME_TAC(CONV_RULE(READ_MEMORY_SPLIT_CONV k) th)
          else NO_TAC
      with Failure _ -> NO_TAC)) in
  split "bytes128" 2 THEN split "bytes64" 1;;

let RL_VADD_TERM mc start stop =
  parse_term(Printf.sprintf
   "exists f_events.
      forall e a b (x:num->int32) (y:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size); (b,1024)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read X19 s = a /\\ read X20 s = b /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add b (word(4 * i))))
                             s = y i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = mld_poly_add x y i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a b pc /\\
                     memaccess_inbounds e2 [a,1024; b,1024] [a,1024]))
             (MAYCHANGE [PC] ,,
              MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18] ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,1024)])"
   mc start stop);;

let RL_VADD_PROVE mc exec start stop n =
  let tm = RL_VADD_TERM mc start stop in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (b:int64) (pc:num). f_ev_map a b pc :(uarch_event)list` THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  RL_VINPUT_TAC `a:int64` `x:num->int32` THEN
  RL_VINPUT_TAC `b:int64` `y:num->int32` THEN
  ARM_STEPS_TAC exec (1--n) THEN
  RL_SPLIT_A_TAC `a:int64` THEN
  WIDE_STORE_SPLIT_TAC `a:int64` 32 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[mld_poly_add] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[WORD_ADD_SYM];
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The test for an overlap of the polynomials that precedes the sum: the     *)
(* code takes the straight-line path if (with a at X19 = t, b at X20 and the *)
(* end of b + 1024 at X23)                                                   *)
(*   not (b < a + 1024 /\ a < b + 1024),                                    *)
(* as unsigned numbers modulo 2^64. If the ranges of t and mat (of 1024      *)
(* bytes) do not overlap modulo 2^64, the condition of the branch holds, also *)
(* if one of the ranges wraps around.                                        *)
(* ------------------------------------------------------------------------- *)

let RL_CONGK = prove
 (`!a b k n. a = b + k * n ==> (a == b) (mod n)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[CONG] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

let RL_SUBN1 = ARITH_RULE `!x nn. ~(x < nn) ==> x = 1 * nn + (x - nn)`;;
let RL_SUBN2 = ARITH_RULE `!x nn. ~(x < nn) /\ x < 2 * nn ==> x - nn < nn`;;

let RL_ALIAS_NUM = prove
 (`!tt mm nn. 1024 < nn /\ tt < nn /\ mm < nn /\
           (!i j. ~(i < 1024 /\ j < 1024 /\ (tt + i == mm + j) (mod nn)))
           ==> mm < (tt + 1024) MOD nn ==> mm + 1024 <= tt`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `tt + 1024 < nn` THENL
   [ASM_SIMP_TAC[MOD_LT] THEN DISCH_TAC THEN
    ASM_CASES_TAC `mm + 1024 <= tt` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `mm <= tt` THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `tt - mm`]) THEN
      MATCH_MP_TAC(TAUT `a ==> ~a ==> b`) THEN
      REPEAT CONJ_TAC THENL
       [ARITH_TAC; ASM_ARITH_TAC;
        MATCH_MP_TAC RL_CONGK THEN EXISTS_TAC `0` THEN ASM_ARITH_TAC];
      FIRST_X_ASSUM(MP_TAC o SPECL [`mm - tt`; `0`]) THEN
      MATCH_MP_TAC(TAUT `a ==> ~a ==> b`) THEN
      REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC; ARITH_TAC;
        MATCH_MP_TAC RL_CONGK THEN EXISTS_TAC `0` THEN ASM_ARITH_TAC]];
    SUBGOAL_THEN `(tt + 1024) MOD nn = (tt + 1024) - nn` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN CONJ_TAC THENL
       [MATCH_MP_TAC RL_SUBN1 THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC RL_SUBN2 THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_TAC THEN
    ASM_CASES_TAC `mm + 1024 <= tt` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(mm + nn) - tt`; `0`]) THEN
    MATCH_MP_TAC(TAUT `a ==> ~a ==> b`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC;
      MATCH_MP_TAC RL_CONGK THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC]]);;

let RL_ALIAS = prove
 (`!(t:int64) (mat:int64).
     nonoverlapping_modulo (2 EXP 64) (val t,1024) (val mat,1024)
     ==> (if val mat < val (word_add t (word 1024))
          then &(val t) - &(val (word_add mat (word 1024))):int =
               &(val (word_sub (t:int64) (word_add (mat:int64) (word 1024))))
          else true)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nonoverlapping_modulo; NOT_EXISTS_THM] THEN
  DISCH_THEN(LABEL_TAC "H") THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPEC `t:int64` VAL_BOUND) THEN MP_TAC(ISPEC `mat:int64` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64] THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(mat:int64) + 1024 <= val(t:int64)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`val(t:int64)`; `val(mat:int64)`; `2 EXP 64`] RL_ALIAS_NUM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `val(mat:int64) < val(word_add (t:int64) (word 1024))` THEN
    REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_ADD; VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;
