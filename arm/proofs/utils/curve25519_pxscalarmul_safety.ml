(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proof of the cores of                   *)
(* curve25519_pxscalarmul and curve25519_pxscalarmul_alt, which only       *)
(* differ in the field operations of the loop body.                        *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;

let CURVE25519_PXSCALARMUL_COUNTER_VAL = prove
 (`!i. i < 256 ==> val(word_sub (word 255) (word i):int64) = 255 - i`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word 255) (word i):int64 = word(255 - i)` SUBST1_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN COND_CASES_TAC THENL
     [REFL_TAC; POP_ASSUM MP_TAC THEN SIMPLE_ARITH_TAC]; ALL_TAC] THEN
  IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC);;

(* Close the non-trace conjuncts left after simulating a loop leg: the PC
   (lifting word over the loop-exit conditional) and the counter X21.       *)

let CURVE25519_PXSCALARMUL_PEEL_TAC =
  REPEAT(W(fun (asl,w) ->
    if is_conj w then
      CONJ_TAC THENL
       [FIRST[(GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN ASM_REWRITE_TAC[] THEN NO_TAC);
              CONV_TAC WORD_RULE];
        ALL_TAC]
    else NO_TAC));;

(* The safety proof of the core, given its code and decoding theorem, the  *)
(* PC of the end of the main loop and the number of steps of its body.     *)

let CURVE25519_PXSCALARMUL_SAFETY_TAC exec ~loop_end ~body =
  let pcoff off = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  CONCRETIZE_F_EVENTS_TAC
   `\(scalar:int64) (point:int64) (res:int64) (pc:num) (stackpointer:int64).
      APPEND (f_ev_post scalar point res pc stackpointer)
        (APPEND (ENUMERATEL 256 (f_ev_loop scalar point res pc stackpointer))
                (f_ev_pre scalar point res pc stackpointer))
      :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`res:int64`; `scalar:int64`; `point:int64`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + 0x4c` (pcoff loop_end)
   `\i s. read SP s = stackpointer /\ read X17 s = res /\ read X19 s = point /\
          read X20 s = scalar /\ read X21 s = word_sub (word 255) (word i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (* pre: pc + 0xc -> pc + 0x4c, 16 steps *)
    REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--16) THEN
    CURVE25519_PXSCALARMUL_PEEL_TAC THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (* loop body pc + 0x4c -> BCS before loop_end. The scalar word read is
       x[(255 - i) DIV 64]. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `val(word_sub (word 255) (word i):int64) = 255 - i` ASSUME_TAC THENL
     [ASM_SIMP_TAC[CURVE25519_PXSCALARMUL_COUNTER_VAL]; ALL_TAC] THEN
    SUBGOAL_THEN `(1 <= 255 - i <=> i + 1 < 256)` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(255 - i) DIV 64 < 4` ASSUME_TAC THENL
     [SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `word (8 * val (word_ushr (word_sub (word 255) (word i):int64) 6)):int64 =
      word (8 * ((255 - i) DIV 64))` ASSUME_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[VAL_WORD_USHR] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--body) THEN
    CURVE25519_PXSCALARMUL_PEEL_TAC THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (* post: loop exit loop_end -> loop_end + 0x88, 34 steps *)
    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--34) THEN
    CURVE25519_PXSCALARMUL_PEEL_TAC THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;
