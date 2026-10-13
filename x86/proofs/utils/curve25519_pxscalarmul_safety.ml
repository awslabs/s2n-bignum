(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proof of the cores of                   *)
(* curve25519_pxscalarmul and curve25519_pxscalarmul_alt, which only       *)
(* differ in the field operations of the loop body.                        *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;

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

  (*** The ladder loop, 256 iterations with the counter in a stack slot ***)

  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + 0xbd` (pcoff loop_end)
   `\i s. read RSP s = stackpointer /\
          read (memory :> bytes64 (word_add stackpointer (word 320))) s = res /\
          read (memory :> bytes64 (word_add stackpointer (word 328))) s = point /\
          read (memory :> bytes64 (word_add stackpointer (word 336))) s = scalar /\
          read (memory :> bytes64 (word_add stackpointer (word 344))) s =
          word_sub (word 255) (word i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The initialization up to the loop head ***)

    REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--28) THEN
    SAFETY_CLOSE_TAC;

    (*** The loop body; the scalar word read is scalar[(255 - i) DIV 64] ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `val(word_sub (word 255) (word i):int64) = 255 - i` ASSUME_TAC THENL
     [SUBGOAL_THEN `word_sub (word 255) (word i):int64 = word(255 - i)`
      SUBST1_TAC THENL
       [IMP_REWRITE_TAC[WORD_SUB2] THEN UNDISCH_TAC `i < 256` THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        UNDISCH_TAC `i < 256` THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(1 <= 255 - i <=> i + 1 < 256) /\ (255 - i < 1 <=> ~(i + 1 < 256)) /\
      (255 - i) DIV 64 < 4`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `i < 256` THEN ARITH_TAC;
        UNDISCH_TAC `i < 256` THEN ARITH_TAC;
        SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN UNDISCH_TAC `i < 256` THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `word (8 * val (word_ushr (word_sub (word 255) (word i):int64) 6)):int64 =
      word (8 * ((255 - i) DIV 64))` ASSUME_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[VAL_WORD_USHR] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--body) THEN
    SAFETY_CLOSE_TAC;

    (*** The final reconstruction and output ***)

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--45) THEN
    SAFETY_CLOSE_TAC];;
