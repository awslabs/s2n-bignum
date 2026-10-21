(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proof of the cores of                   *)
(* p256_scalarmulbase and p256_scalarmulbase_alt, which have the same      *)
(* structure: the _alt version calls the _alt field operations, at         *)
(* different offsets.                                                      *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;

(* Simulate a call to one of the local subroutines (at offset off, with    *)
(* code sub_tmc), using the safety theorem registered under the label      *)
(* assump_name.                                                            *)

let P256_SCALARMULBASE_CALL_TAC (tmc,exec) (off,sub_tmc,_) args assump_name n =
  let pcoff = mk_binary "+" (`pc:num`,mk_small_numeral off) in
  let args' = `e:(uarch_event)list`::
    map (fun t -> if t = `pc:num` then pcoff else t) args in
  REMOVE_THEN assump_name (fun safety_th ->
    let th = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) safety_th in
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (tmc,exec,off,sub_tmc,th)
        args' n THENL [
      EXISTS_E2_TAC(ref
        [`scalar:int64`;`blocksize:int64`;`tab:int64`;`len:num`;`res:int64`;
         `pc:num`;`stackpointer:int64`;`i:num`;
         `f_ev_pre:int64->int64->int64->num->int64->num->int64->(uarch_event)list`;
         `f_ev_inpre:int64->int64->int64->num->int64->num->int64->num->
                     (uarch_event)list`;
         `f_ev_tab:int64->int64->int64->num->int64->num->int64->num->num->
                   (uarch_event)list`;
         `f_ev_inpost:int64->int64->int64->num->int64->num->int64->num->
                      (uarch_event)list`]);
      LABEL_TAC assump_name safety_th
    ]);;

let P256_SCALARMULBASE_ARGS3 =
  [`read RDI s`; `read RSI s`; `read RDX s`; `pc:num`; `read RSP s`;
   `read (memory :> bytes64(read RSP s)) s`];;

let P256_SCALARMULBASE_ARGS2 =
  [`read RDI s`; `read RSI s`; `pc:num`; `read RSP s`;
   `read (memory :> bytes64(read RSP s)) s`];;

(* The loop over a block runs 2^(blocksize-1) times, computed as a shift of  *)
(* 1 by the low byte of blocksize - 1.                                       *)

let P256_SCALARMULBASE_TABSIZE_LEMMA = prove
 (`!b:int64. 2 <= val b /\ val b <= 31
     ==> word_shl (word 1)
          (val (word (val (word_sub b (word 1)) MOD 256):byte) MOD 64):int64 =
         word (2 EXP (val b - 1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val (word_sub (b:int64) (word 1)) = val b - 1` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1; DIMINDEX_64] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= b ==> 1 <= b`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(val (b:int64) - 1) MOD 256 = val b - 1` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (val (b:int64) - 1):byte) = val b - 1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_8] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(val (b:int64) - 1) MOD 64 = val b - 1` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_SHL_WORD; MULT_CLAUSES]);;

(* The test closing the main loop: (i + 1) * blocksize < 257.               *)

let P256_SCALARMULBASE_LOOPTEST_LEMMA = prove
 (`!b:int64 i. 2 <= val b /\ val b <= 31 /\ i < 256 DIV val b + 1
     ==> (val (word_mul (word (i + 1)) b:int64) < 257 <=>
          i + 1 < 256 DIV val b + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `256 DIV val (b:int64) + 1 <= 129` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `n <= 128 ==> n + 1 <= 129`) THEN
    TRANS_TAC LE_TRANS `256 DIV 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIV_MONO2 THEN ASM_REWRITE_TAC[ARITH_EQ];
      CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word_mul (word (i + 1)) b:int64) = (i + 1) * val b`
  SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_MUL; DIMINDEX_64] THEN
    SUBGOAL_THEN `val (word (i + 1):int64) = i + 1` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MOD_LT THEN
    TRANS_TAC LET_TRANS `129 * 31` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `n < 257 <=> n <= 256`;
              ARITH_RULE `a < b + 1 <=> a <= b`] THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `2 <= b ==> ~(b = 0)`] THEN
  REWRITE_TAC[MULT_SYM]);;

(* Regroup the events of one iteration of the main loop for the inner loop. *)

let P256_SCALARMULBASE_REASSOC = METIS[APPEND_ASSOC]
 `(exists e2. P e2 /\ e2 = APPEND (APPEND (APPEND (APPEND a b) c) d) f /\
              Q e2) <=>
  (exists e2. P e2 /\ e2 = APPEND (APPEND a (APPEND b c)) (APPEND d f) /\
              Q e2)`;;

(* The memory-safety reasoning about table offsets wants assumptions free   *)
(* of "val", so abbreviate the block size after the trace is unified.        *)

let P256_SCALARMULBASE_DISCHARGE_TAC =
  GEN_DISCHARGE_SAFETY_PROPERTY_TAC (ABBREV_TAC `bsv = val (blocksize:int64)`);;

(* The safety proof of the core, given its code and decoding theorem and,  *)
(* for each local subroutine, its offset, code and safety theorem.         *)

let P256_SCALARMULBASE_SAFETY_TAC (tmc,exec) jmixadd mul sqr demont inv =
  let call_tac = P256_SCALARMULBASE_CALL_TAC (tmc,exec) in
  let jmixadd_tac = call_tac jmixadd P256_SCALARMULBASE_ARGS3 "H_JMIXADD_SAFE"
  and mul_tac = call_tac mul P256_SCALARMULBASE_ARGS3 "H_MUL_SAFE"
  and sqr_tac = call_tac sqr P256_SCALARMULBASE_ARGS2 "H_SQR_SAFE"
  and demont_tac = call_tac demont P256_SCALARMULBASE_ARGS2 "H_DEMONT_SAFE"
  and inv_tac = call_tac inv P256_SCALARMULBASE_ARGS2 "H_INV_SAFE" in
  (* Prepare the safety theorems of the subroutines to be used. This is
     necessary to keep introduction of metavariables in the right order. *)
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = demont in th)
      "H_DEMONT_SAFE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = inv in th)
      "H_INV_SAFE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = mul in th)
      "H_MUL_SAFE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = sqr in th)
      "H_SQR_SAFE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = jmixadd in th)
      "H_JMIXADD_SAFE" THEN

  CONCRETIZE_F_EVENTS_TAC
   `\(scalar:int64) (blocksize:int64) (tab:int64) (len:num) (res:int64)
     (pc:num) (stackpointer:int64).
      APPEND (f_ev_post scalar blocksize tab len res pc stackpointer)
       (APPEND
         (ENUMERATEL (256 DIV val blocksize + 1)
           (\i. APPEND
                 (APPEND (f_ev_inpost scalar blocksize tab len res pc stackpointer i)
                   (ENUMERATEL (2 EXP (val blocksize - 1))
                      (f_ev_tab scalar blocksize tab len res pc stackpointer i)))
                 (f_ev_inpre scalar blocksize tab len res pc stackpointer i)))
         (f_ev_pre scalar blocksize tab len res pc stackpointer))
      :(uarch_event) list` THEN

  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM SEQ_ASSOC; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL] THEN
  MAP_EVERY X_GEN_TAC
   [`res:int64`; `scalar:int64`; `blocksize:int64`; `tab:int64`; `len:num`;
    `pc:num`; `stackpointer:int64`] THEN
  STRIP_TAC THEN REWRITE_TAC[C_ARGUMENTS] THEN
  ENSURES_EXISTING_PRESERVED_TAC `RSP` THEN
  SUBGOAL_THEN `256 DIV val (blocksize:int64) + 1 <= 129` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `n <= 128 ==> n + 1 <= 129`) THEN
    TRANS_TAC LE_TRANS `256 DIV 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIV_MONO2 THEN ASM_REWRITE_TAC[ARITH_EQ];
      CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN

  (*** Main loop, one iteration per window of the scalar ***)

  ENSURES_EVENTS_WHILE_UP2_TAC `256 DIV val (blocksize:int64) + 1`
   `pc + 0xdd` `pc + 0x38c`
   `\i s. read RSP s = word_add stackpointer (word 296) /\
          read (memory :> bytes64(word_add stackpointer (word 584))) s = res /\
          read (memory :> bytes64(word_add stackpointer (word 592))) s =
          blocksize /\
          read (memory :> bytes64(word_add stackpointer (word 600))) s =
          word_add tab (word (64 * (2 EXP (val blocksize - 1) * i))) /\
          read (memory :> bytes64(word_add stackpointer (word 608))) s =
          (word i:int64)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Reduction and copying of the scalar, zeroing of the accumulator ***)

    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; ENUMERATEL_APPEND_ZERO] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC exec (1--38) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** Defer the main loop body till below ***)

    ALL_TAC;

    (*** Final conversion to affine coordinates ***)

    REWRITE_TAC[] THEN
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC exec (1--3) THEN
    sqr_tac 4 THEN
    X86_STEPS_TAC exec (5--8) THEN
    mul_tac 9 THEN
    X86_STEPS_TAC exec (10--12) THEN
    demont_tac 13 THEN
    X86_STEPS_TAC exec (14--16) THEN
    inv_tac 17 THEN
    X86_STEPS_TAC exec (18--21) THEN
    mul_tac 22 THEN
    X86_STEPS_TAC exec (23--27) THEN
    mul_tac 28 THEN
    X86_STEPS_TAC exec (29--32) THEN
    mul_tac 33 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  (*** The main loop body: a constant-time scan of the table block ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `64 * 2 EXP (val (blocksize:int64) - 1) * (i + 1) <= len`
  ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS
     `(256 DIV val (blocksize:int64) + 1) * 2 EXP (val blocksize - 1) * 64` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `64 * b * (i + 1) = (i + 1) * b * 64`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ENUMERATEL_ADD1] THEN
  ONCE_REWRITE_TAC[P256_SCALARMULBASE_REASSOC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `2 EXP (val (blocksize:int64) - 1)`
   `pc + 0x1a0` `pc + 0x1d5`
   `\t s. read RSP s = word_add stackpointer (word 296) /\
          read (memory :> bytes64(word_add stackpointer (word 584))) s = res /\
          read (memory :> bytes64(word_add stackpointer (word 592))) s =
          blocksize /\
          read RBP s = word_add tab
            (word (64 * (2 EXP (val blocksize - 1) * i + t))) /\
          read (memory :> bytes64(word_add stackpointer (word 608))) s =
          (word i:int64) /\
          read RSI s = (word (2 EXP (val blocksize - 1) - t):int64)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXP_EQ_0; ARITH_EQ];

    (*** Extraction of the window, up to the table scan ***)

    REWRITE_TAC[ADD_CLAUSES; SUB_0; ENUMERATEL_APPEND_ZERO] THEN
    MP_TAC(SPEC `blocksize:int64` P256_SCALARMULBASE_TABSIZE_LEMMA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC exec (1--37) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** One table entry, kept or not by conditional moves ***)

    X_GEN_TAC `t:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `64 * (2 EXP (val (blocksize:int64) - 1) * i + t) + 64 <= len`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th ->
        concl th = `64 * 2 EXP (val (blocksize:int64) - 1) * (i + 1) <= len`)) THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `word_sub (word (2 EXP (val (blocksize:int64) - 1) - t)) (word 1):int64 =
      word (2 EXP (val blocksize - 1) - (t + 1))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `2 EXP (val (blocksize:int64) - 1) - t =
        (2 EXP (val blocksize - 1) - (t + 1)) + 1`
      SUBST1_TAC THENL [ASM_ARITH_TAC; CONV_TAC WORD_RULE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(~(val (word (2 EXP (val (blocksize:int64) - 1) - (t + 1)):int64) = 0) <=>
       t + 1 < 2 EXP (val blocksize - 1))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `val (word (2 EXP (val (blocksize:int64) - 1) - (t + 1)):int64) =
        2 EXP (val blocksize - 1) - (t + 1)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        TRANS_TAC LET_TRANS `2 EXP (val (blocksize:int64) - 1)` THEN
        REWRITE_TAC[ARITH_RULE `a - b <= a`; LT_EXP] THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC exec (1--12) THEN
    SAFETY_REWRITE_READS_TAC ["RBP"]
     [WORD_RULE `word_add (word_add (tab:int64) (word (64 * (k + t)))) (word 64) =
                 word_add tab (word (64 * (k + (t + 1))))`] THEN
    SAFETY_REWRITE_READS_TAC ["RIP"]
     [SAFETY_COND_WORD_LIFT] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    P256_SCALARMULBASE_DISCHARGE_TAC;

    (*** Conditional negation, mixed addition and selection of the result ***)

    REWRITE_TAC[ARITH_RULE `b * i + b = b * (i + 1)`] THEN
    SUBGOAL_THEN `word_add (word i) (word 1):int64 = word (i + 1)` ASSUME_TAC
    THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    MP_TAC(SPECL [`blocksize:int64`; `i:num`] P256_SCALARMULBASE_LOOPTEST_LEMMA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC exec (1--28) THEN
    jmixadd_tac 29 THEN
    X86_STEPS_TAC exec (30--73) THEN
    SAFETY_REWRITE_READS_TAC ["RIP"]
     [SAFETY_COND_WORD_LIFT] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    P256_SCALARMULBASE_DISCHARGE_TAC];;
