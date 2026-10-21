(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proof of the cores of                   *)
(* p384_montjscalarmul and p384_montjscalarmul_alt, which only differ in   *)
(* the field operations of the point operations they call.                 *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;

(* Simulate a call to the point addition or doubling at offset off, with   *)
(* code sub_tmc, using the safety theorem registered under the label       *)
(* assump_name.                                                            *)

let P384_MONTJSCALARMUL_JADD_CALL_TAC (tmc,exec) (off,sub_tmc,_)
    (assump_name:string) (n:int) =
  let pcoff = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (tmc,exec,
          off,sub_tmc,safety_th)
        [`e:(uarch_event)list`;`read RDI s`; `read RSI s`; `read RDX s`;
        pcoff; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
        n THENL [
      EXISTS_E2_TAC(ref
        [`scalar:int64`;`point:int64`;`res:int64`;`pc:num`;
         `stackpointer:int64`;
         (* inside the loop... *)
         `i:num`;
         `f_ev_loop:int64->int64->int64->num->int64->num->(uarch_event)list`]);

      LABEL_TAC assump_name safety_th
    ]);;

let P384_MONTJSCALARMUL_JDOUBLE_CALL_TAC (tmc,exec) (off,sub_tmc,_)
    (assump_name:string) (n:int) =
  let pcoff = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (tmc,exec,
          off,sub_tmc,safety_th)
        [`e:(uarch_event)list`; `read RDI s`; `read RSI s`;
        pcoff; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
              n THENL [
      EXISTS_E2_TAC(ref
        [`scalar:int64`;`point:int64`;`res:int64`;`pc:num`;
         `stackpointer:int64`;
         (* inside the loop... *)
         `i:num`;
         `f_ev_loop:int64->int64->int64->num->int64->num->(uarch_event)list`]);

      LABEL_TAC assump_name safety_th
    ]);;

(* The safety proof of the core, given its code and decoding theorem and,  *)
(* for the point addition and doubling, their offsets, code and prepared   *)
(* safety theorems.                                                        *)

let P384_MONTJSCALARMUL_SAFETY_TAC (tmc,exec) jadd jdouble =
  let jadd_tac = P384_MONTJSCALARMUL_JADD_CALL_TAC (tmc,exec) jadd
  and jdouble_tac = P384_MONTJSCALARMUL_JDOUBLE_CALL_TAC (tmc,exec) jdouble
  and prep (_,_,th) =
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (REWRITE_RULE[bignum_triple_from_memory; bignum_pair_from_memory] th) in
  (* Prepare the safety theorem of subroutine to be used! This is necessary to
     keep introduction of metavariable in the right order. *)
  ASSUME_CALLEE_SAFETY_TAILED_TAC (prep jadd) "H_JADD_SAFE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (prep jdouble) "H_JDOUBLE_SAFE" THEN

  CONCRETIZE_F_EVENTS_TAC
    `\(scalar:int64) (point:int64) (res:int64) (pc:num) (stackpointer:int64).
      APPEND
        (f_ev_loop_post scalar point res pc stackpointer)
        (APPEND
          (ENUMERATEL 76 (f_ev_loop scalar point res pc stackpointer))
            (f_ev_loop_pre scalar point res pc stackpointer))
      :(uarch_event) list` THEN

  REPEAT META_EXISTS_TAC THEN
  STRIP_TAC (* event e *) THEN

  REWRITE_TAC[GSYM SEQ_ASSOC; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst exec] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS] THEN
  ENSURES_EXISTING_PRESERVED_TAC `RSP` THEN

  (*** Main loop invariant setup. ***)

  ENSURES_EVENTS_WHILE_UP2_TAC `76` `pc + 0xec6` `pc + 0x1b61`
   `\i s.
      read RSP s = word_add stackpointer (word 408) /\
      read (memory :> bytes64(word_add stackpointer (word 3048))) s = res /\
      read RBP s = word (5 * (76 - i))` THEN
  REPEAT CONJ_TAC THENL [
    ARITH_TAC;

    (*** Initial holding of invariant ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC exec (1--68) THEN
    jdouble_tac "H_JDOUBLE_SAFE" 69 THEN
    X86_STEPS_TAC exec (70--73) THEN
    jadd_tac "H_JADD_SAFE" 74 THEN
    X86_STEPS_TAC exec (75--77) THEN
    jdouble_tac "H_JDOUBLE_SAFE" 78 THEN
    X86_STEPS_TAC exec (79--82) THEN
    jadd_tac "H_JADD_SAFE" 83 THEN
    X86_STEPS_TAC exec (84--86) THEN
    jdouble_tac "H_JDOUBLE_SAFE" 87 THEN
    X86_STEPS_TAC exec (88--91) THEN
    jadd_tac "H_JADD_SAFE" 92 THEN
    X86_STEPS_TAC exec (93--95) THEN
    jdouble_tac "H_JDOUBLE_SAFE" 96 THEN
    X86_STEPS_TAC exec (97--100) THEN
    jadd_tac "H_JADD_SAFE" 101 THEN
    X86_STEPS_TAC exec (102--104) THEN
    jdouble_tac "H_JDOUBLE_SAFE" 105 THEN
    X86_STEPS_TAC exec (106--109) THEN
    jadd_tac "H_JADD_SAFE" 110 THEN
    X86_STEPS_TAC exec (111--113) THEN
    jdouble_tac "H_JDOUBLE_SAFE" 114 THEN
    X86_STEPS_TAC exec (115--118) THEN
    jadd_tac "H_JADD_SAFE" 119 THEN
    X86_STEPS_TAC exec (120--122) THEN
    jdouble_tac "H_JDOUBLE_SAFE" 123 THEN
    X86_STEPS_TAC exec (124--127) THEN
    jadd_tac "H_JADD_SAFE" 128 THEN
    X86_STEPS_TAC exec (129--131) THEN
    jdouble_tac "H_JDOUBLE_SAFE" 132 THEN
    X86_STEPS_TAC exec (133--522) THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[SUB_0] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** Defer the main invariant preservation proof till below ***)

    ALL_TAC;

    (*** Final copying to the output and specializing invariant ***)

    REWRITE_TAC[] THEN
    ENSURES_INIT_TAC "s0" THEN
    STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC exec (1--37) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC
  ] THEN

  (**** Now the preservation of the loop invariant ***)

  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC exec (1--4) THEN
  jdouble_tac "H_JDOUBLE_SAFE" 5 THEN
  X86_STEPS_TAC exec (6--8) THEN
  jdouble_tac "H_JDOUBLE_SAFE" 9 THEN
  X86_STEPS_TAC exec (10--12) THEN
  jdouble_tac "H_JDOUBLE_SAFE" 13 THEN
  X86_STEPS_TAC exec (14--16) THEN
  jdouble_tac "H_JDOUBLE_SAFE" 17 THEN
  X86_STEPS_TAC exec (18--20) THEN
  jdouble_tac "H_JDOUBLE_SAFE" 21 THEN
  X86_STEPS_TAC exec (22--45) THEN
  X86_STEPS_TAC exec (46--434) THEN
  jadd_tac "H_JADD_SAFE" 435 THEN
  X86_STEPS_TAC exec (436--437) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    IMP_REWRITE_TAC[VAL_WORD_EQ;DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC
  ] THEN
  CONJ_TAC THENL [
    IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL [
      AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC
    ];
    ALL_TAC
  ] THEN

  DISCHARGE_SAFETY_PROPERTY_TAC;;
