(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proof of the cores of p256_montjscalarmul and      *)
(* p256_montjscalarmul_alt, which only differ in the field operations of the point    *)
(* operations they call.                                                     *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;

(* Simulate a call to the point addition or doubling at offset off, with code *)
(* sub_tmc, using the safety theorem registered under the label assump_name. *)

let P256_MONTJSCALARMUL_JADD_CALL_TAC (tmc,exec) (off,sub_tmc,_) (assump_name:string) (n:int) =
  let pcoff = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  REMOVE_THEN assump_name (fun safety_th ->
    let th =
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
        (REWRITE_RULE[bignum_triple_from_memory; bignum_pair_from_memory]
        safety_th) in
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (tmc,exec,off,sub_tmc,th)
        [`e:(uarch_event)list`; `read RDI s`; `read RSI s`;
        `read RDX s`;
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

let P256_MONTJSCALARMUL_JDOUBLE_CALL_TAC (tmc,exec) (off,sub_tmc,_) (assump_name:string) (n:int) =
  let pcoff = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  REMOVE_THEN assump_name (fun safety_th ->
    let th =
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
        (REWRITE_RULE[bignum_triple_from_memory; bignum_pair_from_memory]
        safety_th) in
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (tmc,exec,off,sub_tmc,th)
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
(* for the point addition and doubling, their offsets, code and prepared    *)
(* safety theorems.                                                         *)

let P256_MONTJSCALARMUL_SAFETY_TAC (tmc,exec) jadd jdouble =
  let jadd_tac = P256_MONTJSCALARMUL_JADD_CALL_TAC (tmc,exec) jadd
  and jdouble_tac = P256_MONTJSCALARMUL_JDOUBLE_CALL_TAC (tmc,exec) jdouble in
  (* Prepare the safety theorem of subroutine to be used! This is necessary to
     keep introduction of metavariable in the right order. *)
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = jadd in th)
      "H_JADD_SAFE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = jdouble in th)
      "H_JDOUBLE_SAFE" THEN

  CONCRETIZE_F_EVENTS_TAC
    `\(scalar:int64) (point:int64) (res:int64) (pc:num) (stackpointer:int64).
      APPEND
        (f_ev_loop_post scalar point res pc stackpointer)
        (APPEND
          (ENUMERATEL 63 (f_ev_loop scalar point res pc stackpointer))
            (f_ev_loop_pre scalar point res pc stackpointer))
      :(uarch_event) list` THEN

  REPEAT META_EXISTS_TAC THEN
  STRIP_TAC (* event e *) THEN

  REWRITE_TAC[GSYM SEQ_ASSOC; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS] THEN
  ENSURES_EXISTING_PRESERVED_TAC `RSP` THEN

  (*** Main loop invariant setup. ***)
  ENSURES_EVENTS_WHILE_UP2_TAC `63` `pc + 0x62d`
    `pc + 0xaf8`(*after jne*)
    `\i s.
      read RSP s = word_add stackpointer (word 296) /\
      read (memory :> bytes64(word_add stackpointer (word 1288))) s = res /\
      read RBP s = word (4 * (63 - i))` THEN
  REPEAT CONJ_TAC THENL [
    ARITH_TAC;

    (*** Initial holding of invariant ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC exec (1--85) THEN
    jdouble_tac "H_JDOUBLE_SAFE" 86 THEN
    X86_STEPS_TAC exec (87--90) THEN
    jadd_tac "H_JADD_SAFE" 91 THEN
    X86_STEPS_TAC exec (92--94) THEN
    jdouble_tac "H_JDOUBLE_SAFE" 95 THEN
    X86_STEPS_TAC exec (96--99) THEN
    jadd_tac "H_JADD_SAFE" 100 THEN
    X86_STEPS_TAC exec (101--103) THEN
    jdouble_tac "H_JDOUBLE_SAFE" 104 THEN
    X86_STEPS_TAC exec (105--108) THEN
    jadd_tac "H_JADD_SAFE" 109 THEN
    X86_STEPS_TAC exec (110--112) THEN
    jdouble_tac "H_JDOUBLE_SAFE" 113 THEN
    X86_STEPS_TAC exec (114--115) THEN
    X86_STEPS_TAC exec (116--244) THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[SUB_0] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** Defer the main invariant preservation proof till below ***)

    ALL_TAC;

    (*** Final copying to the output and specializing invariant ***)

    REWRITE_TAC[] THEN
    ENSURES_INIT_TAC "s0" THEN
    STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC exec (1--25) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC
  ] THEN

  (**** Preservation of the loop invariant ***)

  REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN

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
  X86_STEPS_TAC exec (18--27) THEN
  X86_STEPS_TAC exec (28--143) THEN
  X86_STEPS_TAC exec (144--175) THEN
  X86_STEPS_TAC exec (176--179) THEN
  jadd_tac "H_JADD_SAFE" 180 THEN
  X86_STEPS_TAC exec (181--182) THEN

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

  (* Found this pattern from safety_print_log := true *)
  SUBGOAL_THEN
    `word (8 * val (word_ushr (word_sub (word (4 * (63 - i))) (word 4):int64) 6))
     :int64 = word (8 * (4 * (62 - i)) DIV 2 EXP 6)`
  SUBST_ALL_TAC THENL [
    IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL [
      ALL_TAC; SIMPLE_ARITH_TAC
    ] THEN
    AP_TERM_TAC THEN REWRITE_TAC[VAL_WORD_USHR] THEN
    IMP_REWRITE_TAC[VAL_WORD;MOD_LT;DIMINDEX_64] THEN CONJ_TAC THENL [
      BINOP_TAC THENL [REFL_TAC;ALL_TAC] THEN
      BINOP_TAC THENL [SIMPLE_ARITH_TAC; REFL_TAC];

      SIMPLE_ARITH_TAC
    ];

    ALL_TAC
  ] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;
