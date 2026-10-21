(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proof of the cores of p256_scalarmul    *)
(* and p256_scalarmul_alt, which have the same structure: the _alt version *)
(* calls the _alt field operations, at different offsets.                  *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;

(* Simulate a call to one of the local subroutines (at offset off, with    *)
(* code sub_tmc), using the safety theorem registered under the label      *)
(* assump_name.                                                            *)

let P256_SCALARMUL_CALL_TAC (tmc,exec) (off,sub_tmc,_) args assump_name n =
  let pcoff = mk_binary "+" (`pc:num`,mk_small_numeral off) in
  let args' = `e:(uarch_event)list`::
    map (fun t -> if t = `pc:num` then pcoff else t) args in
  REMOVE_THEN assump_name (fun safety_th ->
    let th =
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
        (REWRITE_RULE[bignum_triple_from_memory; bignum_pair_from_memory]
        safety_th) in
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (tmc,exec,off,sub_tmc,th)
        args' n THENL [
      EXISTS_E2_TAC(ref
        [`scalar:int64`;`point:int64`;`res:int64`;`pc:num`;`stackpointer:int64`;
         `i:num`;
         `f_ev_loop:int64->int64->int64->num->int64->num->(uarch_event)list`]);
      LABEL_TAC assump_name safety_th
    ]);;

let P256_SCALARMUL_ARGS3 =
  [`read RDI s`; `read RSI s`; `read RDX s`; `pc:num`; `read RSP s`;
   `read (memory :> bytes64(read RSP s)) s`];;

let P256_SCALARMUL_ARGS2 =
  [`read RDI s`; `read RSI s`; `pc:num`; `read RSP s`;
   `read (memory :> bytes64(read RSP s)) s`];;

(* The safety proof of the core, given its code and decoding theorem and,  *)
(* for each local subroutine, its offset, code and safety theorem.         *)

let P256_SCALARMUL_SAFETY_TAC (tmc,exec)
    jadd jdouble jmixadd tomont mul sqr demont inv =
  let call_tac = P256_SCALARMUL_CALL_TAC (tmc,exec) in
  let jadd_tac = call_tac jadd P256_SCALARMUL_ARGS3 "H_JADD_SAFE"
  and jdouble_tac = call_tac jdouble P256_SCALARMUL_ARGS2 "H_JDOUBLE_SAFE"
  and jmixadd_tac = call_tac jmixadd P256_SCALARMUL_ARGS3 "H_JMIXADD_SAFE"
  and tomont_tac = call_tac tomont P256_SCALARMUL_ARGS2 "H_TOMONT_SAFE"
  and mul_tac = call_tac mul P256_SCALARMUL_ARGS3 "H_MUL_SAFE"
  and sqr_tac = call_tac sqr P256_SCALARMUL_ARGS2 "H_SQR_SAFE"
  and demont_tac = call_tac demont P256_SCALARMUL_ARGS2 "H_DEMONT_SAFE"
  and inv_tac = call_tac inv P256_SCALARMUL_ARGS2 "H_INV_SAFE" in
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
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = tomont in th)
      "H_TOMONT_SAFE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = jadd in th)
      "H_JADD_SAFE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = jdouble in th)
      "H_JDOUBLE_SAFE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = jmixadd in th)
      "H_JMIXADD_SAFE" THEN

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
  ENSURES_EVENTS_WHILE_UP2_TAC `63` `pc + 0x629`
    `pc + 0xae1`(*after jne*)
    `\i s.
      read RSP s = word_add stackpointer (word 296) /\
      read (memory :> bytes64(word_add stackpointer (word 1288))) s = res /\
      read RBP s = word (4 * (63 - i))` THEN
  REPEAT CONJ_TAC THENL [
    ARITH_TAC;

    (*** Initial holding of invariant ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC exec (1--41) THEN
    tomont_tac 42 THEN
    X86_STEPS_TAC exec (43--45) THEN
    tomont_tac 46 THEN
    X86_STEPS_TAC exec (47--79) THEN
    jdouble_tac 80 THEN
    X86_STEPS_TAC exec (81--84) THEN
    jmixadd_tac 85 THEN
    X86_STEPS_TAC exec (86--88) THEN
    jdouble_tac 89 THEN
    X86_STEPS_TAC exec (90--93) THEN
    jmixadd_tac 94 THEN
    X86_STEPS_TAC exec (95--97) THEN
    jdouble_tac 98 THEN
    X86_STEPS_TAC exec (99--102) THEN
    jmixadd_tac 103 THEN
    X86_STEPS_TAC exec (104--106) THEN
    jdouble_tac 107 THEN
    X86_STEPS_TAC exec (108--238) THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[SUB_0] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** Defer the main invariant preservation proof till below ***)

    ALL_TAC;

    (*** Final conversion to affine form and copying to the output ***)

    REWRITE_TAC[] THEN
    ENSURES_INIT_TAC "s0" THEN
    STRIP_EXISTS_ASSUM_TAC THEN
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
    DISCHARGE_SAFETY_PROPERTY_TAC
  ] THEN

  (**** Preservation of the loop invariant ***)

  REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN

  ENSURES_INIT_TAC "s0" THEN
  STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC exec (1--4) THEN
  jdouble_tac 5 THEN
  X86_STEPS_TAC exec (6--8) THEN
  jdouble_tac 9 THEN
  X86_STEPS_TAC exec (10--12) THEN
  jdouble_tac 13 THEN
  X86_STEPS_TAC exec (14--16) THEN
  jdouble_tac 17 THEN
  X86_STEPS_TAC exec (18--173) THEN
  jadd_tac 174 THEN
  X86_STEPS_TAC exec (175--176) THEN

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
