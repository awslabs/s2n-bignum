(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proof of the cores of p256_scalarmul    *)
(* and p256_scalarmul_alt, which have the same structure: the _alt version *)
(* calls the _alt field and point operations, at different offsets.        *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;

(* Simulate a call to one of the local subroutines at offset off, using the  *)
(* safety theorem registered under the label assump_name, transformed by     *)
(* rule: as in the correctness proof, the theorems of the point operations   *)
(* are normalized and those of the field operations are used as they are.    *)

let P256_SCALARMUL_CALL_TAC (mc,exec) rule (off,sub_mc,_) args assump_name n =
  let pcoff = mk_binary "+" (`pc:num`,mk_small_numeral off) in
  let args' = `e:(uarch_event)list`::
    map (fun t -> if t = `pc:num` then pcoff else t) args in
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (mc,exec,off,sub_mc,rule safety_th)
        args' n THENL [
      EXISTS_E2_TAC(ref
        [`scalar:int64`;`point:int64`;`res:int64`;`pc:num`;
         `stackpointer:int64`;`i:num`;
         `f_ev_loop:int64->int64->int64->num->int64->num->(uarch_event)list`]);
      LABEL_TAC assump_name safety_th
    ]);;

let P256_SCALARMUL_POINT_RULE =
  (CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
   REWRITE_RULE[bignum_triple_from_memory; bignum_pair_from_memory]);;

(* The safety proof of the core, given its code and decoding theorem; for  *)
(* each local subroutine, its offset, code and safety theorem; and the     *)
(* offset of the stack pointer in the main loop.                           *)

let P256_SCALARMUL_SAFETY_TAC (mc,exec)
    jadd jdouble jmixadd tomont mul sqr demont inv ~frame =
  let point_tac = P256_SCALARMUL_CALL_TAC (mc,exec) P256_SCALARMUL_POINT_RULE
  and field_tac = P256_SCALARMUL_CALL_TAC (mc,exec) I in
  let jadd_tac = point_tac jadd
    [`read X0 s`; `read X1 s`; `read X2 s`; `pc:num`; `read SP s`; `read X30 s`]
    "H_JADD_SAFE"
  and jdouble_tac = point_tac jdouble
    [`read X0 s`; `read X1 s`; `pc:num`; `read SP s`; `read X30 s`]
    "H_JDOUBLE_SAFE"
  and jmixadd_tac = point_tac jmixadd
    [`read X0 s`; `read X1 s`; `read X2 s`; `pc:num`; `read SP s`; `read X30 s`]
    "H_JMIXADD_SAFE"
  and tomont_tac = field_tac tomont
    [`read X0 s`; `read X1 s`; `pc:num`; `read X30 s`]
    "H_TOMONT_SAFE"
  and mul_tac = field_tac mul
    [`read X0 s`; `read X1 s`; `read X2 s`; `pc:num`; `read X30 s`]
    "H_MUL_SAFE"
  and sqr_tac = field_tac sqr
    [`read X0 s`; `read X1 s`; `pc:num`; `read X30 s`]
    "H_SQR_SAFE"
  and demont_tac = field_tac demont
    [`read X0 s`; `read X1 s`; `pc:num`; `read X30 s`]
    "H_DEMONT_SAFE"
  and inv_tac = field_tac inv
    [`read X0 s`; `read X1 s`; `pc:num`; `read SP s`; `read X30 s`]
    "H_INV_SAFE" in
  (* Prepare the safety theorems of the subroutines to be used. This is
     necessary to keep introduction of metavariables in the right order. *)
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = jadd in th)
      "H_JADD_SAFE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = jdouble in th)
      "H_JDOUBLE_SAFE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = jmixadd in th)
      "H_JMIXADD_SAFE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = tomont in th)
      "H_TOMONT_SAFE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = mul in th)
      "H_MUL_SAFE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = sqr in th)
      "H_SQR_SAFE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = demont in th)
      "H_DEMONT_SAFE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (let _,_,th = inv in th)
      "H_INV_SAFE" THEN

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

  (*** Main loop invariant setup. ***)

  ENSURES_EVENTS_WHILE_UP2_TAC `63` `pc + 0x454` `pc + 0x7b4`
   (vsubst [mk_small_numeral frame,`frame:num`]
    `\i s.
       read SP s = word_add stackpointer (word frame) /\
       read X19 s = res /\
       read X20 s = word (4 * (63 - i))`) THEN
  REPEAT CONJ_TAC THENL [
    ARITH_TAC;

    (*** Initial conversions and tabulation of multiples ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC exec (1--43) THEN
    tomont_tac 44 THEN
    ARM_STEPS_TAC exec (45--47) THEN
    tomont_tac 48 THEN
    ARM_STEPS_TAC exec (49--73) THEN
    jdouble_tac 74 THEN
    ARM_STEPS_TAC exec (75--78) THEN
    jmixadd_tac 79 THEN
    ARM_STEPS_TAC exec (80--82) THEN
    jdouble_tac 83 THEN
    ARM_STEPS_TAC exec (84--87) THEN
    jmixadd_tac 88 THEN
    ARM_STEPS_TAC exec (89--91) THEN
    jdouble_tac 92 THEN
    ARM_STEPS_TAC exec (93--96) THEN
    jmixadd_tac 97 THEN
    ARM_STEPS_TAC exec (98--100) THEN
    jdouble_tac 101 THEN
    ARM_STEPS_TAC exec (102--283) THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[SUB_0] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** Defer the main invariant preservation proof till below ***)

    ALL_TAC;

    (*** Final conversion to affine coordinates ***)

    REWRITE_TAC[] THEN
    ENSURES_INIT_TAC "s0" THEN
    STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC exec (1--3) THEN
    sqr_tac 4 THEN
    ARM_STEPS_TAC exec (5--8) THEN
    mul_tac 9 THEN
    ARM_STEPS_TAC exec (10--12) THEN
    demont_tac 13 THEN
    ARM_STEPS_TAC exec (14--16) THEN
    inv_tac 17 THEN
    ARM_STEPS_TAC exec (18--21) THEN
    mul_tac 22 THEN
    ARM_STEPS_TAC exec (23--26) THEN
    mul_tac 27 THEN
    ARM_STEPS_TAC exec (28--31) THEN
    mul_tac 32 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC
  ] THEN

  (**** Now the preservation of the loop invariant ***)

  REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN

  ENSURES_INIT_TAC "s0" THEN
  STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC exec (1--4) THEN
  jdouble_tac 5 THEN
  ARM_STEPS_TAC exec (6--8) THEN
  jdouble_tac 9 THEN
  ARM_STEPS_TAC exec (10--12) THEN
  jdouble_tac 13 THEN
  ARM_STEPS_TAC exec (14--16) THEN
  jdouble_tac 17 THEN
  ARM_STEPS_TAC exec (18--219) THEN
  jadd_tac 220 THEN
  ARM_STEPS_TAC exec (221--221) THEN

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
