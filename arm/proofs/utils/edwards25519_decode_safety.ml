(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proof of edwards25519_decode and        *)
(* edwards25519_decode_alt, which only differ in the field operations of   *)
(* the local multiplication (LOCAL_MUL_P25519) and repeated squaring       *)
(* (LOCAL_NSQR_P25519).                                                    *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;

(* The safety proof of LOCAL_NSQR_P25519, given the decoding theorem, the  *)
(* PCs of the start and the end of its loop and the numbers of steps       *)
(* before the loop and of its body.                                        *)

let EDWARDS25519_DECODE_NSQR_SAFETY_TAC exec
    ~loop:(loop_start,loop_end) ~pre ~body =
  let pcoff off = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  CONCRETIZE_F_EVENTS_TAC
    `\(z:int64) (k:int64) (x:int64) (pc:num).
      APPEND
        (f_ev_loop_post z k x pc)
        (APPEND
          (ENUMERATEL (val k) (f_ev_loop z k x pc))
            (f_ev_loop_pre z k x pc))
      :(uarch_event) list` THEN

  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN

  REPEAT STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; ALL; SOME_FLAGS] THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `val (k:int64)`
    (pcoff loop_start) (pcoff loop_end)(*+1*)
   `\i s. read X0 s = z /\
          read X1 s = word((val (k:int64)) - i)` THEN REPEAT CONJ_TAC THENL [
    ASM_ARITH_TAC;

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC exec (1--pre) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[SUB_0;WORD_VAL];ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC; (*** Main loop invariant ***)

    ENSURES_INIT_TAC "s0" THEN
    STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC exec (1--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC
  ] THEN

  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC exec (1--body) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    ABBREV_TAC `k' = val (k:int64)` THEN
    VAL_INT64_TAC `k' - i` THEN VAL_INT64_TAC `1` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
    SIMPLE_ARITH_TAC; ALL_TAC
  ] THEN
  CONJ_TAC THENL [
    IMP_REWRITE_TAC[WORD_SUB2] THEN
    ABBREV_TAC `k' = val (k:int64)` THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC];
    ALL_TAC
  ] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* Simulate a call of LOCAL_MUL_P25519 or LOCAL_NSQR_P25519 (both at       *)
(* offset 0 and with the same arguments), using the safety theorem         *)
(* registered under the label assump_name.                                 *)

let EDWARDS25519_DECODE_CALL_TAC (mc,exec) (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (mc,exec,0x0,mc,safety_th)
        [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
        `pc:num`] n THENL [
      EXISTS_E2_TAC (ref [`z:int64`;`c:int64`;`pc:num`;`stackpointer:int64`]);

      LABEL_TAC assump_name safety_th
    ]);;

(* The safety proof of the core, given its code and decoding theorem and   *)
(* the safety theorems of LOCAL_MUL_P25519 and LOCAL_NSQR_P25519.          *)

let EDWARDS25519_DECODE_SAFETY_TAC (mc,exec) (mul_th,nsqr_th) =
  let mul_tac = EDWARDS25519_DECODE_CALL_TAC (mc,exec)
  and nsqr_tac = EDWARDS25519_DECODE_CALL_TAC (mc,exec) in
  ASSUME_CALLEE_SAFETY_TAILED_TAC mul_th "H_MUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC nsqr_th "H_NSQR" THEN
  META_EXISTS_TAC THEN STRIP_TAC THEN

  REWRITE_TAC[ALL; C_ARGUMENTS; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_INIT_TAC "s0" THEN
  (* simply use symbolic sim to cover the first part of ENSURES_SEQUENCE_TAC *)
  ARM_STEPS_TAC exec (1--74) THEN
  (* now the second part of ENSURES_SEQUENCE_TAC. *)
  ARM_STEPS_TAC exec (75--78) THEN
  nsqr_tac "H_NSQR" 79 THEN
  ARM_STEPS_TAC exec (80--111) THEN
  mul_tac "H_MUL" 112 THEN
  ARM_STEPS_TAC exec (113--125) THEN
  mul_tac "H_MUL" 126 THEN

  (*** The power tower. Simply use the original step numbers in fn correctness
       proof! ***)
  ARM_STEPS_TAC exec (53--57) THEN nsqr_tac "H_NSQR" 58 THEN
  ARM_STEPS_TAC exec (59--63) THEN mul_tac "H_MUL" 64 THEN
  ARM_STEPS_TAC exec (65--69) THEN nsqr_tac "H_NSQR" 70 THEN
  ARM_STEPS_TAC exec (71--75) THEN mul_tac "H_MUL" 76 THEN
  ARM_STEPS_TAC exec (77--81) THEN nsqr_tac "H_NSQR" 82 THEN
  ARM_STEPS_TAC exec (83--87) THEN mul_tac "H_MUL" 88 THEN
  ARM_STEPS_TAC exec (89--93) THEN nsqr_tac "H_NSQR" 94 THEN
  ARM_STEPS_TAC exec (95--99) THEN mul_tac "H_MUL" 100 THEN
  ARM_STEPS_TAC exec (101--105) THEN nsqr_tac "H_NSQR" 106 THEN
  ARM_STEPS_TAC exec (107--111) THEN mul_tac "H_MUL" 112 THEN
  ARM_STEPS_TAC exec (113--117) THEN nsqr_tac "H_NSQR" 118 THEN
  ARM_STEPS_TAC exec (119--123) THEN mul_tac "H_MUL" 124 THEN
  ARM_STEPS_TAC exec (125--129) THEN nsqr_tac "H_NSQR" 130 THEN
  ARM_STEPS_TAC exec (131--135) THEN mul_tac "H_MUL" 136 THEN
  ARM_STEPS_TAC exec (137--141) THEN nsqr_tac "H_NSQR" 142 THEN
  ARM_STEPS_TAC exec (143--147) THEN mul_tac "H_MUL" 148 THEN
  ARM_STEPS_TAC exec (149--153) THEN nsqr_tac "H_NSQR" 154 THEN
  ARM_STEPS_TAC exec (155--159) THEN mul_tac "H_MUL" 160 THEN
  ARM_STEPS_TAC exec (161--165) THEN nsqr_tac "H_NSQR" 166 THEN
  ARM_STEPS_TAC exec (167--171) THEN mul_tac "H_MUL" 172 THEN
  ARM_STEPS_TAC exec (173--177) THEN nsqr_tac "H_NSQR" 178 THEN
  ARM_STEPS_TAC exec (179--183) THEN mul_tac "H_MUL" 184 THEN

  (*** e^2 * w computation ***)
  ARM_STEPS_TAC exec (185--189) THEN nsqr_tac "H_NSQR" 190 THEN
  ARM_STEPS_TAC exec (191--195) THEN mul_tac "H_MUL" 196 THEN

  (*** s = u * e ***)
  ARM_STEPS_TAC exec (197--201) THEN mul_tac "H_MUL" 202 THEN
  ARM_STEPS_TAC exec (203--225) THEN
  mul_tac "H_MUL" 226 THEN

  (*** The remaining parts ***)
  ARM_STEPS_TAC exec (227--283) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;
