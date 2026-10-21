(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proof of the cores of                   *)
(* edwards25519_scalarmuldouble and edwards25519_scalarmuldouble_alt,      *)
(* which only differ in the field operations and their offsets.            *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;

(* Simulate the call at offset off of the subroutine with code sub_mc and  *)
(* arguments args, using the safety theorem registered under the label     *)
(* assump_name.                                                            *)

let EDWARDS25519_SCALARMULDOUBLE_CALL_TAC (mc,exec) (off,sub_mc) args
    (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (mc,exec,off,sub_mc,safety_th) (`e:(uarch_event)list`::args) n
    THENL [
      EXISTS_E2_TAC(ref
        [`scalar:int64`;`point:int64`;`res:int64`;`pc:num`;`bscalar:int64`;
         `stackpointer:int64`;`tables:num`;
         (* inside the loop... *)
         `i:num`;
         `f_ev_loop:int64->int64->int64->int64->
                    num->num->int64->num->(uarch_event)list`]);

      LABEL_TAC assump_name safety_th
    ]);;

(* The safety proof of the core, given its code mc, decoding theorem exec  *)
(* and constant data; the safety theorems of the modular inverse and of    *)
(* the local point operations; the offset of the call of the modular       *)
(* inverse; the PCs of the start and the end of the main loop; and the     *)
(* number of steps of the inlined field multiplications.                   *)

let EDWARDS25519_SCALARMULDOUBLE_SAFETY_TAC (mc,exec,data)
    (inv_th,epdouble_th,pdouble_th,epadd_th,pepadd_th)
    ~inv ~loop:(loop_start,loop_end) ~mul_4 ~mul_p25519 =
  let pcoff off = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  let call_tac = EDWARDS25519_SCALARMULDOUBLE_CALL_TAC (mc,exec) in
  let modinv_tac = call_tac
    (inv,(GEN_REWRITE_CONV RAND_CONV [bignum_inv_p25519_mc] THENC
          TRIM_LIST_CONV) `TRIM_LIST (12,16) bignum_inv_p25519_mc`)
    [`read X0 s`; `read X1 s`; pcoff inv;
     `word_add stackpointer (word 192):int64`]
  and double_tac = call_tac (0x0,mc)
    [`read X22 s`; `read X23 s`; `pc:num`; `tables:num`; `read SP s`]
  and add_tac = call_tac (0x0,mc)
    [`read X22 s`; `read X23 s`; `read X24 s`;
     `pc:num`; `tables:num`; `read SP s`] in
  (* Prepare the safety theorem of subroutine to be used! This is necessary to
     keep introduction of metavariable in the right order. *)
  ASSUME_CALLEE_SAFETY_TAILED_TAC inv_th "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC epdouble_th "H_EPDOUBLE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC pdouble_th "H_PDOUBLE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC epadd_th "H_EPADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC pepadd_th "H_PEPADD" THEN

  CONCRETIZE_F_EVENTS_TAC
    `\(scalar:int64) (point:int64) (bscalar:int64) (res:int64) (tables:num)
      (pc:num) (stackpointer:int64).
      APPEND
        (f_ev_epil scalar point bscalar res tables pc stackpointer)
        (APPEND
          (ENUMERATEL 63 (\i.
            f_ev_loop scalar point bscalar res tables pc stackpointer i))
          (f_ev_prol scalar point bscalar res tables pc stackpointer))
    :(uarch_event)list` THEN

  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ALLPAIRS; ALL] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  REWRITE_TAC[fst exec] THEN
  REWRITE_TAC[BYTES_LOADED_DATA] THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `63`
    (pcoff loop_start) (pcoff loop_end)(*+1 insn *)
   (vsubst [data,`constant_data:byte list`]
    `\i s.
       read (memory :> bytes (word tables,768)) s =
         num_of_bytelist constant_data /\
       read SP s = word_add stackpointer (word 192) /\
       read X25 s = res /\
       read X19 s = word (4 * (63 - i))`) THEN
  REPEAT CONJ_TAC THENL [
    ARITH_TAC;

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC exec (1--64) THEN
    ARM_STEPS_TAC exec (65--(64+6+mul_4)) THEN
    (* following the step numbers of fn correctness... *)
    ARM_STEPS_TAC exec (72--75) THEN
    double_tac "H_EPDOUBLE" 76 THEN
    ARM_STEPS_TAC exec (77--83) THEN
    add_tac "H_EPADD" 84 THEN
    ARM_STEPS_TAC exec (85--90) THEN
    double_tac "H_EPDOUBLE" 91 THEN
    ARM_STEPS_TAC exec (92--98) THEN
    add_tac "H_EPADD" 99 THEN
    ARM_STEPS_TAC exec (100--105) THEN
    double_tac "H_EPDOUBLE" 106 THEN
    ARM_STEPS_TAC exec (107--113) THEN
    add_tac "H_EPADD" 114 THEN
    ARM_STEPS_TAC exec (115--120) THEN
    double_tac "H_EPDOUBLE" 121 THEN
    ARM_STEPS_TAC exec (122--128) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP ADRP_ADD_FOLD)) THEN
    ARM_STEPS_TAC exec (129--539) THEN
    ARM_STEPS_TAC exec (540--544) THEN
    add_tac "H_PEPADD" 545 THEN
    ARM_STEPS_TAC exec (546--547) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[ARITH]; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** Defer the main invariant proof to below ***)

    ALL_TAC;

    (*** The finale with the modular inverse ***)

    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC exec (1--2) THEN
    modinv_tac "H_INV" 3 THEN
    ARM_STEPS_TAC exec (4--(3+3+mul_p25519)) THEN
    ARM_STEPS_TAC exec (5--(4+3+mul_p25519)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  (*** The preservation of the loop invariant ***)
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC exec (1--5) THEN
  double_tac "H_PDOUBLE" 6 THEN
  ARM_STEPS_TAC exec (7--8) THEN
  ARM_STEPS_TAC exec (9--18) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP ADRP_ADD_FOLD)) THEN
  ARM_STEPS_TAC exec (19--189) THEN
  ARM_STEPS_TAC exec (190--214) THEN
  ARM_STEPS_TAC exec (215--222) THEN
  ARM_STEPS_TAC exec (223--445) THEN
  ARM_STEPS_TAC exec (446--471) THEN
  ARM_STEPS_TAC exec (472--475) THEN
  double_tac "H_PDOUBLE" 476 THEN
  ARM_STEPS_TAC exec (477--478) THEN
  ARM_STEPS_TAC exec (479--483) THEN
  add_tac "H_PEPADD" 484 THEN
  ARM_STEPS_TAC exec (485--486) THEN
  ARM_STEPS_TAC exec (487--490) THEN
  double_tac "H_PDOUBLE" 491 THEN
  ARM_STEPS_TAC exec (492--493) THEN
  ARM_STEPS_TAC exec (494--497) THEN
  double_tac "H_EPDOUBLE" 498 THEN
  ARM_STEPS_TAC exec (499--500) THEN
  ARM_STEPS_TAC exec (501--505) THEN
  add_tac "H_EPADD" 506 THEN
  ARM_STEPS_TAC exec (507--508) THEN
  ARM_STEPS_TAC exec (509--509) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    MAP_EVERY VAL_INT64_TAC [`4 * (63 - i)`; `4`] THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
    SIMPLE_ARITH_TAC; ALL_TAC
  ] THEN
  CONJ_TAC THENL [ IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL [
    AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC
  ]; ALL_TAC] THEN
  (* Found this pattern from safety_print_log := true *)
  SUBGOAL_THEN
    `val (word_ushr (word_sub (word (4 * (63 - i))) (word 4):int64) 6) =
     (4 * (63 - (i + 1))) DIV 64` SUBST_ALL_TAC THENL [
    REWRITE_TAC[VAL_WORD_USHR] THEN
    IMP_REWRITE_TAC[WORD_SUB2; VAL_WORD;MOD_LT;DIMINDEX_64] THEN
    REPEAT CONJ_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC
  ] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;
