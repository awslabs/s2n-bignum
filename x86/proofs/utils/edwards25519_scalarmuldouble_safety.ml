(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proof of the cores of                   *)
(* edwards25519_scalarmuldouble and edwards25519_scalarmuldouble_alt,      *)
(* which only differ in the field operations and their offsets.            *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;

(* Simulate the call at offset off of the subroutine with code sub_tmc and *)
(* arguments args, using the safety theorem registered under the label     *)
(* assump_name.                                                            *)

let EDWARDS25519_SCALARMULDOUBLE_CALL_TAC (tmc,exec) (off,sub_tmc) args
    (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (tmc,exec,off,sub_tmc,safety_th) (`e:(uarch_event)list`::args) n
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

(* The safety proof of the core, given its code tmc, decoding theorem exec *)
(* and constant data; the safety theorems of the modular inverse and of    *)
(* the local point operations; the offset of the call of the modular       *)
(* inverse; the PCs of the start and the end of the main loop; the number  *)
(* of steps of the inlined field multiplications; and the offsets of the   *)
(* two instructions computing the address of the table, before and in the  *)
(* main loop.                                                              *)

let EDWARDS25519_SCALARMULDOUBLE_SAFETY_TAC (tmc,exec,data)
    (inv_th,epdouble_th,pdouble_th,epadd_th,pepadd_th)
    ~inv ~loop:(loop_start,loop_end) ~mul_4 ~mul_p25519
    ~lea:(lea_init,lea_loop) =
  let pcoff off = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  let call_tac = EDWARDS25519_SCALARMULDOUBLE_CALL_TAC (tmc,exec) in
  let modinv_tac = call_tac
    (inv,(GEN_REWRITE_CONV RAND_CONV [bignum_inv_p25519_tmc] THENC
          TRIM_LIST_CONV) `TRIM_LIST (17,18) bignum_inv_p25519_tmc`)
    [`read RDI s`; `read RSI s`; pcoff inv;
     `word_add stackpointer (word 200):int64`]
  and double_tac = call_tac (0x0,tmc)
    [`read RDI s`; `read RSI s`; `pc:num`; `tables:num`; `read RSP s`]
  and add_tac = call_tac (0x0,tmc)
    [`read RDI s`; `read RSI s`; `read RBP s`;
     `pc:num`; `tables:num`; `read RSP s`] in
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
  ENSURES_EXISTING_PRESERVED_TAC `RSP` THEN
  REWRITE_TAC[fst exec] THEN
  REWRITE_TAC[BYTES_LOADED_DATA] THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `63`
    (pcoff loop_start) (pcoff loop_end)(*+3 insn *)
   (vsubst [data,`constant_data:byte list`]
    `\i s.
       read (memory :> bytes(word tables,768)) s =
       num_of_bytelist constant_data /\
       read RSP s = word_add stackpointer (word 200) /\
       read (memory :> bytes64(word_add stackpointer (word 1664))) s = res /\
       read (memory :> bytes64(word_add stackpointer (word 1656))) s =
           word (4 * (63 - i))`) THEN
  REPEAT CONJ_TAC THENL [
    ARITH_TAC;

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC exec (1--87) THEN
    X86_STEPS_TAC exec (88--(87+9+mul_4)) THEN
    (* following the step numbers of fn correctness... *)
    X86_STEPS_TAC exec (98--101) THEN
    double_tac "H_EPDOUBLE" 102 THEN
    X86_STEPS_TAC exec (103--109) THEN
    add_tac "H_EPADD" 110 THEN
    X86_STEPS_TAC exec (111--116) THEN
    double_tac "H_EPDOUBLE" 117 THEN
    X86_STEPS_TAC exec (118--124) THEN
    add_tac "H_EPADD" 125 THEN
    X86_STEPS_TAC exec (126--131) THEN
    double_tac "H_EPDOUBLE" 132 THEN
    X86_STEPS_TAC exec (133--139) THEN
    add_tac "H_EPADD" 140 THEN
    X86_STEPS_TAC exec (141--146) THEN
    double_tac "H_EPDOUBLE" 147 THEN
    X86_STEPS_TAC exec (148--167) THEN
    UNDISCH_TAC
     (vsubst [mk_small_numeral lea_init,`lea:num`]
       `read RBP s167 =
        word(val(word(pc + lea):int64) +
             val(word_sx(iword(&tables - (&pc + &lea)):int32):int64))`) THEN
    IMP_REWRITE_TAC[RIP_REL_ADDR_FOLD] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    X86_STEPS_TAC exec (168--709) THEN
    X86_STEPS_TAC exec (710--714) THEN
    add_tac "H_PEPADD" 715 THEN
    X86_STEPS_TAC exec (716--717) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[ARITH]; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** Defer the main invariant proof to below ***)

    ALL_TAC;

    (*** The finale with the modular inverse ***)

    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC exec (1--2) THEN
    modinv_tac "H_INV" 3 THEN
    X86_STEPS_TAC exec (4--(3+mul_p25519)) THEN
    X86_STEPS_TAC exec (5--(4+mul_p25519)) THEN
    X86_STEPS_TAC exec (6--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  (*** The preservation of the loop invariant ***)

  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC exec (1--7) THEN
  double_tac "H_PDOUBLE" 8 THEN
  X86_STEPS_TAC exec (9--10) THEN
  X86_STEPS_TAC exec (11--22) THEN
  X86_STEPS_TAC exec (23--35) THEN
  UNDISCH_TAC
   (vsubst [mk_small_numeral lea_loop,`lea:num`]
     `read RBP s35 =
      word(val(word(pc + lea):int64) +
           val(word_sx(iword(&tables - (&pc + &lea)):int32):int64))`) THEN
  IMP_REWRITE_TAC[RIP_REL_ADDR_FOLD] THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  X86_STEPS_TAC exec (36--242) THEN
  X86_STEPS_TAC exec (243--277) THEN
  X86_STEPS_TAC exec (278--289) THEN
  X86_STEPS_TAC exec (290--601) THEN
  X86_STEPS_TAC exec (602--627) THEN
  X86_STEPS_TAC exec (628--631) THEN
  double_tac "H_PDOUBLE" 632 THEN
  X86_STEPS_TAC exec (633--634) THEN
  X86_STEPS_TAC exec (635--639) THEN
  add_tac "H_PEPADD" 640 THEN
  X86_STEPS_TAC exec (641--642) THEN
  X86_STEPS_TAC exec (643--646) THEN
  double_tac "H_PDOUBLE" 647 THEN
  X86_STEPS_TAC exec (648--649) THEN
  X86_STEPS_TAC exec (650--653) THEN
  double_tac "H_EPDOUBLE" 654 THEN
  X86_STEPS_TAC exec (655--656) THEN
  X86_STEPS_TAC exec (657--661) THEN
  add_tac "H_EPADD" 662 THEN
  X86_STEPS_TAC exec (663--664) THEN
  X86_STEPS_TAC exec (665--665) THEN
  X86_STEPS_TAC exec (666--667) THEN
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
