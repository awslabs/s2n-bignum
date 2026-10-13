(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proof of the cores of                   *)
(* curve25519_x25519base, curve25519_x25519base_alt and their _byte        *)
(* versions, which only differ in the field operations, the conversions    *)
(* from and to bytes, and the offsets.                                     *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;

(* Simulate the call of the modular inverse at offset off, using the       *)
(* safety theorem registered under the label assump_name.                  *)

let CURVE25519_X25519BASE_MODINV_TAC (mc,exec,off)
    (assump_name:string) (n:int) =
  let pcoff = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mc,exec,off,
        (GEN_REWRITE_CONV RAND_CONV [bignum_inv_p25519_mc] THENC TRIM_LIST_CONV)
        `TRIM_LIST (12,16) bignum_inv_p25519_mc`,
        safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`;
        pcoff; `stackpointer:int64`] n
    THENL [
      EXISTS_E2_TAC(ref
        [`scalar:int64`;`point:int64`;`res:int64`;`pc:num`;
         `stackpointer:int64`;`tables:num`;
         (* inside the loop... *)
         `i:num`;
         `f_ev_loop:int64->int64->int64->num->int64->num->(uarch_event)list`]);

      LABEL_TAC assump_name safety_th
    ]
  );;

(* The safety proof of the core, given its code mc, decoding theorem exec  *)
(* and constant data; the safety theorem of the modular inverse and the    *)
(* offset of its call; the PCs of the start and the end of the main loop;  *)
(* the number of steps before the main loop, of the inlined field          *)
(* multiplications and of the final conversion to bytes (0 if none).       *)

let CURVE25519_X25519BASE_SAFETY_TAC (mc,exec,data) inv_th
    ~inv ~loop:(loop_start,loop_end) ~init ~mul_4 ~mul_p25519 ~out_steps =
  let pcoff off = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  let modinv_tac = CURVE25519_X25519BASE_MODINV_TAC (mc,exec,inv) in
  let loop_steps =
    (211+(14(*DOUBLE_TWICE4*) + 16(*SUB_TWICE4*) + 16(*ADD_TWICE4*) +
          mul_4(*MUL_4*) + mul_4(*MUL_4*) + mul_4(*MUL_4*) + 16(*SUB_TWICE4*) +
          16(*ADD_TWICE4*) + 16(*SUB_TWICE4*) + 16(*ADD_TWICE4*) +
          mul_4(*MUL_4*) + mul_4(*MUL_4*) + mul_4(*MUL_4*) + mul_4(*MUL_4*))) in
  (* Prepare the safety theorem of subroutine to be used! This is necessary to
     keep introduction of metavariable in the right order. *)
  ASSUME_CALLEE_SAFETY_TAILED_TAC inv_th "H_INV_SAFE" THEN

  CONCRETIZE_F_EVENTS_TAC
    `\(scalar:int64) (res:int64) (tables:num) (pc:num) (stackpointer:int64).
      APPEND
        (f_ev_epil scalar res tables pc stackpointer)
        (APPEND
          (ENUMERATEL 63 (\i.
            f_ev_loop scalar res tables pc stackpointer i))
          (f_ev_prol scalar res tables pc stackpointer))
    :(uarch_event)list` THEN

  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ALLPAIRS; ALL] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN

  REWRITE_TAC[BYTES_LOADED_DATA] THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `63`
    (pcoff loop_start) (pcoff loop_end)(*+2 insn *)
   (vsubst [data,`constant_data:byte list`]
    `\i s.
       read (memory :> bytes(word tables,48576)) s =
         num_of_bytelist constant_data /\
       read SP s = stackpointer /\
       read X23 s = res /\
       read X19 s = word(tables + 0xc0 + 768 * i) /\
       read X20 s = word (4 * (i + 1))`) THEN
  REPEAT CONJ_TAC THENL [
    ARITH_TAC;

    (*** Initial setup and modification of the inputs ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC exec (1--init) THEN

    FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP ADRP_ADD_FOLD) THEN

    ARM_STEPS_TAC exec ((init+1)--(init+36)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONJ_TAC THENL [WORD_ARITH_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The main loop invariant for adding the next table entry ***)

    REPEAT STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC exec (1--5) THEN
    ARM_STEPS_TAC exec (6--11) THEN
    ARM_STEPS_TAC exec (12--183) THEN
    ARM_STEPS_TAC exec (184--211) THEN
    ARM_STEPS_TAC exec (212--loop_steps) THEN
    ARM_STEPS_TAC exec ((loop_steps+1)--(loop_steps+3)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [
      REWRITE_TAC[VAL_WORD_ADD] THEN
      MAP_EVERY VAL_INT64_TAC [`4*(i+1)`;`4`] THEN
      ASM_REWRITE_TAC[DIMINDEX_64] THEN
      ONCE_REWRITE_TAC[GSYM COND_RAND] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN
      SIMPLE_ARITH_TAC;

      ALL_TAC
    ] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE;ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE;ALL_TAC] THEN

    (* Found this pattern from safety_print_log := true *)
    SUBGOAL_THEN
      `word (8 * val (word_ushr (word (4 * (i + 1)):int64) 6))
      :int64 = word (8 * (4 * (i + 1)) DIV 2 EXP 6)`
    SUBST_ALL_TAC THENL [
      AP_TERM_TAC THEN REWRITE_TAC[VAL_WORD_USHR] THEN
      IMP_REWRITE_TAC[VAL_WORD;MOD_LT;DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
      ALL_TAC
    ] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC
  ] THEN

  (*** Clean up ready for the final translation part ***)

  ENSURES_INIT_TAC "s0" THEN
  STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC exec (1--34) THEN
  modinv_tac "H_INV_SAFE" 35 THEN
  ARM_STEPS_TAC exec (36--(35+mul_p25519)) THEN
  ARM_STEPS_TAC exec ((36+mul_p25519)--(35+mul_p25519+out_steps)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  SUBST_ALL_TAC (ARITH_RULE`2 EXP 6 = 64`) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;
