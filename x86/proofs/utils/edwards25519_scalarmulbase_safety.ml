(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proof of the cores of                   *)
(* edwards25519_scalarmulbase and edwards25519_scalarmulbase_alt, which    *)
(* only differ in the field operations and their offsets.                  *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;

(* Simulate the call of the modular inverse at offset off, using the       *)
(* safety theorem registered under the label assump_name.                  *)

let EDWARDS25519_SCALARMULBASE_MODINV_TAC (tmc,exec,off)
    (assump_name:string) (n:int) =
  let pcoff = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (tmc,
          exec,
          off,
          (GEN_REWRITE_CONV RAND_CONV [bignum_inv_p25519_tmc] THENC TRIM_LIST_CONV)
            `TRIM_LIST (17,18) bignum_inv_p25519_tmc`,
            safety_th)
        [`e:(uarch_event)list`; `read RDI s`; `read RSI s`;
        pcoff; `stackpointer:int64`] n
    THENL [
      EXISTS_E2_TAC(ref
        [`scalar:int64`;`res:int64`;`pc:num`;`stackpointer:int64`;`tables:num`;
         (* inside the loop... *)
         `i:num`;
         `f_ev_loop:int64->int64->num->num->int64->num->num->(uarch_event)list`]);

      LABEL_TAC assump_name safety_th
    ]);;

(* The safety proof of the core, given its code tmc, decoding theorem exec *)
(* and constant data; the safety theorem of the modular inverse and the    *)
(* offset of its call; the PC of the end of the main loop; and the number  *)
(* of steps of the inlined field multiplications.                          *)

let EDWARDS25519_SCALARMULBASE_SAFETY_TAC (tmc,exec,data) inv_th
    ~inv ~loop_end ~mul_4 ~mul_p25519 =
  let pcoff off = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  let modinv_tac = EDWARDS25519_SCALARMULBASE_MODINV_TAC (tmc,exec,inv) in
  (* Prepare the safety theorem of subroutine to be used! This is necessary to
     keep introduction of metavariable in the right order. *)
  ASSUME_CALLEE_SAFETY_TAILED_TAC inv_th "H_INV" THEN

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
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  REWRITE_TAC[BYTES_LOADED_DATA] THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `63` `pc + 0x1f1`
    (pcoff loop_end)(*+2 insn *)
   (vsubst [data,`constant_data:byte list`]
    `\i s.
       read (memory :> bytes(word tables,48576)) s =
       num_of_bytelist constant_data /\
       read RSP s = stackpointer /\
       read (memory :> bytes64 (word_add stackpointer (word 448))) s = res /\
       read (memory :> bytes64 (word_add stackpointer (word 480))) s =
           word(tables + 0xc0 + 768 * i) /\
       read (memory :> bytes64 (word_add stackpointer (word 456))) s =
           word (4 * i)`) THEN
  REPEAT CONJ_TAC THENL [
    ARITH_TAC;

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC exec (1--39) THEN

    (*** Fold the rip-relative LEA results so `read R10 s = word tables`
         and `read R11 s = word_add (word tables) (word 96)`. ***)

    UNDISCH_TAC `read R10 s39 =
        word(val (word (pc + 174):(64)word) +
             val (word_sx (iword (&tables - (&pc + &174)):int32):(64)word):num)` THEN
    IMP_REWRITE_TAC[RIP_REL_ADDR_FOLD] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `read R11 s39 =
        word_add
        (word (val (word (pc + 174):(64)word) +
               val (word_sx (iword (&tables - (&pc + &174)):int32):(64)word):num))
        (word 96)` THEN
    IMP_REWRITE_TAC[RIP_REL_ADDR_FOLD] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

    X86_STEPS_TAC exec (40--97) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONJ_TAC THENL [WORD_ARITH_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The main loop invariant for adding the next table entry ***)

    REPEAT STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC exec (1--281) THEN
    X86_STEPS_TAC exec (282--
      (281 + 19(*DOUBLE_TWICE4*) + 19(*SUB_TWICE4*) + 19(*ADD_TWICE4*) +
       mul_4 + mul_4 + mul_4 + 19(*SUB_TWICE4*) +
       19(*ADD_TWICE4*) + 19(*SUB_TWICE4*) + 19(*ADD_TWICE4*) +
       mul_4 + mul_4 + mul_4 + mul_4)) THEN

    X86_STEPS_TAC exec (296--298) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [
      REWRITE_TAC[GSYM WORD_ADD] THEN
      MAP_EVERY VAL_INT64_TAC [`4 * i + 4`] THEN
      ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
      SIMPLE_ARITH_TAC; ALL_TAC
    ] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN
      `val (word_ushr (word (4 * i):int64) 6) = (4 * i) DIV 64`
      SUBST_ALL_TAC THENL [
      REWRITE_TAC[VAL_WORD_USHR] THEN
      IMP_REWRITE_TAC[VAL_WORD;MOD_LT;DIMINDEX_64] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC
    ] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC] THEN

  (*** Clean up ready for the final translation part ***)

  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC exec (3--26) THEN
  modinv_tac "H_INV" 27 THEN
  X86_STEPS_TAC exec (28--(27+1+mul_p25519*2)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  DISCHARGE_SAFETY_PROPERTY_TAC;;
