(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise Montgomery multiplication: the proof (see                       *)
(* poly_pointwise_montgomery_spec.ml).                                       *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/poly_pointwise_montgomery_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_scalar.ml";;

(* ------------------------------------------------------------------------- *)
(* The value stored for a coefficient from the 64-bit product p: with        *)
(* t = (low 32 bits of p) * q^-1 mod 2^32, computed with a 32-bit IMUL and   *)
(* sign-extended, the high 32 bits of p - t * q, with t * q computed as      *)
(* ((t << 10) - t) << 13 + t (here as the negation, ((t - (t << 10)) << 13)  *)
(* - t, added to p).                                                         *)
(* ------------------------------------------------------------------------- *)

let MONTRED_LANE = prove
 (`!p:int64.
     word_zx
      (word_ishr
        (word_add
          (word_sub
            (word_shl
              (word_sub
                (word_sx(word_zx(word_zx(word_mul (word_zx p)
                                           (word 58728449):int32):int64)
                         :int32):int64)
                (word_shl
                  (word_sx(word_zx(word_zx(word_mul (word_zx p)
                                             (word 58728449):int32):int64)
                           :int32):int64)
                  10))
              13)
            (word_sx(word_zx(word_zx(word_mul (word_zx p)
                                       (word 58728449):int32):int64)
                     :int32):int64))
          p)
        32):int32 =
     mld_montgomery_reduce p`,
  GEN_TAC THEN REWRITE_TAC[mld_montgomery_reduce; WORD_ZX_ZX_32_64_32] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SPEC_TAC(`word_sx(word_mul (word_zx (p:int64)) (word 58728449):int32)
            :int64`,`u:int64`) THEN
  GEN_TAC THEN
  REWRITE_TAC[WORD_BLAST
   `word_zx(word_ishr (v:int64) 32):int32 = word_subword v (32,32)`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_BLAST `word_shl (u:int64) 10 = word_mul u (word 1024)`;
              WORD_BLAST `word_shl (u:int64) 13 = word_mul u (word 8192)`] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 256 iterations  *)
(* of the loop multiplies one coefficient, addressed with the index 4 * i in *)
(* RDX; the loop test is the end of the body, as                             *)
(* ENSURES_EVENTS_WHILE_UP2_TAC requires, and the events of an iteration     *)
(* depend on its index only.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (b:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil r b pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 256
            (\i. f_ev_loop r b pc stackpointer returnaddress i))
          (f_ev_prol r b pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r:int64`; `b:int64`; `x:num->int32`;
    `y:num->int32`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; mld_poly_pointwise_montgomery;
              fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256`
   `pc + mldsa_poly_pointwise_montgomery_loop1`
   `pc + mldsa_poly_pointwise_montgomery_loop1_exit`
   `\i s. read R8 s = r /\ read RSI s = b /\ read RDX s = word(4 * i) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s =
                   y j) /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                   x j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                   mld_montgomery_reduce
                    (word_mul (word_sx (x j)) (word_sx (y j))))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    FULL_INIT_TAC THEN X86_STEPS_TAC EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_montgomery_reduce` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o C MATCH_MP (ASSUME `i < 256`) o
      check (fun th -> is_forall(concl th) &&
        free_in `y:num->int32` (concl th) &&
        not(free_in `x:num->int32` (concl th)))) THEN
    VAL_INT64_TAC `4 * i` THEN INDEX4_ADDR_TAC THEN
    X86_STEPS_TAC EXEC (1--14) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MONTRED_LANE]) THEN
    X86_STEPS_TAC EXEC (15--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_REWRITE_TAC[] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The return ***)

    FULL_EXIT_TAC EXEC 1]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
