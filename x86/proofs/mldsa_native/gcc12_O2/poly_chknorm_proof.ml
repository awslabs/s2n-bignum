(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Check of the norm of a polynomial: the proof (see poly_chknorm_spec.ml).  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/poly_chknorm_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_scalar.ml";;

(*** The absolute value as the code selects it, with the mask of the sign ***)

let MLD_CT_ABS_SELECT = prove
 (`!y:int32. mld_ct_abs y =
             word_xor (word_and (word_xor (word_neg y) y) (word_ishr y 31)) y`,
  REWRITE_TAC[mld_ct_abs; GSYM MSB_IVAL; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN BITBLAST_TAC);;

let WORD_OR_ONES_32 = prove
 (`!y:int32. word_or (word 4294967295) y = word 4294967295`,
  BITBLAST_TAC);;

(*** The accumulated mask for the coefficients before i, and one more ***)

let EXISTS_LT_SUC_SPLIT = prove
 (`!P i. (?j. j < i + 1 /\ P j) <=> (?j. j < i /\ P j) \/ P i`,
  REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The loop handles one        *)
(* coefficient per iteration and accumulates the masks in ESI; the loop test *)
(* is the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires, and the *)
(* events of an iteration depend on its index only.                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (bnd:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil a bnd pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 256
            (\i. f_ev_loop a bnd pc stackpointer returnaddress i))
          (f_ev_prol a bnd pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `x:num->int32`; `bnd:int64`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; NONOVERLAPPING_CLAUSES; ALL; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mldsa_poly_chknorm_loop1`
   `pc + mldsa_poly_chknorm_loop1_exit`
   `\i s. read RCX s = word_add a (word(4 * i)) /\
          read R8 s = word_add a (word 1024) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          read RDI s = word_zx(word_sub (word_zx (bnd:int64):int32) (word 1)) /\
          read RSI s =
          word_zx(if ?j. j < i /\
                         ival(word_sub (word_sub (word_zx bnd) (word 1))
                                       (mld_ct_abs(x j))) < &0
                  then word 4294967295 else word 0:int32) /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization: B - 1 computed by LEA in 32 bits ***)

    FULL_INIT_TAC THEN
    X86_STEPS_TAC EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    CONJ_TAC THENL
     [W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop body, with the loop test: the mask for coefficient i ***)
    (*** is ORed in                                                     ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `x:num->int32` (concl th))) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
    X86_STEPS_TAC EXEC (1--16) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_SX_32_64_32;
                    WORD_ZX_ISHR_SX_31] THEN
        REWRITE_TAC[EXISTS_LT_SUC_SPLIT; GSYM MLD_CT_ABS_SELECT] THEN
        SPEC_TAC(`?j. j < i /\
                      ival(word_sub (word_sub (word_zx (bnd:int64)) (word 1))
                                    (mld_ct_abs((x:num->int32) j))) < &0`,
                 `p:bool`) THEN
        GEN_TAC THEN ASM_CASES_TAC `p:bool` THEN
        ASM_REWRITE_TAC[WORD_OR_0; WORD_OR_ONES_32; WORD_ISHR_31_COND] THEN
        NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The return, with the result moved to EAX ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    X86_STEPS_TAC EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[mld_poly_chknorm; WORD_ZX_ZX_32_64_32] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
