(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition of polynomials, coefficientwise with wraparound.                 *)
(* This is the code for mlkem_poly_add from mlkem-native's portable C        *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which the compiler has vectorized. It is verified in the whole image (see *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x41e0.        *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    41e0: mov     x2, #0x0
    41e4: nop
    41e8: ldr     q0, [x0, x2]
    41ec: ldr     q1, [x1, x2]
    41f0: add     v0.8h, v0.8h, v1.8h
    41f4: str     q0, [x0, x2]
    41f8: add     x2, x2, #0x10
    41fc: cmp     x2, #0x200
    4200: b.ne    41e8 <mlkem_poly_add+0x8>
    4204: ret
 ***)

let MLKEM_NATIVE_POLY_ADD_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x41e0,0x4208];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r b x y pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,0x6480); (b,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x41e0) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add r (word(2 * i))))
                             s = x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add b (word(2 * i))))
                             s = y i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word_add (x i) (y i))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `b:int64`; `x:num->int16`; `y:num->int16`; `pc:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `32` `pc + 0x41e8` `pc + 0x41fc`
   `\i s. read X0 s = r /\ read X1 s = b /\ read X2 s = word(16 * i) /\
          read X30 s = returnaddress /\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add b (word(2 * j)))) s =
                   y j) /\
          (!j. 8 * i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   x j) /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word_add (x j) (y j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0] THEN ASM_REWRITE_TAC[];

    (*** The loop body, for 8 coefficients loaded as one 128-bit word ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [MATCH_MP CHUNK8_INPUT_SPLIT (ASSUME `i < 32`)]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CHUNK8_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!k. k < 8
          ==> read(memory :> bytes16(word_add b (word(2 * (8 * i + k)))))
                s0 = y(8 * i + k)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CHUNK8_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add r (word(16 * i)))) s0`) THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add b (word(16 * i)))) s0`) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY (fun n ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_GCC12_O2_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[]) (1--5) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE (SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (fun th ->
        can (term_match [] `read (memory :> bytes128 a) s = x`) (concl th) &&
        free_in `r:int64` (concl th))) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    REWRITE_TAC[CHUNK8_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[CHUNK8_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_GCC12_O2_EXEC (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `word_add:int16->int16->int16` (concl th)))]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_add_signature =
  ([("r", "int16_t[static 256]", "false");
    ("b", "int16_t[static 256]", "true")],
   "void",
   [("r", "256", 2); ("b", "256", 2)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_poly_add_signature
    MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_ADD_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r b pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,0x6480; b,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x41e0) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; b] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events b r pc returnaddress /\
                         memaccess_inbounds e2 [r,512; b,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(b:int64) (r:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil b r pc returnaddress)
        (APPEND
          (ENUMERATEL 32 (\i. f_ev_loop b r pc returnaddress i))
          (f_ev_prol b r pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_ADD_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x41e8` `pc + 0x4204`
    `\i s. read X30 s = returnaddress /\
           read X0 s = r /\ read X1 s = b /\ read X2 s = word(16 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_ADD_GCC12_O2_EXEC (1--2) THEN
    REWRITE_TAC[MULT_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_ADD_GCC12_O2_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_ADD_GCC12_O2_EXEC (1--7) THEN
  SUBGOAL_THEN
   `~(val(word_add (word(16 * i)) (word 18446744073709551120):int64) = 0) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    ASM_CASES_TAC `i = 31` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 /\ ~(i = 31)
      ==> 16 * i + 18446744073709551120 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
