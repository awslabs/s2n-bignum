(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of polynomial coefficients producing nonnegative remainders.    *)
(* This is the code for mlkem_poly_reduce from mlkem-native's portable C     *)
(* implementation compiled by clang 17 with -O3 (see                         *)
(* mlkem_native/README.md), which is the same as with -O2. It is verified in *)
(* the whole image (see libmlkem.ml).                                        *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_reduce:
       +0x0: mov     x8, xzr
       +0x4: mov     w9, #0x4ebf
       +0x8: mov     w10, #0x2000000
       +0xc: mov     w11, #0xfffff2ff
      +0x10: ldrsh   w12, [x0, x8]
      +0x14: madd    w13, w12, w9, w10
      +0x18: asr     w13, w13, #26
      +0x1c: madd    w12, w13, w11, w12
      +0x20: sxth    w13, w12
      +0x24: add     w14, w12, #0xd01
      +0x28: neg     w13, w13, lsr #16
      +0x2c: lsr     w13, w13, #16
      +0x30: bic     w12, w12, w13
      +0x34: and     w13, w14, w13
      +0x38: orr     w12, w13, w12
      +0x3c: strh    w12, [x0, x8]
      +0x40: add     x8, x8, #0x2
      +0x44: cmp     x8, #0x200
      +0x48: b.ne    <mlkem_poly_reduce+0x10>
      +0x4c: ret
 ***)

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_reduce"];;

(* ------------------------------------------------------------------------- *)
(* The value computed for each coefficient.                                  *)
(* ------------------------------------------------------------------------- *)

(*** The conditional addition of 3329, mlk_scalar_signed_to_unsigned_q,
 *** as compiled, applied to the 32-bit result w of the Barrett reduction
 ***)

let CONDADD_CLANG17_O3 = prove
 (`!w:int32.
     word_zx
      (word_or
        (word_and (word_add w (word 3329))
          (word_ushr (word_sub (word 0)
                        (word_ushr (word_sxfrom 15
                                     (word_subword w (0,16):int32)) 16))
                     16))
        (word_and w
          (word_not
            (word_ushr (word_sub (word 0)
                          (word_ushr (word_sxfrom 15
                                       (word_subword w (0,16):int32)) 16))
                       16)))):int16 =
     word_add (word_zx w) (word_and (word_ishr (word_zx w) 15) (word 3329))`,
  BITBLAST_TAC);;

let REDUCE_ELEMENT = prove
 (`!x:int16.
     let w:int32 =
       word_add (word_sx x)
        (word_mul (word_ishr (word_add (word 33554432)
                               (word_mul (word_sx x) (word 20159))) 26)
                  (word 4294963967)) in
     ival(word_zx
      (word_or
        (word_and (word_add w (word 3329))
          (word_ushr (word_sub (word 0)
                        (word_ushr (word_sxfrom 15
                                     (word_subword w (0,16):int32)) 16))
                     16))
        (word_and w
          (word_not
            (word_ushr (word_sub (word 0)
                          (word_ushr (word_sxfrom 15
                                       (word_subword w (0,16):int32)) 16))
                       16)))):int16) =
     ival x rem &3329`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CONDADD_CLANG17_O3; BARRED_SCALAR; BARRED_CONDADD_REM]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        nonoverlapping (word pc,libmlkem_size) (a,512)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_poly_reduce) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `x:num->int16`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `256` `pc + mlkem_poly_reduce_loop1`
   `pc + mlkem_poly_reduce_loop1_test`
   `\i s. read X0 s = a /\ read X8 s = word(2 * i) /\
          read X9 s = word 20159 /\ read X10 s = word 33554432 /\
          read X11 s = word 4294963967 /\
          read X30 s = returnaddress /\
          (!j. j < i
               ==> ival(read(memory :> bytes16(word_add a (word(2 * j)))) s) =
                   ival(x j) rem &3329) /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization of the constants and the offset ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; CONJUNCT1 LT; LE_0] THEN
    ASM_REWRITE_TAC[];

    (*** The loop body: process one coefficient ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes16 (word_add a (word (2 * i)))) s0 = x i /\
      (!j. i + 1 <= j /\ j < 256
           ==> read (memory :> bytes16 (word_add a (word (2 * j)))) s0 = x j)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN STRIP_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_EXEC (1--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MLKEM_NATIVE_W_SIMP_TAC THEN
    REWRITE_TAC[CONV_RULE(TOP_DEPTH_CONV let_CONV) REDUCE_ELEMENT];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_EXEC (1--2) THEN
    SUBGOAL_THEN `~(val(word_sub (word (2 * i)) (word 512):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 256 ==> 2 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_reduce ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           nonoverlapping (word pc,libmlkem_size) (a,512)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_reduce) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a pc returnaddress /\
                        memaccess_inbounds e2 [a,512] [a,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a pc returnaddress)
        (APPEND
          (ENUMERATEL 256 (\i. f_ev_loop a pc returnaddress i))
          (f_ev_prol a pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mlkem_poly_reduce_loop1`
   `pc + mlkem_poly_reduce_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X0 s = a /\
           read X8 s = word(2 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_EXEC (1--4) THEN
    CONJ_TAC THENL [REWRITE_TAC[MULT_0; WORD_ADD_0]; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_EXEC (1--15) THEN
  SUBGOAL_THEN
   `~(val(word_add (word (2 * i)) (word 18446744073709551106):int64) = 0) <=>
    i + 1 < 256`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 256 ==> 2 * i < 18446744073709551616`] THEN
    ASM_CASES_TAC `i = 255` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 256 /\ ~(i = 255)
      ==> 2 * i + 18446744073709551106 < 18446744073709551616`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, for the      *)
(* modulus check of the encapsulation key, whose result the encapsulation    *)
(* branches on. The loop is that of the correctness proof, but with the loop *)
(* test at the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires.    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_IMAGE_SUBROUTINE_FULL = prove
 (`exists f_events.
       forall e a x pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           nonoverlapping (word pc,libmlkem_size) (a,512)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_reduce) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    (!i. i < 256
                         ==> read(memory :> bytes16
                                   (word_add a (word(2 * i)))) s = x i) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> ival(read(memory :> bytes16
                                    (word_add a (word(2 * i)))) s) =
                             ival(x i) rem &3329) /\
                    (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a pc returnaddress /\
                        memaccess_inbounds e2 [a,512] [a,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a pc returnaddress)
        (APPEND
          (ENUMERATEL 256 (\i. f_ev_loop a pc returnaddress i))
          (f_ev_prol a pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `x:num->int16`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mlkem_poly_reduce_loop1`
   `pc + mlkem_poly_reduce_loop1_exit`
   `\i s. read X30 s = returnaddress /\
          read X0 s = a /\ read X8 s = word(2 * i) /\
          read X9 s = word 20159 /\ read X10 s = word 33554432 /\
          read X11 s = word 4294963967 /\
          (!j. j < i
               ==> ival(read(memory :> bytes16(word_add a (word(2 * j)))) s) =
                   ival(x j) rem &3329) /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; CONJUNCT1 LT; LE_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN
     `read (memory :> bytes16 (word_add a (word (2 * i)))) s0 = x i /\
      (!j. i + 1 <= j /\ j < 256
           ==> read (memory :> bytes16 (word_add a (word (2 * j)))) s0 = x j)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN STRIP_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_EXEC (1--15) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_add (word (2 * i)) (word 18446744073709551106):int64) =
        0) <=>
      i + 1 < 256`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 256 ==> 2 * i < 18446744073709551616`] THEN
      ASM_CASES_TAC `i = 255` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 256 /\ ~(i = 255)
        ==> 2 * i + 18446744073709551106 < 18446744073709551616`] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN
      REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      MLKEM_NATIVE_W_SIMP_TAC THEN
      REWRITE_TAC[CONV_RULE(TOP_DEPTH_CONV let_CONV) REDUCE_ELEMENT];
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
