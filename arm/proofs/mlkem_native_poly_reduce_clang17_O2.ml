(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of polynomial coefficients producing nonnegative remainders.    *)
(* This is the code for mlkem_poly_reduce from mlkem-native's portable C     *)
(* implementation compiled by clang 17 with -O2 (see mlkem_native/README.md).*)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;

(**** print_literal_from_elf
        "arm/mlkem_native/mlkem_native_poly_reduce_clang17_O2.o";;
 ****)

let mlkem_native_poly_reduce_clang17_O2_mc = define_assert_from_elf
  "mlkem_native_poly_reduce_clang17_O2_mc"
  "arm/mlkem_native/mlkem_native_poly_reduce_clang17_O2.o"
[
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0x5289d7e9;       (* arm_MOV W9 (rvalue (word 20159)) *)
  0x52a0400a;       (* arm_MOVZ W10 (word 512) 16 *)
  0x1281a00b;       (* arm_MOVN W11 (word 3328) 0 *)
  0x78e8680c;       (* arm_LDRSH W12 X0 (Register_Offset X8) *)
  0x1b09298d;       (* arm_MADD W13 W12 W9 W10 *)
  0x131a7dad;       (* arm_ASR W13 W13 26 *)
  0x1b0b31ac;       (* arm_MADD W12 W13 W11 W12 *)
  0x13003d8d;       (* arm_SBFM W13 W12 0 15 *)
  0x1134058e;       (* arm_ADD W14 W12 (rvalue (word 3329)) *)
  0x4b4d43ed;       (* arm_NEG W13 (Shiftedreg W13 LSR 16) *)
  0x53107dad;       (* arm_LSR W13 W13 16 *)
  0x0a2d018c;       (* arm_BIC W12 W12 W13 *)
  0x0a0d01cd;       (* arm_AND W13 W14 W13 *)
  0x2a0c01ac;       (* arm_ORR W12 W13 W12 *)
  0x7828680c;       (* arm_STRH W12 X0 (Register_Offset X8) *)
  0x91000908;       (* arm_ADD X8 X8 (rvalue (word 2)) *)
  0xf108011f;       (* arm_CMP X8 (rvalue (word 512)) *)
  0x54fffe41;       (* arm_BNE (word 2097096) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC =
  ARM_MK_EXEC_RULE mlkem_native_poly_reduce_clang17_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* The value computed for each coefficient.                                  *)
(* ------------------------------------------------------------------------- *)

(*** The conditional addition of 3329, mlk_scalar_signed_to_unsigned_q,
 *** as compiled, applied to the 32-bit result w of the Barrett reduction
 ***)

let CONDADD_CLANG17_O2 = prove
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
  REWRITE_TAC[CONDADD_CLANG17_O2; BARRED_SCALAR; BARRED_CONDADD_REM]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_CORRECT = prove
 (`!a x pc.
        nonoverlapping (word pc,0x50) (a,512)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_poly_reduce_clang17_O2_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = word(pc + 0x4c) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `256` `pc + 0x10` `pc + 0x44`
   `\i s. read X0 s = a /\ read X8 s = word(2 * i) /\
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

    (*** Initialization of the constants and the offset ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC (1--4) THEN
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
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC (1--13) THEN
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
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC (1--2) THEN
    SUBGOAL_THEN `~(val(word_sub (word (2 * i)) (word 512):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 256 ==> 2 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_SUBROUTINE_CORRECT = prove
 (`!a x pc returnaddress.
        nonoverlapping (word pc,0x50) (a,512)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_poly_reduce_clang17_O2_mc /\
                  read PC s = word pc /\
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
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_reduce ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC;;

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a pc returnaddress.
           nonoverlapping (word pc,80) (a,512)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_poly_reduce_clang17_O2_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a pc returnaddress /\
                        memaccess_inbounds e2 [a,512] [a,512])
               (\s s'. true)`,
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
              fst MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + 0x10` `pc + 0x4c`
    `\i s. read X30 s = returnaddress /\
           read X0 s = a /\
           read X8 s = word(2 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC (1--4) THEN
    CONJ_TAC THENL [REWRITE_TAC[MULT_0; WORD_ADD_0]; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC (1--15) THEN
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
